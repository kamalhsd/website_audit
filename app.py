import streamlit as st
import requests
from bs4 import BeautifulSoup
import pandas as pd
from urllib.parse import urljoin, urlparse
import time
from collections import deque, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from datetime import datetime
import xml.etree.ElementTree as ET
from urllib.robotparser import RobotFileParser
import streamlit.components.v1 as components
import html
import re
import os
import threading
import sqlite3
import uuid

# --- AI & ML IMPORTS ---
try:
    from sklearn.feature_extraction.text import TfidfVectorizer
    from sklearn.metrics.pairwise import cosine_similarity
    import numpy as np
    HAS_SKLEARN = True
except ImportError:
    HAS_SKLEARN = False

# Page config
st.set_page_config(page_title="Battersea Crawler", layout="wide", page_icon="🐸")

# --- GLOBAL CONFIG ---
write_lock = threading.Lock()

# Initialize session state
if 'db_file' not in st.session_state:
    st.session_state.db_file = f"battersea_data_{uuid.uuid4().hex}.db"

if 'crawl_data' not in st.session_state:
    st.session_state.crawl_data = []
if 'crawling' not in st.session_state:
    st.session_state.crawling = False
if 'stop_crawling' not in st.session_state:
    st.session_state.stop_crawling = False
if 'sitemap_urls_set' not in st.session_state:
    st.session_state.sitemap_urls_set = set()
if 'psi_results' not in st.session_state:
    st.session_state.psi_results = {}
if 'total_crawled_count' not in st.session_state:
    st.session_state.total_crawled_count = 0
if 'storage_mode' not in st.session_state:
    st.session_state.storage_mode = "RAM"
if 'img_size_cache' not in st.session_state:
    st.session_state.img_size_cache = {}
if 'link_status_cache' not in st.session_state:
    st.session_state.link_status_cache = {}


# --- SQLITE HELPER FUNCTIONS ---
def init_db(db_path):
    """Initializes the SQLite database with the pages table."""
    conn = sqlite3.connect(db_path, check_same_thread=False)
    c = conn.cursor()
    # Create table if not exists
    # Added 'depth' column
    c.execute('''
        CREATE TABLE IF NOT EXISTS pages (
            url TEXT PRIMARY KEY,
            original_url TEXT,
            status_code INTEGER,
            title TEXT,
            title_length INTEGER,
            meta_description TEXT,
            meta_desc_length INTEGER,
            canonical_url TEXT,
            meta_robots TEXT,
            is_noindex_follow BOOLEAN,
            is_noindex_nofollow BOOLEAN,
            h1_tags TEXT,
            h1_count INTEGER,
            h2_tags TEXT,
            h2_count INTEGER,
            h3_tags TEXT,
            h3_count INTEGER,
            h4_tags TEXT,
            h4_count INTEGER,
            word_count INTEGER,
            response_time REAL,
            content_length INTEGER,
            internal_links_count INTEGER,
            external_links_count INTEGER,
            internal_links TEXT,
            external_links TEXT,
            images TEXT,
            image_count INTEGER,
            images_without_alt INTEGER,
            schema_types TEXT,
            schema_dump TEXT,
            schema_count INTEGER,
            schema_validity TEXT,
            schema_errors TEXT,
            redirect_chain TEXT,
            redirect_count INTEGER,
            css_files INTEGER,
            js_files INTEGER,
            og_title TEXT,
            og_description TEXT,
            twitter_title TEXT,
            custom_extraction TEXT,
            indexability TEXT,
            crawl_timestamp TEXT,
            header_structure TEXT,
            scope_content TEXT,
            depth INTEGER,  -- <--- NEW: Depth Level
            error TEXT
        )
    ''')
    conn.commit()
    conn.close()

def save_row_to_db(data, db_path):
    """Writes a single row of data to the SQLite DB safely."""
    row_data = data.copy()
    
    # Serialize lists/dicts to JSON for SQLite storage (TEXT columns)
    for key in ['internal_links', 'external_links', 'images', 'redirect_chain', 'schema_dump', 'header_structure']:
        if key in row_data:
            row_data[key] = json.dumps(row_data[key])
    
    # Convert Booleans to Integers
    if 'is_noindex_follow' in row_data:
        row_data['is_noindex_follow'] = 1 if row_data['is_noindex_follow'] else 0
    if 'is_noindex_nofollow' in row_data:
        row_data['is_noindex_nofollow'] = 1 if row_data['is_noindex_nofollow'] else 0

    columns = [
        'url', 'original_url', 'status_code', 'title', 'title_length', 
        'meta_description', 'meta_desc_length', 'canonical_url', 'meta_robots', 
        'is_noindex_follow', 'is_noindex_nofollow', 'h1_tags', 'h1_count', 
        'h2_tags', 'h2_count', 'h3_tags', 'h3_count', 'h4_tags', 'h4_count', 
        'word_count', 'response_time', 'content_length', 'internal_links_count', 
        'external_links_count', 'internal_links', 'external_links', 'images', 
        'image_count', 'images_without_alt', 'schema_types', 'schema_dump', 
        'schema_count', 'schema_validity', 'schema_errors', 'redirect_chain', 
        'redirect_count', 'css_files', 'js_files', 'og_title', 'og_description', 
        'twitter_title', 'custom_extraction', 'indexability', 'crawl_timestamp', 
        'header_structure', 
        'scope_content', 
        'depth', # <--- Added Depth
        'error'
    ]
    
    filtered_data = {k: row_data.get(k) for k in columns}
    
    placeholders = ', '.join(['?'] * len(columns))
    col_names = ', '.join(columns)
    sql = f"INSERT OR REPLACE INTO pages ({col_names}) VALUES ({placeholders})"
    
    with write_lock:
        conn = sqlite3.connect(db_path, check_same_thread=False)
        try:
            conn.execute(sql, list(filtered_data.values()))
            conn.commit()
        except Exception as e:
            print(f"DB Error: {e}")
        finally:
            conn.close()

# --- NEW AI HELPER FUNCTIONS ---
def generate_interlink_suggestions(df, min_score=40, max_suggestions=10):
    if df.empty: return pd.DataFrame()
    
    # Use scope_content if available, else fallback to Title/Meta
    df['target_topic'] = df['title'].fillna('') + " " + df['h1_tags'].fillna('')
    df['source_context'] = df['scope_content'].fillna('')
    mask = df['source_context'] == ''
    df.loc[mask, 'source_context'] = df.loc[mask, 'title'].fillna('') + " " + df.loc[mask, 'meta_description'].fillna('')

    valid_targets = df[df['target_topic'].str.strip() != '']
    valid_sources = df[df['source_context'].str.strip() != '']
    
    if valid_targets.empty or valid_sources.empty: return pd.DataFrame()

    tfidf = TfidfVectorizer(stop_words='english')
    try:
        all_text = pd.concat([valid_targets['target_topic'], valid_sources['source_context']])
        tfidf.fit(all_text)
        target_matrix = tfidf.transform(df['target_topic'])
        source_matrix = tfidf.transform(df['source_context'])
    except ValueError: return pd.DataFrame()
    
    suggestions = []
    existing_links = set()
    for _, row in df.iterrows():
        links = row.get('internal_links', [])
        if isinstance(links, str):
            try: links = json.loads(links)
            except: links = []
        for link in links:
            existing_links.add((row['url'], link['url']))

    similarity_scores = cosine_similarity(source_matrix, target_matrix)

    for idx, row in df.iterrows():
        source_url = row['url']
        scores = similarity_scores[idx]
        top_indices = scores.argsort()[::-1][:50] 
        count = 0
        for target_idx in top_indices:
            if count >= max_suggestions: break
            target_url = df.iloc[target_idx]['url']
            score = round(scores[target_idx] * 100, 1)
            
            if source_url == target_url: continue 
            if score < min_score: continue 
            if (source_url, target_url) in existing_links: continue 
            
            suggestions.append({
                'Source URL': source_url,
                'Source Content Preview': row['source_context'][:50] + "...",
                'Suggested Target URL': target_url,
                'Target Topic': df.iloc[target_idx]['target_topic'][:60] + "...",
                'Relevance Score': score
            })
            count += 1
    return pd.DataFrame(suggestions)

def analyze_content_cannibalization(df, merge_threshold=0.50, duplicate_threshold=0.85):
    if df.empty: return pd.DataFrame()
    
    df['analysis_text'] = df['title'].fillna('') + " " + df['scope_content'].fillna(df['meta_description'].fillna(''))
    valid_df = df[df['analysis_text'].str.strip().str.len() > 10].copy().reset_index(drop=True)
    
    if len(valid_df) < 2: return pd.DataFrame()

    tfidf = TfidfVectorizer(stop_words='english', min_df=2)
    try:
        tfidf_matrix = tfidf.fit_transform(valid_df['analysis_text'])
    except: return pd.DataFrame()

    cosine_sim = cosine_similarity(tfidf_matrix, tfidf_matrix)
    results = []
    num_rows = len(valid_df)
    
    for i in range(num_rows):
        for j in range(i + 1, num_rows):
            score = cosine_sim[i, j]
            if score >= merge_threshold:
                action = "🤝 Merge Content"
                if score >= duplicate_threshold:
                    action = "🚨 Remove/Redirect (Duplicate)"
                
                results.append({
                    'Page A': valid_df.iloc[i]['url'],
                    'Page A Title': valid_df.iloc[i]['title'],
                    'Page B': valid_df.iloc[j]['url'],
                    'Page B Title': valid_df.iloc[j]['title'],
                    'Similarity': score,
                    'Recommendation': action
                })
    return pd.DataFrame(results).sort_values(by='Similarity', ascending=False)

# --- CRAWLER CLASS ---
class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None, link_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Accept-Encoding': 'gzip, deflate',
            'Connection': 'keep-alive',
            'Upgrade-Insecure-Requests': '1'
        })
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=20,
            pool_maxsize=20,
            max_retries=1
        )
        self.session.mount('http://', adapter)
        self.session.mount('https://', adapter)
        
        self.robots_cache = {}
        self.base_domain = None
        self.base_path = None
    
    def set_base_url(self, url):
        parsed = urlparse(url)
        self.base_domain = parsed.netloc
        self.base_path = parsed.path.rstrip('/')
    
    def should_crawl_url(self, url):
        parsed = urlparse(url)
        base_clean = self.base_domain.replace('www.', '')
        target_clean = parsed.netloc.replace('www.', '')

        if self.crawl_scope == "exact":
            return url == urljoin(f"https://{self.base_domain}", self.base_path)
        elif self.crawl_scope == "subdomain":
            return base_clean in target_clean
        else:  # subfolder
            return (base_clean == target_clean and parsed.path.startswith(self.base_path))
    
    def can_fetch(self, url):
        if self.ignore_robots:
            return True
        try:
            domain = urlparse(url).netloc
            if domain not in self.robots_cache:
                try:
                    rp = RobotFileParser()
                    rp.set_url(f"https://{domain}/robots.txt")
                    rp.read()
                    self.robots_cache[domain] = rp
                except:
                    self.robots_cache[domain] = None
            if self.robots_cache[domain] is None:
                return True
            return self.robots_cache[domain].can_fetch('*', url)
        except:
            return True

    def smart_clean(self, text):
        if not text:
            return ""
        text = str(text)
        text = html.unescape(text)
        text = re.sub(r'[\r\n\t]+', ' ', text)
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def get_css_path(self, element):
        path = []
        for parent in element.parents:
            if parent.name == '[document]':
                break
            selector = parent.name
            if parent.get('id'):
                selector += f"#{parent['id']}"
            elif parent.get('class'):
                selector += f".{parent['class'][0]}"
            path.append(selector)
        path.reverse()
        element_selector = element.name
        if element.get('class'):
            element_selector += f".{element['class'][0]}"
        path.append(element_selector)
        return " > ".join(path)

    def extract_sitemap_urls(self, sitemap_url):
        urls = []
        try:
            response = self.session.get(sitemap_url, timeout=8)
            if response.status_code == 200:
                root = ET.fromstring(response.content)
                namespaces = {'sitemap': 'http://www.sitemaps.org/schemas/sitemap/0.9'}
                
                sitemapindex = root.findall('.//sitemap:sitemap', namespaces)
                if sitemapindex:
                    for sitemap in sitemapindex:
                        loc = sitemap.find('sitemap:loc', namespaces)
                        if loc is not None:
                            urls.extend(self.extract_sitemap_urls(loc.text))
                else:
                    url_elements = root.findall('.//sitemap:url', namespaces)
                    for url_elem in url_elements:
                        loc = url_elem.find('sitemap:loc', namespaces)
                        if loc is not None:
                            urls.append(loc.text)
        except Exception as e:
            st.error(f"Error parsing sitemap: {e}")
        return urls
        
    def get_file_size(self, url):
        try:
            r = self.session.head(url, timeout=2)
            if 'content-length' in r.headers:
                return round(int(r.headers['content-length']) / 1024, 2)
        except:
            pass
        return 0

    def extract_recursive_types(self, data, types_list):
        if isinstance(data, dict):
            if '@type' in data:
                if isinstance(data['@type'], list):
                    types_list.extend(data['@type'])
                else:
                    types_list.append(data['@type'])
            for key, value in data.items():
                self.extract_recursive_types(value, types_list)
        elif isinstance(data, list):
            for item in data:
                self.extract_recursive_types(item, types_list)

    def extract_page_data(self, url):
        try:
            response = self.session.get(url, timeout=10, allow_redirects=True)
            
            actual_status_code = response.status_code
            if response.history:
                actual_status_code = response.history[0].status_code

            soup = BeautifulSoup(response.content, 'html.parser')
            
            # --- MODIFIED: Extract Scope Content for AI Analysis ---
            scope_content = ""
            if self.link_selector:
                scoped_element = soup.select_one(self.link_selector)
                if scoped_element:
                    scope_content = self.smart_clean(scoped_element.get_text())
            else:
                if soup.body:
                    scope_content = self.smart_clean(soup.body.get_text())[:50000]
            # -----------------------------------------------------

            header_structure = []
            all_headers = soup.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6'])
            for tag in all_headers:
                header_structure.append({
                    'tag': tag.name,
                    'level': int(tag.name[1]), 
                    'text': self.smart_clean(tag.get_text())[:100]
                })
            
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            
            is_noindex_follow = False
            is_noindex_nofollow = False
            if robots_content:
                directives = [d.strip().lower() for d in robots_content.split(',')]
                if 'noindex' in directives and 'follow' in directives:
                    is_noindex_follow = True
                elif 'noindex' in directives and 'nofollow' in directives:
                    is_noindex_nofollow = True

            h1_tags = [self.smart_clean(h1.get_text()) for h1 in soup.find_all('h1')]
            h2_tags = [self.smart_clean(h2.get_text()) for h2 in soup.find_all('h2')]
            h3_tags = [self.smart_clean(h3.get_text()) for h3 in soup.find_all('h3')]
            h4_tags = [self.smart_clean(h4.get_text()) for h4 in soup.find_all('h4')]
            
            custom_data = ""
            if self.custom_selector:
                custom_elements = soup.select(self.custom_selector)
                custom_data = "; ".join([self.smart_clean(el.get_text()) for el in custom_elements])

            internal_links = []
            external_links = []
            base_domain_clean = urlparse(response.url).netloc.replace('www.', '')
            
            search_area = soup
            if self.link_selector:
                specific_section = soup.select_one(self.link_selector)
                if specific_section:
                    search_area = specific_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(response.url, link['href']) 
                
                # --- MODIFIED: Fix for Fragment URLs ---
                href = href.split('#')[0]
                if not href: continue
                # ---------------------------------------

                link_text = self.smart_clean(link.get_text())[:100]
                css_path = self.get_css_path(link)
                
                rel_attr = link.get('rel', [])
                target_attr = link.get('target', '')
                rel_str = ' '.join(rel_attr) if isinstance(rel_attr, list) else str(rel_attr)
                
                link_rel_status = "dofollow"
                if 'nofollow' in rel_str.lower(): link_rel_status = "nofollow"
                if 'sponsored' in rel_str.lower(): link_rel_status += ", sponsored"
                if 'ugc' in rel_str.lower(): link_rel_status += ", ugc"
                
                link_target = "_blank" if target_attr == "_blank" else "_self"
                
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower: placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower or "menu" in path_lower: placement = "Header"
                elif "sidebar" in path_lower or "aside" in path_lower: placement = "Sidebar"

                link_data = {
                    'url': href, 'anchor_text': link_text, 'css_path': css_path,
                    'placement': placement, 'rel_status': link_rel_status, 'target': link_target
                }
                
                link_netloc = urlparse(href).netloc.replace('www.', '')
                if link_netloc == base_domain_clean:
                    internal_links.append(link_data)
                else:
                    external_links.append(link_data)
            
            images = []
            for img in soup.find_all('img'):
                img_src = urljoin(response.url, img.get('src', ''))
                images.append({
                    'src': img_src,
                    'alt': self.smart_clean(img.get('alt', '')),
                    'title': self.smart_clean(img.get('title', '')),
                    'width': img.get('width', ''),
                    'height': img.get('height', ''),
                    'size_kb': 0
                })
            
            scripts = soup.find_all('script', type='application/ld+json')
            schema_types = []
            schema_dump = [] 
            schema_validity = "No Schema"
            schema_errors = []
            
            if scripts:
                schema_validity = "Valid"
                for script in scripts:
                    try:
                        if script.string:
                            data = json.loads(script.string)
                            schema_dump.append(data)
                            self.extract_recursive_types(data, schema_types)
                    except json.JSONDecodeError as e:
                        schema_validity = "Invalid JSON"
                        schema_errors.append(str(e))
                    except Exception as e:
                        schema_validity = "Error"
                        schema_errors.append(str(e))

            css_files = len(soup.find_all('link', attrs={'rel': 'stylesheet'}))
            js_files = len(soup.find_all('script', src=True))
            text_content = soup.get_text()
            word_count = len(text_content.split())
            
            redirect_chain = []
            if hasattr(response, 'history') and response.history:
                for i, resp in enumerate(response.history):
                    redirect_chain.append({
                        'step': i + 1, 'from_url': resp.url,
                        'status_code': resp.status_code,
                        'redirect_type': '301 Permanent' if resp.status_code == 301 else f'{resp.status_code}'
                    })
            
            return {
                'url': url, 
                'original_url': url, 
                'status_code': actual_status_code,
                'title': title_text, 'title_length': len(title_text),
                'meta_description': meta_desc_text, 'meta_desc_length': len(meta_desc_text),
                'canonical_url': canonical_url, 'meta_robots': robots_content,
                'is_noindex_follow': is_noindex_follow, 'is_noindex_nofollow': is_noindex_nofollow,
                'h1_tags': '; '.join(h1_tags), 'h1_count': len(h1_tags),
                'h2_tags': '; '.join(h2_tags), 'h2_count': len(h2_tags),
                'h3_tags': '; '.join(h3_tags), 'h3_count': len(h3_tags),
                'h4_tags': '; '.join(h4_tags), 'h4_count': len(h4_tags),
                'word_count': word_count, 'response_time': response.elapsed.total_seconds(),
                'content_length': len(response.content),
                'internal_links_count': len(internal_links), 'external_links_count': len(external_links),
                'internal_links': internal_links, 'external_links': external_links,
                'images': images, 'image_count': len(images),
                'images_without_alt': len([img for img in images if not img['alt']]),
                'schema_types': '; '.join(list(set(schema_types))), 'schema_dump': schema_dump,
                'schema_count': len(schema_types), 'schema_validity': schema_validity,
                'schema_errors': '; '.join(schema_errors), 'redirect_chain': redirect_chain,
                'redirect_count': len(redirect_chain), 'css_files': css_files, 'js_files': js_files,
                'og_title': soup.find('meta', attrs={'property': 'og:title'}).get('content', '') if soup.find('meta', attrs={'property': 'og:title'}) else '',
                'og_description': soup.find('meta', attrs={'property': 'og:description'}).get('content', '') if soup.find('meta', attrs={'property': 'og:description'}) else '',
                'twitter_title': soup.find('meta', attrs={'name': 'twitter:title'}).get('content', '') if soup.find('meta', attrs={'name': 'twitter:title'}) else '',
                'custom_extraction': custom_data,
                'indexability': self.get_indexability_status(actual_status_code, robots_content),
                'crawl_timestamp': datetime.now().isoformat(), 
                'header_structure': header_structure, 
                'scope_content': scope_content, 
                'error': ''
            }
        except Exception as e:
            return {
                'url': url, 'original_url': url, 'status_code': 0, 'error': str(e),
                'title': '', 'title_length': 0, 'meta_description': '', 'meta_desc_length': 0,
                'canonical_url': '', 'meta_robots': '', 'is_noindex_follow': False, 'is_noindex_nofollow': False,
                'h1_tags': '', 'h1_count': 0, 'h2_tags': '', 'h2_count': 0, 'h3_tags': '', 'h3_count': 0,
                'h4_tags': '', 'h4_count': 0, 'word_count': 0, 'response_time': 0,
                'content_length': 0, 'internal_links_count': 0, 'external_links_count': 0,
                'internal_links': [], 'external_links': [], 'images': [], 'image_count': 0,
                'images_without_alt': 0, 'schema_types': '', 'schema_dump': [], 'schema_count': 0, 
                'schema_validity': 'Error', 'schema_errors': '',
                'redirect_chain': [], 'redirect_count': 0, 'css_files': 0, 'js_files': 0,
                'og_title': '', 'og_description': '', 'twitter_title': '',
                'custom_extraction': '', 'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat(),
                'header_structure': [], 'scope_content': ''
            }
    
    def get_indexability_status(self, status_code, robots_content):
        if status_code != 200:
            return 'Non-Indexable'
        if 'noindex' in robots_content.lower():
            return 'Non-Indexable'
        return 'Indexable'

# --- PSI HELPER FUNCTION ---
def run_psi_test(url, api_key, strategy="mobile"):
    if not api_key: return {"error": "No API Key Provided"}
    api_url = f"https://www.googleapis.com/pagespeedonline/v5/runPagespeed?url={url}&strategy={strategy}&key={api_key}"
    try:
        response = requests.get(api_url)
        data = response.json()
        if "error" in data: 
            return {"error": data["error"]["message"]}
        lh_result = data["lighthouseResult"]
        return {
            "Score": int(lh_result["categories"]["performance"]["score"] * 100),
            "LCP": lh_result["audits"]["largest-contentful-paint"]["displayValue"],
            "FCP": lh_result["audits"]["first-contentful-paint"]["displayValue"],
            "CLS": lh_result["audits"]["cumulative-layout-shift"]["displayValue"],
            "INP": lh_result["audits"].get("interaction-to-next-paint", {}).get("displayValue", "N/A"),
            "TTI": lh_result["audits"]["interactive"]["displayValue"]
        }
    except Exception as e: 
        return {"error": str(e)}

# --- HELPER FOR HEADER ANALYSIS ---
def analyze_heading_structure(structure):
    """Analyzes header list for SEO issues."""
    issues = []
    h1_count = 0
    prev_level = 0
    
    if not structure:
        return ["⚠️ No Heading Tags Found"], 0

    for h in structure:
        curr_level = h['level']
        if curr_level == 1:
            h1_count += 1
        if curr_level - prev_level > 1 and prev_level != 0:
            issues.append(f"⚠️ Skipped Level: {h['tag'].upper()} follows H{prev_level} (Should be H{prev_level+1})")
        prev_level = curr_level

    if h1_count == 0:
        issues.insert(0, "❌ Missing H1 Tag")
    elif h1_count > 1:
        issues.insert(0, f"❌ Multiple H1 Tags Found ({h1_count})")
        
    return issues, h1_count

# --- CRAWLER HANDLERS ---
def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, storage="RAM"):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector)
    crawler.set_base_url(start_url)
    
    if storage == "SQLite":
        init_db(st.session_state.db_file) 
    else:
        st.session_state.crawl_data = [] 
    
    # MODIFIED: Queue stores (url, depth) tuples
    urls_to_visit = deque([(start_url, 0)]) 
    visited_urls = set()
    st.session_state.total_crawled_count = 0
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    
    # Reduced max_workers to 5 for stability
    with ThreadPoolExecutor(max_workers=5) as executor:
        while urls_to_visit and len(visited_urls) < max_urls:
            if st.session_state.stop_crawling: break
                
            current_batch = []
            batch_size = min(20, len(urls_to_visit), max_urls - len(visited_urls))
            
            for _ in range(batch_size):
                if urls_to_visit and not st.session_state.stop_crawling:
                    # Pop tuple (url, depth)
                    url, depth = urls_to_visit.popleft()
                    
                    if url not in visited_urls and crawler.can_fetch(url):
                        current_batch.append((url, depth))
                        visited_urls.add(url)
            
            if not current_batch: break
            
            # Map future to (url, depth)
            future_to_url = {executor.submit(crawler.extract_page_data, u): (u, d) for u, d in current_batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: f.cancel()
                    break
                try:
                    page_data = future.result(timeout=12)
                    # Retrieve depth from the mapping
                    _, current_depth = future_to_url[future]
                    page_data['depth'] = current_depth # Add depth to result
                    
                    if storage == "SQLite":
                        save_row_to_db(page_data, st.session_state.db_file) 
                    else:
                        st.session_state.crawl_data.append(page_data)

                    st.session_state.total_crawled_count += 1
                    
                    if not st.session_state.stop_crawling:
                        for link_data in page_data.get('internal_links', []):
                            link_url = link_data['url']
                            if (link_url not in visited_urls and 
                                # Use a generator check to see if link is already in queue tuples
                                not any(link_url == u[0] for u in urls_to_visit) and 
                                crawler.should_crawl_url(link_url) and 
                                len(visited_urls) + len(urls_to_visit) < max_urls):
                                # Add new link with incremented depth
                                urls_to_visit.append((link_url, current_depth + 1))
                    
                    progress = min(st.session_state.total_crawled_count / max_urls, 1.0)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {st.session_state.total_crawled_count} | Queue: {len(urls_to_visit)} | Speed: {st.session_state.total_crawled_count/max(1, time.time() - st.session_state.get('start_time', time.time())):.1f} URLs/sec")
                except Exception as e: st.error(f"Error: {e}")
    return True

def crawl_from_list(url_list, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, storage="RAM"):
    crawler = UltraFrogCrawler(len(url_list), ignore_robots, custom_selector=custom_selector, link_selector=link_selector)
    
    if storage == "SQLite":
        init_db(st.session_state.db_file) 
    else:
        st.session_state.crawl_data = []

    st.session_state.total_crawled_count = 0
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    valid_urls = [url.strip() for url in url_list if crawler.can_fetch(url.strip())]
    
    if not valid_urls: return False
    
    # Reduced max_workers to 5
    with ThreadPoolExecutor(max_workers=5) as executor:
        for i in range(0, len(valid_urls), 25):
            if st.session_state.stop_crawling: break
            batch = valid_urls[i:i + 25]
            future_to_url = {executor.submit(crawler.extract_page_data, url): url for url in batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: f.cancel()
                    break
                try:
                    page_data = future.result(timeout=12)
                    page_data['depth'] = 0 # List mode has 0 depth for all
                    
                    if storage == "SQLite":
                        save_row_to_db(page_data, st.session_state.db_file) 
                    else:
                        st.session_state.crawl_data.append(page_data)

                    st.session_state.total_crawled_count += 1
                    progress = st.session_state.total_crawled_count / len(valid_urls)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Processed: {st.session_state.total_crawled_count}/{len(valid_urls)}")
                except Exception as e: st.error(f"Error: {e}")
    return True

def crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, storage="RAM"):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, custom_selector=custom_selector, link_selector=link_selector)
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    status_text.text("🗺️ Extracting URLs from sitemap...")
    sitemap_urls = crawler.extract_sitemap_urls(sitemap_url)
    
    if not sitemap_urls:
        st.error("No URLs found in sitemap")
        return False
    if len(sitemap_urls) > max_urls:
        sitemap_urls = sitemap_urls[:max_urls]
    
    st.info(f"Found {len(sitemap_urls)} URLs in sitemap")
    return crawl_from_list(sitemap_urls, progress_container, ignore_robots, custom_selector, link_selector, storage)

# CSS
st.markdown("""
<style>
.stTabs [data-baseweb="tab-list"]{ gap: 10px; padding: 6px 6px; border-radius: 10px; background: #eef2f6; }
.stTabs [data-baseweb="tab"]{ height: 50px; white-space: pre-wrap; border-radius: 8px; background: #ffffff !important; color: #111827 !important; border: 1px solid #d1d5db !important; }
.stTabs [data-baseweb="tab"] *{ color: inherit !important; }
.stTabs [aria-selected="true"]{ background: #4CAF50 !important; color: #ffffff !important; border: 1px solid #3f9f46 !important; font-weight: 700; }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown("""
<div class="main-header">
    <h1 style="color: white; margin: 0;">Battersea Crawler</h1>
    <p style="color: white; margin: 0; opacity: 0.9;">Professional Edition • Full SEO Analysis</p>
</div>
""", unsafe_allow_html=True)

# Sidebar
with st.sidebar:
    st.header("🔧 Crawl Configuration")
    
    storage_option = st.radio(
        "💾 Storage Mode", 
        ["RAM (Fast, <10k URLs)", "SQLite (Unlimited)"], 
        index=0,
        help="Use RAM for speed on small sites. Use SQLite for 100k+ URLs to prevent crashing."
    )

    crawl_mode = st.selectbox("🎯 Crawl Mode", [
        "🕷️ Spider Crawl (Follow Links)",
        "📝 List Mode (Upload URLs)",
        "🗺️ Sitemap Crawl (XML Sitemap)"
    ])
    
    sitemap_url_orphan = ""
    
    if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
        start_url = st.text_input("🌐 Website URL", placeholder="https://example.com")
        sitemap_url_orphan = st.text_input("🗺️ Orphan Check Sitemap (Optional)", placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs", min_value=1, max_value=100000, value=1000)
        crawl_scope = st.selectbox("🎯 Crawl Scope", ["subfolder", "subdomain", "exact"])
        
    elif crawl_mode == "📝 List Mode (Upload URLs)":
        uploaded_file = st.file_uploader("Choose file", type=['txt', 'csv'])
        url_list_text = st.text_area("Or paste URLs here (one per line)", height=100)
        
    elif crawl_mode == "🗺️ Sitemap Crawl (XML Sitemap)":
        sitemap_url = st.text_input("🗺️ Sitemap URL", placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs", min_value=1, max_value=100000, value=5000)
    
    ignore_robots = st.checkbox("🤖 Ignore robots.txt")
    
    st.markdown("---")
    st.subheader("⛏️ Custom Extraction")
    custom_selector = st.text_input("Data Selector (Optional)", placeholder=".price, h1, #sku", help="Extract text from specific elements")
    
    st.subheader("🎯 Link Scope (Optional)")
    link_selector = st.text_input("Link Area Selector", placeholder=".sidebar, #footer, .content", help="Only extract links found inside this element")
    
    st.markdown("---")
    st.subheader("⚡ PageSpeed Insights")
    psi_api_key = st.text_input("Google API Key (Optional)", type="password", help="Required for Speed Tab")

    col1, col2 = st.columns(2)
    with col1:
        start_btn = st.button("🚀 Start Crawl", type="primary", disabled=st.session_state.crawling)
    with col2:
        stop_btn = st.button("⛔ Stop Crawl", disabled=not st.session_state.crawling)
    
    if stop_btn:
        st.session_state.stop_crawling = True
        st.session_state.crawling = False
        st.rerun()
    
    if start_btn:
        valid_input = False
        url_list = []
        
        # Determine Storage Mode
        if "SQLite" in storage_option:
            st.session_state.storage_mode = "SQLite"
            st.session_state.crawl_data = [] 
            # Re-generate session file on new crawl start to ensure freshness
            if os.path.exists(st.session_state.db_file):
                try: os.remove(st.session_state.db_file)
                except: pass
            st.session_state.db_file = f"battersea_data_{uuid.uuid4().hex}.db"
        else:
            st.session_state.storage_mode = "RAM"
            # We don't delete DB file here, we just ignore it

        if crawl_mode == "🕷️ Spider Crawl (Follow Links)" and start_url:
            valid_input = True
            if sitemap_url_orphan:
                crawler_temp = UltraFrogCrawler()
                st.session_state.sitemap_urls_set = set(crawler_temp.extract_sitemap_urls(sitemap_url_orphan))
            else:
                st.session_state.sitemap_urls_set = set()
        elif crawl_mode == "📝 List Mode (Upload URLs)":
            if uploaded_file:
                content = uploaded_file.read().decode('utf-8')
                url_list = [line.strip() for line in content.split('\n') if line.strip()]
                valid_input = len(url_list) > 0
            elif url_list_text:
                url_list = [line.strip() for line in url_list_text.split('\n') if line.strip()]
                valid_input = len(url_list) > 0
        elif crawl_mode == "🗺️ Sitemap Crawl (XML Sitemap)" and sitemap_url:
            valid_input = True
        
        if valid_input:
            st.session_state.crawling = True
            st.session_state.stop_crawling = False
            st.session_state.start_time = time.time()
            st.rerun()
        else:
            st.error("Please provide valid input")
    
    if st.button("🗑️ Clear All Data"):
        st.session_state.crawl_data = []
        if os.path.exists(st.session_state.db_file):
            try: os.remove(st.session_state.db_file)
            except: pass
        # Create a fresh file name
        st.session_state.db_file = f"battersea_data_{uuid.uuid4().hex}.db"
        st.session_state.sitemap_urls_set = set()
        st.session_state.psi_results = {}
        st.rerun()

# Main content
if st.session_state.crawling:
    st.header("🐸 Battersea Crawler is Running...")
    progress_container = st.container()
    
    try:
        custom_sel = custom_selector if custom_selector else None
        link_sel = link_selector if link_selector else None
        mode_val = st.session_state.storage_mode
        
        if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
            crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots, custom_sel, link_sel, mode_val)
        elif crawl_mode == "📝 List Mode (Upload URLs)":
            if uploaded_file:
                content = uploaded_file.read().decode('utf-8')
                url_list = [line.strip() for line in content.split('\n') if line.strip()]
            else:
                url_list = [line.strip() for line in url_list_text.split('\n') if line.strip()]
            crawl_from_list(url_list, progress_container, ignore_robots, custom_sel, link_sel, mode_val)
        else:
            crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots, custom_sel, link_sel, mode_val)
        
        st.session_state.crawling = False
        st.session_state.stop_crawling = False
        
        if st.session_state.stop_crawling:
            st.warning("⛔ Crawl stopped by user")
        else:
            crawl_time = time.time() - st.session_state.get('start_time', time.time())
            st.success(f"✅ Crawl completed! Found {st.session_state.total_crawled_count} URLs in {crawl_time:.1f} seconds")
        st.rerun()
        
    except Exception as e:
        st.error(f"Error: {str(e)}")
        st.session_state.crawling = False

# --- RESULT LOADING LOGIC ---
df = None
has_data = False

if st.session_state.storage_mode == "RAM" and st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    has_data = True
elif st.session_state.storage_mode == "SQLite" and os.path.exists(st.session_state.db_file):
    conn = sqlite3.connect(st.session_state.db_file, check_same_thread=False)
    try:
        df = pd.read_sql("SELECT * FROM pages LIMIT 20000", conn)
        for col in ['internal_links', 'external_links', 'images', 'redirect_chain', 'schema_dump', 'header_structure']: 
            if col in df.columns:
                df[col] = df[col].apply(lambda x: json.loads(x) if isinstance(x, str) else [])
        has_data = True
        cursor = conn.cursor()
        cursor.execute("SELECT COUNT(*) FROM pages")
        total_in_db = cursor.fetchone()[0]
        if total_in_db > 20000:
            st.warning(f"⚠️ Displaying first 20,000 URLs for performance. Download the DB below for the full dataset ({total_in_db} URLs).")
        conn.close()
    except Exception as e:
        st.error(f"Error reading DB: {e}")

# --- NEW: CALCULATE INLINKS ON LOAD ---
if has_data and df is not None:
    # 1. Calculate Inlinks Count
    inlinks_counter = Counter()
    for _, row in df.iterrows():
        links = row.get('internal_links', [])
        if isinstance(links, str): 
            try: links = json.loads(links)
            except: links = []
        for link in links:
            inlinks_counter[link['url']] += 1
            
    # Map to DataFrame
    df['inlinks_count'] = df['url'].map(inlinks_counter).fillna(0).astype(int)
    
    # 2. Ensure Depth is present (fill NaN with 0 for list mode)
    if 'depth' not in df.columns:
        df['depth'] = 0
    else:
        df['depth'] = df['depth'].fillna(0).astype(int)

if has_data and df is not None:
    # Summary stats
    st.header("📊 Battersea Analysis Dashboard")
    col1, col2, col3, col4, col5, col6 = st.columns(6)
    with col1: st.metric("Total URLs", len(df) if st.session_state.storage_mode == "RAM" else total_in_db)
    with col2: st.metric("✅ Indexable", len(df[df['indexability'] == 'Indexable']))
    with col3: st.metric("❌ Non-Indexable", len(df[df['indexability'] == 'Non-Indexable']))
    with col4: st.metric("🔄 Redirects", len(df[df['redirect_count'] > 0]))
    with col5: st.metric("⚡ Avg Response", f"{df['response_time'].mean():.2f}s" if len(df)>0 else "0s")
    with col6:
        crawled_urls = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled_urls) if st.session_state.sitemap_urls_set else []
        st.metric("👻 Orphans", len(orphans))
    
    # Tabs
    tab1, tab2, tab3, tab4, tab5, tab6, tab_struct, tab7, tab8, tab9, tab10, tab11, tab13, tab14, tab15, tab16, tab_interlink, tab_cannibal = st.tabs([
        "🔗 Internal", "🌐 External", "🖼️ Images", "📝 Titles", "📄 Meta", "🏷️ Counts", 
        "🏗️ Structure", "🔄 Redirects", "📊 Status", "🎯 Canonicals", "📱 Social", "🚀 Perf", 
        "👻 Orphans", "⛏️ Custom", "⚡ PSI", "🏗️ Schema", "💡 Interlink", "👯 Cannibalization"
    ])
    
    status_lookup = df[['url', 'status_code']].drop_duplicates()
    status_lookup.columns = ['Destination URL', 'Status Code']

    # TAB 1: INTERNAL LINKS
    with tab1:
        st.subheader("🔗 Internal Links Analysis")
        if link_selector:
            st.info(f"Showing links extracted ONLY from: `{link_selector}`")
        
        if 'internal_links' in df.columns:
            base_df = df[['url', 'internal_links']].copy()
            base_df = base_df.rename(columns={'url': 'Source URL'})
            exploded = base_df.explode('internal_links')
            exploded = exploded.dropna(subset=['internal_links'])
            
            if not exploded.empty:
                links_data = pd.json_normalize(exploded['internal_links'])
                exploded = exploded.reset_index(drop=True)
                links_data = links_data.reset_index(drop=True)
                final_links = pd.concat([exploded['Source URL'], links_data], axis=1)
                
                if 'rel_status' not in final_links.columns: final_links['rel_status'] = 'dofollow'
                if 'target' not in final_links.columns: final_links['target'] = '_self'
                
                final_links = final_links[['Source URL', 'url', 'anchor_text', 'rel_status', 'target', 'placement', 'css_path']]
                final_links.columns = ['Source URL', 'Destination URL', 'Anchor Text', 'Link Type', 'Target', 'Placement', 'CSS Path']
                
                final_links = pd.merge(final_links, status_lookup, on='Destination URL', how='left')
                
                if 'link_status_cache' not in st.session_state:
                    st.session_state.link_status_cache = {}
                
                final_links['Status Code'] = final_links.apply(
                    lambda x: st.session_state.link_status_cache.get(x['Destination URL'], x['Status Code']), axis=1
                )
                final_links['Status Code'] = final_links['Status Code'].fillna('Not Crawled').astype(str)

                col_btn, col_info = st.columns([1, 3])
                uncrawled_list = final_links[final_links['Status Code'] == 'Not Crawled']['Destination URL'].unique().tolist()
                
                if col_btn.button("🔍 Check Internal Statuses"):
                    if uncrawled_list:
                        progress_bar = col_info.progress(0)
                        status_text = col_info.empty()
                        temp_crawler = UltraFrogCrawler()
                        results = {}
                        
                        def fetch_status(url):
                            try:
                                r = temp_crawler.session.head(url, timeout=5, allow_redirects=True)
                                if r.status_code == 405:
                                    r = temp_crawler.session.get(url, timeout=5, stream=True)
                                return url, r.status_code
                            except:
                                return url, "Error"

                        with ThreadPoolExecutor(max_workers=20) as executor:
                            futures = [executor.submit(fetch_status, u) for u in uncrawled_list]
                            for i, future in enumerate(as_completed(futures)):
                                u, code = future.result()
                                results[u] = code
                                if i % 5 == 0:
                                    progress_bar.progress((i + 1) / len(uncrawled_list))
                                    status_text.text(f"Checking: {u}")
                        
                        st.session_state.link_status_cache.update(results)
                        status_text.success("✅ Internal statuses updated!")
                        time.sleep(1)
                        st.rerun()
                    else:
                        col_info.info("All internal links have status codes.")

                st.dataframe(final_links, use_container_width=True)
                
                c1, c2, c3 = st.columns(3)
                c1.metric("Nofollow Links", len(final_links[final_links['Link Type'].str.contains('nofollow')]))
                c2.metric("Sponsored Links", len(final_links[final_links['Link Type'].str.contains('sponsored')]))
                c3.metric("Broken Links (4xx/5xx)", len(final_links[final_links['Status Code'].str.match(r'4|5', na=False)]))
                
                csv = final_links.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Internal Links", csv, "internal_links.csv", "text/csv")
            else:
                st.warning("No internal links found.")

    # TAB 2: EXTERNAL LINKS
    with tab2:
        st.subheader("🌐 External Links Analysis")
        external_data = []
        for _, row in df.iterrows():
            for ext_link in row.get('external_links', []):
                external_data.append({
                    'Source URL': row['url'],
                    'Destination URL': ext_link['url'],
                    'Anchor Text': ext_link['anchor_text'],
                    'Link Type': ext_link.get('rel_status', 'dofollow'),
                    'Target': ext_link.get('target', '_self'),
                    'Placement': ext_link.get('placement', 'Unknown'),
                    'CSS Path': ext_link.get('css_path', '')
                })
        if external_data:
            ext_df = pd.DataFrame(external_data)
            ext_df = pd.merge(ext_df, status_lookup, on='Destination URL', how='left')
            
            if 'link_status_cache' not in st.session_state:
                st.session_state.link_status_cache = {}
                
            ext_df['Status Code'] = ext_df.apply(
                lambda x: st.session_state.link_status_cache.get(x['Destination URL'], x['Status Code']), axis=1
            )
            ext_df['Status Code'] = ext_df['Status Code'].fillna('Not Crawled').astype(str)

            col_btn_ext, col_info_ext = st.columns([1, 3])
            uncrawled_ext = ext_df[ext_df['Status Code'] == 'Not Crawled']['Destination URL'].unique().tolist()
            
            if col_btn_ext.button("🔍 Check External Statuses"):
                if uncrawled_ext:
                    progress_bar = col_info_ext.progress(0)
                    status_text = col_info_ext.empty()
                    temp_crawler = UltraFrogCrawler()
                    results = {}
                    
                    def fetch_status(url):
                        try:
                            r = temp_crawler.session.head(url, timeout=5, allow_redirects=True)
                            if r.status_code == 405 or r.status_code == 403: 
                                r = temp_crawler.session.get(url, timeout=5, stream=True)
                            return url, r.status_code
                        except Exception as e:
                            return url, "Error"

                    with ThreadPoolExecutor(max_workers=20) as executor:
                        futures = [executor.submit(fetch_status, u) for u in uncrawled_ext]
                        for i, future in enumerate(as_completed(futures)):
                            u, code = future.result()
                            results[u] = code
                            if i % 5 == 0:
                                progress_bar.progress((i + 1) / len(uncrawled_ext))
                                status_text.text(f"Checking: {u}")
                    
                    st.session_state.link_status_cache.update(results)
                    status_text.success("✅ External statuses updated!")
                    time.sleep(1)
                    st.rerun()
                else:
                    col_info_ext.info("All external links have status codes.")

            st.dataframe(ext_df, use_container_width=True)
            csv = ext_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download External", csv, "external_links.csv", "text/csv")
        else:
            st.info("No external links found.")

    # TAB 3: IMAGES
    with tab3:
        st.subheader("🖼️ Images Analysis")
        images_data = []
        for _, row in df.iterrows():
            imgs = row.get('images', [])
            if isinstance(imgs, str):
                try: imgs = json.loads(imgs)
                except: imgs = []
                
            for img in imgs:
                images_data.append({
                    'source_url': row['url'],
                    'image_url': img['src'],
                    'alt_text': img['alt'],
                    'title': img['title'],
                    'dimensions': f"{img['width']}x{img['height']}" if img['width'] else 'Unknown',
                    'size_kb': img.get('size_kb', 0)
                })
        
        if images_data:
            img_df = pd.DataFrame(images_data)
            
            if 'img_size_cache' not in st.session_state:
                st.session_state.img_size_cache = {}
            if st.session_state.img_size_cache:
                img_df['size_kb'] = img_df['image_url'].map(st.session_state.img_size_cache).fillna(img_df['size_kb'])

            col_btn, col_info = st.columns([1, 4])
            if col_btn.button("📏 Check Image Sizes"):
                unique_img_urls = img_df[img_df['size_kb'] == 0]['image_url'].unique().tolist()
                if unique_img_urls:
                    progress_text = col_info.empty()
                    progress_bar = col_info.progress(0)
                    temp_crawler = UltraFrogCrawler() 
                    results = {}
                    total = len(unique_img_urls)
                    with ThreadPoolExecutor(max_workers=20) as executor:
                        future_to_url = {executor.submit(temp_crawler.get_file_size, url): url for url in unique_img_urls}
                        completed = 0
                        for future in as_completed(future_to_url):
                            url = future_to_url[future]
                            try:
                                size = future.result()
                                results[url] = size
                            except:
                                results[url] = 0
                            completed += 1
                            if completed % 5 == 0:
                                progress_bar.progress(completed / total)
                                progress_text.text(f"⏳ Checking size: {completed}/{total} images...")
                    st.session_state.img_size_cache.update(results)
                    progress_text.success("✅ sizes checked!")
                    time.sleep(1)
                    st.rerun()
                else:
                    col_info.info("All image sizes are already checked.")

            st.dataframe(img_df, use_container_width=True)
            csv = img_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Images", csv, "images.csv", "text/csv")
        else:
            st.info("No images found.")

    # TAB 4: TITLES
    with tab4:
        st.subheader("📝 Titles Analysis")
        title_df = df[['url', 'title', 'title_length']].copy()
        title_df['status'] = title_df.apply(lambda row: '❌ Missing' if row['title_length']==0 else '✅ Good', axis=1)
        st.dataframe(title_df, use_container_width=True)
        csv = title_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Titles", csv, "titles.csv", "text/csv")

    # TAB 5: META DESC
    with tab5:
        st.subheader("📄 Meta Descriptions")
        meta_df = df[['url', 'meta_description', 'meta_desc_length']].copy()
        st.dataframe(meta_df, use_container_width=True)
        csv = meta_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Meta", csv, "meta_desc.csv", "text/csv")

    # TAB 6: HEADERS COUNTS
    with tab6:
        st.subheader("🏷️ Headers (H1-H4) Counts")
        # MODIFIED: Added Depth and Inlinks to this table as it's a good summary place
        header_df = df[['url', 'depth', 'inlinks_count', 'h1_count', 'h1_tags', 'h2_count']].copy()
        st.dataframe(header_df, use_container_width=True)
        csv = header_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Headers", csv, "headers.csv", "text/csv")

    # TAB STRUCTURE
    with tab_struct:
        st.subheader("🏗️ Heading Hierarchy Analysis")
        
        if 'header_structure' in df.columns:
            struct_df = df[['url', 'header_structure']].copy()
            bad_h1_count = 0
            broken_struct_count = 0
            analyzed_data = []
            problematic_urls = []  
            
            for idx, row in struct_df.iterrows():
                struct = row['header_structure']
                if isinstance(struct, str):
                    try: struct = json.loads(struct)
                    except: struct = []
                
                issues, h1_c = analyze_heading_structure(struct)
                
                has_error = False
                if h1_c != 1: 
                    bad_h1_count += 1
                    has_error = True
                if any("Skipped" in i for i in issues): 
                    broken_struct_count += 1
                    has_error = True
                
                if has_error:
                    problematic_urls.append({
                        'URL': row['url'],
                        'H1 Count': h1_c,
                        'Issues': " | ".join(issues)
                    })
                
                analyzed_data.append({
                    'url': row['url'],
                    'structure': struct,
                    'issues': issues,
                    'h1_count': h1_c
                })

            m1, m2, m3 = st.columns(3)
            m1.metric("Total Pages", len(df))
            m2.metric("❌ Bad H1 Usage", bad_h1_count, help="Pages with 0 or >1 H1 tags")
            m3.metric("⚠️ Broken Hierarchy", broken_struct_count, help="Pages skipping levels (e.g. H2->H4)")

            st.divider()

            if problematic_urls:
                st.write("### 🚨 Problematic Pages Report")
                st.dataframe(
                    pd.DataFrame(problematic_urls), 
                    use_container_width=True,
                    column_config={
                        "URL": st.column_config.LinkColumn("URL"),
                        "Issues": st.column_config.TextColumn("Issues Identified", width="large"),
                    }
                )
            else:
                st.success("✨ No hierarchy issues found across all pages!")

            st.divider()

            st.write("### 🔍 Visual Hierarchy Inspector")
            
            filter_mode = st.radio("Show:", ["All Pages", "Only Pages with Issues"], horizontal=True)
            
            if filter_mode == "Only Pages with Issues":
                dropdown_options = [d['URL'] for d in problematic_urls]
            else:
                dropdown_options = [d['url'] for d in analyzed_data]
            
            if not dropdown_options:
                st.info("No pages match the filter.")
                selected_page_url = None
            else:
                selected_page_url = st.selectbox("Select Page to Inspect:", dropdown_options, key="struct_select")

            if selected_page_url:
                page_data = next((item for item in analyzed_data if item['url'] == selected_page_url), None)
                
                if page_data:
                    if page_data['issues']:
                        for issue in page_data['issues']:
                            if "❌" in issue: st.error(issue)
                            else: st.warning(issue)
                    else:
                        st.success("✅ Perfect Heading Structure!")

                    st.markdown("#### DOM Tree:")
                    st.markdown("""
                    <style>
                    .header-node { padding: 4px; border-left: 2px solid #ddd; margin-bottom: 2px; }
                    .header-tag { font-weight: bold; color: #555; font-size: 0.8em; margin-right: 8px; }
                    .header-text { font-family: sans-serif; }
                    </style>
                    """, unsafe_allow_html=True)

                    if not page_data['structure']:
                        st.info("No headers found on this page.")
                    
                    for h in page_data['structure']:
                        indent = (h['level'] - 1) * 20
                        tag_color = "#e63946" if h['level'] == 1 else "#457b9d"
                        
                        st.markdown(
                            f"<div class='header-node' style='margin-left: {indent}px; border-left-color: {tag_color};'>"
                            f"<span class='header-tag' style='color:{tag_color}'>{h['tag'].upper()}</span>"
                            f"<span class='header-text'>{h['text']}</span>"
                            f"</div>", 
                            unsafe_allow_html=True
                        )
        else:
            st.warning("Header structure data not available. Please re-crawl the site.")

    # TAB 7: REDIRECTS
    with tab7:
        st.subheader("🔄 Redirects")
        redirect_df = df[df['redirect_count'] > 0].copy()
        if not redirect_df.empty:
            st.dataframe(redirect_df[['url', 'original_url', 'status_code']], use_container_width=True)
            csv = redirect_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Redirects", csv, "redirects.csv", "text/csv")
        else:
            st.success("No redirects found.")

    # TAB 8: STATUS
    with tab8:
        st.subheader("📊 Status Codes")
        st.dataframe(df[['url', 'status_code', 'indexability']], use_container_width=True)
        csv = df[['url', 'status_code']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Status", csv, "status_codes.csv", "text/csv")

    # TAB 9: CANONICALS
    with tab9:
        st.subheader("🎯 Canonicals")
        can_df = df[['url', 'canonical_url']].copy()
        def check_canonical(row):
            c_url = row['canonical_url']
            if not c_url: return "❌ Missing"
            if row['url'] == c_url: return "✅ Match"
            return "⚠️ Mismatch"

        can_df['Status'] = can_df.apply(check_canonical, axis=1)
        st.dataframe(can_df, use_container_width=True)
        csv = can_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Canonicals", csv, "canonicals.csv", "text/csv")

    # TAB 10: SOCIAL
    with tab10:
        st.subheader("📱 Social Tags")
        st.dataframe(df[['url', 'og_title', 'twitter_title']], use_container_width=True)
        csv = df[['url', 'og_title', 'twitter_title']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Social", csv, "social_tags.csv", "text/csv")

    # TAB 11: PERFORMANCE
    with tab11:
        st.subheader("🚀 Performance Stats")
        st.dataframe(df[['url', 'response_time', 'word_count', 'content_length']], use_container_width=True)
        csv = df[['url', 'response_time']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Performance", csv, "performance.csv", "text/csv")

    # TAB 13: ORPHANS
    with tab13:
        st.subheader("👻 Orphan Pages")
        if orphans:
            orphan_df = pd.DataFrame(orphans, columns=['Orphan URL'])
            st.dataframe(orphan_df, use_container_width=True)
            csv = orphan_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Orphans", csv, "orphans.csv", "text/csv")
        else:
            st.success("No orphans found (or no sitemap provided).")

    # TAB 14: CUSTOM DATA
    with tab14:
        st.subheader("⛏️ Custom Extracted Data")
        if custom_selector:
            st.info(f"Results for Selector: `{custom_selector}`")
            st.dataframe(df[['url', 'custom_extraction']], use_container_width=True)
            csv = df[['url', 'custom_extraction']].to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Custom Data", csv, "custom_data.csv", "text/csv")
        else:
            st.info("Enter a CSS Selector in the sidebar to extract custom data.")

    # TAB 15: SPEED (PSI)
    with tab15:
        st.subheader("⚡ Google PageSpeed Insights (PSI)")
        st.info("Enter your Google PageSpeed API Key in the Sidebar to use this feature.")
        
        if psi_api_key:
            check_all = st.checkbox("Select All URLs (Run for everyone)", help="⚠️ Be careful with API limits if you have thousands of URLs.")
            if check_all:
                urls_to_test = df['url'].tolist()
                st.write(f"Selected {len(urls_to_test)} URLs.")
            else:
                urls_to_test = st.multiselect("Select URLs to Test (Max 5 recommended)", df['url'].head(20).tolist())
            
            if st.button("🏃 Run PageSpeed Test (Mobile & Desktop)"):
                if not urls_to_test:
                    st.warning("Please select at least one URL.")
                else:
                    progress_psi = st.progress(0)
                    status_text = st.empty()
                    results = []
                    total_steps = len(urls_to_test)
                    
                    for i, u in enumerate(urls_to_test):
                        status_text.text(f"Testing {i+1}/{total_steps}: {u}...")
                        mobile_res = run_psi_test(u, psi_api_key, "mobile")
                        desktop_res = run_psi_test(u, psi_api_key, "desktop")
                        
                        row = {'url': u}
                        if "error" in mobile_res: row['Mobile Error'] = mobile_res['error']
                        else:
                            for k, v in mobile_res.items(): row[f"Mobile {k}"] = v
                                
                        if "error" in desktop_res: row['Desktop Error'] = desktop_res['error']
                        else:
                            for k, v in desktop_res.items(): row[f"Desktop {k}"] = v

                        results.append(row)
                        progress_psi.progress((i + 1) / total_steps)
                    
                    st.session_state.psi_results = results
                    status_text.success("✅ Analysis Complete!")
            
            if st.session_state.psi_results:
                psi_df = pd.DataFrame(st.session_state.psi_results)
                desired_order = ['url', 'Mobile Score', 'Desktop Score', 'Mobile LCP', 'Desktop LCP', 'Mobile FCP', 'Desktop FCP', 'Mobile CLS', 'Desktop CLS', 'Mobile INP', 'Desktop INP']
                final_cols = [c for c in desired_order if c in psi_df.columns]
                remaining_cols = [c for c in psi_df.columns if c not in final_cols]
                st.dataframe(psi_df[final_cols + remaining_cols], use_container_width=True)
                csv_psi = psi_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download PSI Report", csv_psi, "psi_report.csv", "text/csv")
        else:
            st.warning("⚠️ PSI API Key is missing. Please add it in the sidebar.")

    # TAB 16: SCHEMA VALIDATOR
    with tab16:
        st.subheader("🏗️ Schema Markup Analysis")
        schema_df = df[['url', 'schema_types', 'schema_validity', 'schema_errors']].copy()
        st.dataframe(schema_df, use_container_width=True)
        st.markdown("### 🔍 Schema Detail Viewer")
        try:
            selected_url = st.selectbox("Select URL to inspect Schema:", df['url'].tolist())
        except: selected_url = None
        
        if selected_url:
            row = df[df['url'] == selected_url].iloc[0]
            st.write(f"**Schema Status:** {row['schema_validity']}")
            if row['schema_errors']: st.error(f"Errors: {row['schema_errors']}")
            
            schema_json_str = row.get('schema_dump', '[]')
            try:
                if isinstance(schema_json_str, str): schema_json = json.loads(schema_json_str)
                else: schema_json = schema_json_str
                if schema_json: st.json(schema_json)
                else: st.info("No Schema JSON found on this page.")
            except: st.text(str(schema_json_str))

        st.markdown("---")
        st.write("### 🤖 Indexing & Robots Directives")
        c1, c2 = st.columns(2)
        with c1:
            noindex_follow_df = df[df['is_noindex_follow'] == 1][['url', 'meta_robots']]
            if not noindex_follow_df.empty:
                st.warning(f"⚠️ Found {len(noindex_follow_df)} pages with 'noindex, follow'")
                st.dataframe(noindex_follow_df, use_container_width=True)
            else: st.success("✅ No 'noindex, follow' pages.")
        with c2:
            noindex_nofollow_df = df[df['is_noindex_nofollow'] == 1][['url', 'meta_robots']]
            if not noindex_nofollow_df.empty:
                st.error(f"⛔ Found {len(noindex_nofollow_df)} pages with 'noindex, nofollow'")
                st.dataframe(noindex_nofollow_df, use_container_width=True)
            else: st.success("✅ No 'noindex, nofollow' pages.")

    # TAB 17: AI INTERLINK SUGGESTER
    with tab_interlink:
        st.subheader("💡 AI Internal Link Opportunities")
        
        if not HAS_SKLEARN:
            st.error("❌ 'scikit-learn' is not installed. Please run: `pip install scikit-learn` in your terminal to use AI features.")
        else:
            st.markdown("""
            **How this works:**
            1. We analyze the content inside your **Link Area Selector** (or Body text if empty).
            2. We compare it against the **Title & H1** of every other page.
            3. We suggest links where the content is highly relevant to another page's topic.
            """)
            
            c1, c2, c3 = st.columns(3)
            min_score = c1.slider("Minimum Relevance Score", 0, 100, 50, help="Higher = More relevant matches only")
            max_links = c2.number_input("Max Suggestions per Page", 1, 20, 5)
            
            if st.button("🚀 Generate Suggestions"):
                with st.spinner("Analyzing semantics and calculating relevance scores..."):
                    if 'scope_content' not in df.columns:
                        st.error("Please re-crawl the website to capture content data for analysis.")
                    else:
                        # Run the logic
                        suggestions_df = generate_interlink_suggestions(df, min_score=min_score, max_suggestions=max_links)
                        
                        if not suggestions_df.empty:
                            st.success(f"Found {len(suggestions_df)} new linking opportunities!")
                            st.session_state.interlink_opportunities = suggestions_df
                        else:
                            st.warning("No suggestions found. Try lowering the relevance score.")
            
            if 'interlink_opportunities' in st.session_state and not st.session_state.interlink_opportunities.empty:
                res_df = st.session_state.interlink_opportunities
                
                search_url = st.text_input("Filter by Source URL", placeholder="/blog/my-post")
                if search_url:
                    res_df = res_df[res_df['Source URL'].str.contains(search_url, case=False)]
                
                st.dataframe(
                    res_df,
                    column_config={
                        "Relevance Score": st.column_config.ProgressColumn(
                            "Relevance",
                            format="%.1f%%",
                            min_value=0,
                            max_value=100,
                        ),
                        "Suggested Target URL": st.column_config.LinkColumn("Target Link"),
                    },
                    use_container_width=True
                )
                
                csv = res_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Suggestions CSV", csv, "interlink_opportunities.csv", "text/csv")
    
    # TAB 18: CONTENT CANNIBALIZATION / MERGER
    with tab_cannibal:
        st.subheader("👯 Content Similarity & Pruning")
        st.info("Finds pages that are too similar. Helps you merge thin content or remove duplicates.")
        
        if not HAS_SKLEARN:
            st.error("❌ 'scikit-learn' is not installed. Please run: `pip install scikit-learn` in your terminal to use AI features.")
        else:
            col1, col2 = st.columns(2)
            merge_thresh = col1.slider("Merge Threshold %", 30, 90, 50, help="Lower = Find loosely related topics.")
            dupe_thresh = col2.slider("Duplicate Threshold %", 80, 100, 85, help="Higher = Find exact matches only.")
            
            if st.button("🔍 Analyze Content Similarity"):
                with st.spinner("Comparing every page against every other page..."):
                    cannibal_df = analyze_content_cannibalization(df, merge_threshold=merge_thresh/100, duplicate_threshold=dupe_thresh/100)
                    st.session_state.cannibal_data = cannibal_df
            
            if 'cannibal_data' in st.session_state and not st.session_state.cannibal_data.empty:
                data = st.session_state.cannibal_data
                
                # SECTION 1: DUPLICATES (Red Zone)
                duplicates = data[data['Recommendation'].str.contains("Remove")]
                st.write("### 🚨 High Risk: Duplicates to Remove")
                if not duplicates.empty:
                    st.error(f"Found {len(duplicates)} pairs that look nearly identical.")
                    st.dataframe(
                        duplicates,
                        column_config={
                            "Page A": st.column_config.LinkColumn("Page A"),
                            "Page B": st.column_config.LinkColumn("Page B"),
                            "Similarity": st.column_config.ProgressColumn("Similarity Score", format="%.2f", min_value=0, max_value=1),
                        },
                        use_container_width=True
                    )
                else:
                    st.success("✅ No exact duplicates found.")

                st.divider()

                # SECTION 2: MERGE CANDIDATES (Yellow Zone)
                mergers = data[data['Recommendation'].str.contains("Merge")]
                st.write("### 🤝 Opportunities: Topics to Merge")
                if not mergers.empty:
                    st.warning(f"Found {len(mergers)} pairs covering similar topics. Consider combining them.")
                    st.dataframe(
                        mergers,
                        column_config={
                            "Page A": st.column_config.LinkColumn("Page A"),
                            "Page B": st.column_config.LinkColumn("Page B"),
                            "Similarity": st.column_config.ProgressColumn("Similarity Score", format="%.2f", min_value=0, max_value=1),
                        },
                        use_container_width=True
                    )
                else:
                    st.info("No obvious merge candidates found with current settings.")
                    
            elif 'cannibal_data' in st.session_state:
                 st.info("No similarities found above the threshold.")

    st.markdown("---")
    st.header("📥 Full Report")
    
    if st.session_state.storage_mode == "SQLite" and os.path.exists(st.session_state.db_file):
        with open(st.session_state.db_file, "rb") as file:
            st.download_button("📊 Download Complete Database (SQLite)", file, "battersea_data.db", "application/octet-stream")
    else:
        csv_all = df.to_csv(index=False).encode('utf-8')
        st.download_button("📊 Download Complete Crawl Data", csv_all, "complete_crawl.csv", "text/csv")

else:
    st.info("👈 Configure your crawl settings and click '🚀 Start Crawl' to begin.")
