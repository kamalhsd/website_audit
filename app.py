import sys
import asyncio
import os

# --- FIX FOR WINDOWS & STREAMLIT COMPATIBILITY ---
if sys.platform.startswith("win"):
    asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())
# --------------------------------------------------

import streamlit as st
import requests
from bs4 import BeautifulSoup
import pandas as pd
from urllib.parse import urljoin, urlparse
import time
from collections import deque, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from datetime import datetime, timedelta
import xml.etree.ElementTree as ET
from urllib.robotparser import RobotFileParser
import streamlit.components.v1 as components
import html
import re
import threading
import sqlite3
import uuid
import traceback

# --- NEW IMPORTS FOR IMAGE OPTIMIZATION ---
try:
    from PIL import Image
    import io
    HAS_PIL = True
except ImportError:
    HAS_PIL = False
    
# --- AI & ML IMPORTS ---
try:
    from sklearn.feature_extraction.text import TfidfVectorizer
    from sklearn.metrics.pairwise import cosine_similarity
    HAS_SKLEARN = True
except ImportError:
    HAS_SKLEARN = False

# --- GRAMMAR CHECKER IMPORT (Fixes NameError) ---
try:
    import language_tool_python
    HAS_LT = True
except ImportError:
    HAS_LT = False

# --- GSC IMPORTS ---
try:
    from google.oauth2 import service_account
    from googleapiclient.discovery import build
    HAS_GSC = True
except ImportError:
    HAS_GSC = False

# --- PLAYWRIGHT IMPORT (JS RENDERING) ---
try:
    from playwright.sync_api import sync_playwright
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False

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
if 'img_real_dim_cache' not in st.session_state:
    st.session_state.img_real_dim_cache = {}
if 'img_rendered_cache' not in st.session_state:
    st.session_state.img_rendered_cache = {}
if 'link_status_cache' not in st.session_state:
    st.session_state.link_status_cache = {}
if 'gsc_service' not in st.session_state:
    st.session_state.gsc_service = None
if 'gsc_sites_list' not in st.session_state:
    st.session_state.gsc_sites_list = []
if 'gsc_merged_data' not in st.session_state:
    st.session_state.gsc_merged_data = pd.DataFrame()
if 'content_audit_data' not in st.session_state:
    st.session_state.content_audit_data = pd.DataFrame()
if 'grammar_audit_data' not in st.session_state:
    st.session_state.grammar_audit_data = pd.DataFrame()


# --- SQLITE HELPER FUNCTIONS ---
def init_db(db_path):
    conn = sqlite3.connect(db_path, check_same_thread=False)
    c = conn.cursor()
    c.execute('''
        CREATE TABLE IF NOT EXISTS pages (
            url TEXT PRIMARY KEY,
            original_url TEXT,
            final_url TEXT,
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
            custom_search_count INTEGER,
            indexability TEXT,
            crawl_timestamp TEXT,
            header_structure TEXT,
            scope_content TEXT,
            depth INTEGER, 
            error TEXT
        )
    ''')
    conn.commit()
    conn.close()

def save_row_to_db(data, db_path):
    row_data = data.copy()
    for key in ['internal_links', 'external_links', 'images', 'redirect_chain', 'schema_dump', 'header_structure']:
        if key in row_data:
            row_data[key] = json.dumps(row_data[key])
    
    if 'is_noindex_follow' in row_data:
        row_data['is_noindex_follow'] = 1 if row_data['is_noindex_follow'] else 0
    if 'is_noindex_nofollow' in row_data:
        row_data['is_noindex_nofollow'] = 1 if row_data['is_noindex_nofollow'] else 0

    columns = [
        'url', 'original_url', 'final_url', 'status_code', 'title', 'title_length', 
        'meta_description', 'meta_desc_length', 'canonical_url', 'meta_robots', 
        'is_noindex_follow', 'is_noindex_nofollow', 'h1_tags', 'h1_count', 
        'h2_tags', 'h2_count', 'h3_tags', 'h3_count', 'h4_tags', 'h4_count', 
        'word_count', 'response_time', 'content_length', 'internal_links_count', 
        'external_links_count', 'internal_links', 'external_links', 'images', 
        'image_count', 'images_without_alt', 'schema_types', 'schema_dump', 
        'schema_count', 'schema_validity', 'schema_errors', 'redirect_chain', 
        'redirect_count', 'css_files', 'js_files', 'og_title', 'og_description', 
        'twitter_title', 'custom_extraction', 'custom_search_count', 'indexability', 'crawl_timestamp', 
        'header_structure', 'scope_content', 'depth', 'error'
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

# --- GSC HELPER FUNCTIONS ---
def authenticate_gsc(json_content):
    try:
        info = json.loads(json_content)
        creds = service_account.Credentials.from_service_account_info(
            info, scopes=['https://www.googleapis.com/auth/webmasters.readonly']
        )
        service = build('searchconsole', 'v1', credentials=creds)
        return service
    except Exception as e:
        st.error(f"Authentication Error: {e}")
        return None

def list_gsc_sites(service):
    try:
        site_list = service.sites().list().execute()
        return [s['siteUrl'] for s in site_list.get('siteEntry', [])]
    except Exception as e:
        st.error(f"Error listing sites: {e}")
        return []

def fetch_gsc_data(service, site_url, start_date, end_date):
    try:
        s_date = start_date.strftime('%Y-%m-%d')
        e_date = end_date.strftime('%Y-%m-%d')
    except AttributeError:
        s_date = str(start_date)
        e_date = str(end_date)

    request = {
        'startDate': s_date, 'endDate': e_date,
        'dimensions': ['page'], 'rowLimit': 25000
    }
    
    try:
        response = service.searchanalytics().query(siteUrl=site_url, body=request).execute()
        rows = response.get('rows', [])
        data = []
        for row in rows:
            data.append({
                'url': row['keys'][0],
                'GSC Clicks': row['clicks'],
                'GSC Impressions': row['impressions'],
                'GSC CTR': row['ctr'],
                'GSC Position': row['position']
            })
        return pd.DataFrame(data)
    except Exception as e:
        st.error(f"Error fetching data: {e}")
        return pd.DataFrame()

def inspect_url_indexing(service, site_url, url_list):
    results = []
    progress_bar = st.progress(0)
    status_text = st.empty()
    total = len(url_list)
    
    for i, u in enumerate(url_list):
        progress_bar.progress((i + 1) / total)
        status_text.text(f"Inspecting {i+1}/{total}: {u}")
        try:
            req = {'inspectionUrl': u, 'siteUrl': site_url}
            resp = service.urlInspection().index().inspect(body=req).execute()
            inspection_res = resp.get('inspectionResult', {})
            index_res = inspection_res.get('indexStatusResult', {})
            mobile_res = inspection_res.get('mobileUsabilityResult', {})
            results.append({
                'url': u,
                'Coverage State': index_res.get('coverageState', 'Unknown'),
                'Indexing Status': index_res.get('indexingState', 'Unknown'),
                'Google Canonical': index_res.get('googleCanonical', 'N/A'),
                'User Canonical': index_res.get('userCanonical', 'N/A'),
                'Last Crawl Time': index_res.get('lastCrawlTime', 'Never'),
                'Mobile Usability': mobile_res.get('verdict', 'Not Tested')
            })
            time.sleep(0.2) 
        except Exception as e:
            err_msg = str(e)
            if "403" in err_msg: err_msg = "Permission Denied"
            elif "429" in err_msg: err_msg = "Quota Exceeded"
            results.append({'url': u, 'Coverage State': f"Error: {err_msg}"})
            
    status_text.success("✅ Inspection Complete!")
    return pd.DataFrame(results)

# --- AI HELPER FUNCTIONS ---
def generate_interlink_suggestions(df, min_score=40, max_suggestions=10):
    if df.empty: return pd.DataFrame()
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
    
    # 1. Filter out empty/thin pages to reduce noise
    valid_df = df[df['scope_content'].str.len() > 100].copy().reset_index(drop=True)
    if len(valid_df) < 2: return pd.DataFrame()

    # 2. Create "Weighted" Content for comparison
    # We repeat Title and H1 3 times so they are more important than body text
    valid_df['analysis_text'] = (
        (valid_df['title'].fillna('') + " ") * 3 + 
        (valid_df['h1_tags'].fillna('') + " ") * 3 + 
        valid_df['scope_content'].fillna('').str[:5000] # Limit body to 5000 chars
    )

    # 3. Calculate Similarity (TF-IDF)
    tfidf = TfidfVectorizer(stop_words='english', min_df=1)
    try:
        tfidf_matrix = tfidf.fit_transform(valid_df['analysis_text'])
    except: return pd.DataFrame()

    cosine_sim = cosine_similarity(tfidf_matrix, tfidf_matrix)
    results = []
    num_rows = len(valid_df)
    
    # 4. Compare every page against every other page
    for i in range(num_rows):
        for j in range(i + 1, num_rows):
            score = cosine_sim[i, j]
            
            # Skip if score is too low
            if score < merge_threshold: continue
            
            # Determine Action based on thresholds
            if score >= duplicate_threshold:
                action = "🚨 Remove/Redirect (Duplicate)"
                reason = "Content is nearly identical (>{}%)".format(int(duplicate_threshold*100))
            else:
                action = "🤝 Merge Content"
                reason = "Topics overlap significantly (>{}%)".format(int(merge_threshold*100))

            results.append({
                'Page A': valid_df.iloc[i]['url'],
                'Page A Title': valid_df.iloc[i]['title'],
                'Page B': valid_df.iloc[j]['url'],
                'Page B Title': valid_df.iloc[j]['title'],
                'Similarity': round(score * 100, 1),
                'Recommendation': action,
                'Reason': reason
            })
            
    return pd.DataFrame(results).sort_values(by='Similarity', ascending=False)

def generate_ai_meta(provider, api_key, model_name, endpoint_url, prompt_text, system_instruction="You are an SEO expert."):
    try:
        if provider == "Gemini":
            url = f"https://generativelanguage.googleapis.com/v1beta/models/{model_name}:generateContent?key={api_key}"
            headers = {"Content-Type": "application/json"}
            payload = {"contents": [{"parts": [{"text": f"{system_instruction}\n\n{prompt_text}"}]}]}
            response = requests.post(url, headers=headers, json=payload, timeout=30)
            if response.status_code == 200:
                data = response.json()
                return data['candidates'][0]['content']['parts'][0]['text'].strip()
            else:
                return f"Error {response.status_code}: {response.text}"
        elif provider == "OpenAI Compatible (Groq/Ollama/OpenAI)":
            headers = {"Content-Type": "application/json", "Authorization": f"Bearer {api_key}" if api_key else ""}
            payload = {
                "model": model_name,
                "messages": [{"role": "system", "content": system_instruction}, {"role": "user", "content": prompt_text}],
                "temperature": 0.7
            }
            response = requests.post(endpoint_url, headers=headers, json=payload, timeout=30)
            if response.status_code == 200:
                data = response.json()
                return data['choices'][0]['message']['content'].strip()
            else:
                return f"Error {response.status_code}: {response.text}"
    except Exception as e:
        return f"Exception: {str(e)}"
    return "Unknown Error"

def analyze_content_freshness(url, title, content, provider, api_key, model_name, endpoint_url):
    """Uses AI to determine if content is Relevant, Stale, or Outdated."""
    current_date = datetime.now().strftime("%B %Y")
    prompt = f"""
    You are an expert SEO Content Strategist. 
    Today's Date: {current_date}
    Analyze the following page content and determine its relevance for TODAY's users.
    URL: {url}
    Title: {title}
    Content Snippet: {content[:1500]}
    
    Decision Criteria:
    - KEEP: Content is evergreen, still accurate, or historically valuable.
    - UPDATE: Content is good but contains old dates, old prices, or missing newer facts.
    - REMOVE: Content is completely outdated (e.g., Covid-19 temporary rules, 2021 event guides, broken promotions).
    
    Provide your response in this EXACT format:
    DECISION: [KEEP/UPDATE/REMOVE]
    REASON: [Short explanation why]
    ACTION: [What exactly to add or change, or why to delete]
    """
    try:
        response = generate_ai_meta(provider, api_key, model_name, endpoint_url, prompt, "You are a content auditor.")
        lines = response.split('\n')
        res_dict = {"URL": url}
        for line in lines:
            if line.startswith("DECISION:"): res_dict["Decision"] = line.replace("DECISION:", "").strip()
            if line.startswith("REASON:"): res_dict["Reason"] = line.replace("REASON:", "").strip()
            if line.startswith("ACTION:"): res_dict["Action Suggestion"] = line.replace("ACTION:", "").strip()
        if "Decision" not in res_dict: res_dict["Decision"] = "Unknown"
        return res_dict
    except:
        return {"URL": url, "Decision": "Error", "Reason": "AI failed to respond", "Action Suggestion": "N/A"}

# --- GRAMMAR FALLBACK HELPER (UPDATED) ---
def check_grammar_cloud(text):
    """Fallback to direct Cloud API call if Java is missing."""
    url = "https://api.languagetool.org/v2/check"
    data = {
        'text': text,
        'language': 'en-US'
    }
    try:
        response = requests.post(url, data=data, timeout=5)
        if response.status_code == 200:
            result = response.json()
            matches = []
            for m in result.get('matches', []):
                # We capture offset/length to extract the specific wrong word later
                replacements = [r['value'] for r in m.get('replacements', [])][:3]
                matches.append({
                    'message': m.get('message', ''),
                    'replacements': replacements,
                    'offset': m.get('offset', 0),
                    'length': m.get('length', 0)
                })
            return matches
        return []
    except Exception:
        return []
# --- CRAWLER CLASS ---
class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None, link_selector=None, search_config=None, use_js=False):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector
        self.search_config = search_config
        self.use_js = use_js 
        
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Accept-Encoding': 'gzip, deflate',
            'Connection': 'keep-alive',
            'Upgrade-Insecure-Requests': '1'
        })
        adapter = requests.adapters.HTTPAdapter(pool_connections=20, pool_maxsize=20, max_retries=1)
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
        else:
            return (base_clean == target_clean and parsed.path.startswith(self.base_path))
    
    def can_fetch(self, url):
        if self.ignore_robots: return True
        try:
            domain = urlparse(url).netloc
            if domain not in self.robots_cache:
                try:
                    rp = RobotFileParser()
                    rp.set_url(f"https://{domain}/robots.txt")
                    rp.read()
                    self.robots_cache[domain] = rp
                except: self.robots_cache[domain] = None
            if self.robots_cache[domain] is None: return True
            return self.robots_cache[domain].can_fetch('*', url)
        except: return True

    def smart_clean(self, text):
        if not text: return ""
        text = str(text)
        text = html.unescape(text)
        text = re.sub(r'[\r\n\t]+', ' ', text)
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def get_css_path(self, element):
        path = []
        for parent in element.parents:
            if parent.name == '[document]': break
            selector = parent.name
            if parent.get('id'): selector += f"#{parent['id']}"
            elif parent.get('class'): selector += f".{parent['class'][0]}"
            path.append(selector)
        path.reverse()
        element_selector = element.name
        if element.get('class'): element_selector += f".{element['class'][0]}"
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
                        if loc is not None: urls.extend(self.extract_sitemap_urls(loc.text))
                else:
                    url_elements = root.findall('.//sitemap:url', namespaces)
                    for url_elem in url_elements:
                        loc = url_elem.find('sitemap:loc', namespaces)
                        if loc is not None: urls.append(loc.text)
        except Exception as e: st.error(f"Error parsing sitemap: {e}")
        return urls
        
    def get_file_size(self, url):
        try:
            r = self.session.head(url, timeout=2)
            if 'content-length' in r.headers: return round(int(r.headers['content-length']) / 1024, 2)
        except: pass
        return 0

    def extract_recursive_types(self, data, types_list):
        if isinstance(data, dict):
            if '@type' in data:
                if isinstance(data['@type'], list): types_list.extend(data['@type'])
                else: types_list.append(data['@type'])
            for key, value in data.items(): self.extract_recursive_types(value, types_list)
        elif isinstance(data, list):
            for item in data: self.extract_recursive_types(item, types_list)

    def fetch_with_playwright(self, url):
        """Uses Playwright to render the page content."""
        if not HAS_PLAYWRIGHT:
            return None, "Playwright library not found."
        
        try:
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                context = browser.new_context(user_agent='Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')
                page = context.new_page()
                page.goto(url, wait_until="networkidle", timeout=30000) 
                content = page.content() 
                
                class MockResponse:
                    def __init__(self, url, content, status_code):
                        self.url = url
                        self.content = content.encode('utf-8')
                        self.text = content
                        self.status_code = status_code
                        self.history = []
                        self.elapsed = type('obj', (object,), {'total_seconds': lambda: 1.0})
                
                browser.close()
                return MockResponse(url, content, 200), None
        except Exception as e:
            return None, str(e)

    def extract_page_data(self, url):
        try:
            if self.use_js:
                response, error_msg = self.fetch_with_playwright(url)
                if not response:
                    raise Exception(error_msg)
            else:
                response = self.session.get(url, timeout=10, allow_redirects=True)
            
            actual_status_code = response.status_code
            if hasattr(response, 'history') and response.history:
                actual_status_code = response.history[0].status_code

            soup = BeautifulSoup(response.content, 'html.parser')
            
            custom_search_count = 0
            if self.search_config and self.search_config.get('query'):
                query = self.search_config['query']
                mode = self.search_config['mode']
                scope = self.search_config['scope']
                
                search_target = ""
                if mode == "CSS Selector Existence":
                    try:
                        elements = soup.select(query)
                        custom_search_count = len(elements)
                    except: custom_search_count = 0
                else:
                    if scope == "HTML Source Code": search_target = response.text
                    else: search_target = soup.get_text()
                    
                    if mode == "Text (Case Insensitive)": custom_search_count = search_target.lower().count(query.lower())
                    elif mode == "Text (Case Sensitive)": custom_search_count = search_target.count(query)
                    elif mode == "Regex":
                        try: custom_search_count = len(re.findall(query, search_target))
                        except: custom_search_count = 0

            scope_content = ""
            if self.link_selector:
                scoped_element = soup.select_one(self.link_selector)
                if scoped_element: scope_content = self.smart_clean(scoped_element.get_text())
            else:
                if soup.body: scope_content = self.smart_clean(soup.body.get_text())[:50000]

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
                if 'noindex' in directives and 'follow' in directives: is_noindex_follow = True
                elif 'noindex' in directives and 'nofollow' in directives: is_noindex_nofollow = True

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
                if specific_section: search_area = specific_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(response.url, link['href']) 
                href = href.split('#')[0]
                if not href: continue

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
                if link_netloc == base_domain_clean: internal_links.append(link_data)
                else: external_links.append(link_data)
            
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
                'final_url': response.url,
                'status_code': actual_status_code,
                'title': title_text, 'title_length': len(title_text),
                'meta_description': meta_desc_text, 'meta_desc_length': len(meta_desc_text),
                'canonical_url': canonical_url, 'meta_robots': robots_content,
                'is_noindex_follow': is_noindex_follow, 'is_noindex_nofollow': is_noindex_nofollow,
                'h1_tags': '; '.join(h1_tags), 'h1_count': len(h1_tags),
                'h2_tags': '; '.join(h2_tags), 'h2_count': len(h2_tags),
                'h3_tags': '; '.join(h3_tags), 'h3_count': len(h3_tags),
                'h4_tags': '; '.join(h4_tags), 'h4_count': len(h4_tags),
                'word_count': word_count, 'response_time': 1.0, 
                'content_length': len(response.content) if hasattr(response, 'content') else len(response.text),
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
                'custom_search_count': custom_search_count,
                'indexability': self.get_indexability_status(actual_status_code, robots_content),
                'crawl_timestamp': datetime.now().isoformat(), 
                'header_structure': header_structure, 
                'scope_content': scope_content, 
                'error': ''
            }
        except Exception as e:
            return {
                'url': url, 'original_url': url, 'final_url': url, 'status_code': 0, 'error': str(e),
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
                'custom_extraction': '', 'custom_search_count': 0, 'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat(),
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

# --- PRODUCTION HELPER: VISUAL DIMENSIONS (PLAYWRIGHT) ---
def measure_rendered_images(url_list, progress_callback=None):
    """
    Robust scanner:
    1. Scrolls down to trigger lazy loading.
    2. Uses 'stealth' arguments to avoid bot detection.
    3. Waits for network idle to ensure images render.
    """
    if not HAS_PLAYWRIGHT:
        return {}, "Playwright not installed"

    results = {}
    total_images_found = 0
    import traceback 

    try:
        from playwright.sync_api import sync_playwright
        with sync_playwright() as p:
            # 1. Launch Browser in 'Stealth' mode (looks like real Chrome)
            try:
                browser = p.chromium.launch(
                    headless=True,
                    args=["--disable-blink-features=AutomationControlled"]
                )
            except Exception as e:
                return {}, f"BROWSER LAUNCH FAILED: {str(e)}\n\nTry running: playwright install"
            
            # Common User Agent
            REAL_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
            
            # Context 1: Desktop
            context_desk = browser.new_context(
                viewport={"width": 1920, "height": 1080},
                user_agent=REAL_USER_AGENT,
                locale='en-US'
            )
            page_desk = context_desk.new_page()

            # Context 2: Mobile
            context_mob = browser.new_context(
                viewport={"width": 390, "height": 844},
                user_agent="Mozilla/5.0 (iPhone; CPU iPhone OS 16_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.0 Mobile/15E148 Safari/604.1",
                is_mobile=True,
                locale='en-US'
            )
            page_mob = context_mob.new_page()

            total = len(url_list)
            for i, url in enumerate(url_list):
                if progress_callback:
                    progress_callback(i, total, url)

                # --- MEASURE DESKTOP ---
                try:
                    page_desk.goto(url, wait_until="domcontentloaded", timeout=25000)
                    
                    # 2. Smooth Auto-Scroll (Crucial for Lazy Loading)
                    page_desk.evaluate("""
                        async () => {
                            const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
                            for (let i = 0; i < document.body.scrollHeight; i += 500) {
                                window.scrollTo(0, i);
                                await delay(50); 
                            }
                        }
                    """)
                    time.sleep(0.5) # Settle time
                    
                    # 3. Extract Data (CurrentSrc handles responsive images)
                    imgs_desk = page_desk.evaluate("""
                        Array.from(document.querySelectorAll('img')).map(img => {
                            const rect = img.getBoundingClientRect();
                            return {
                                src: img.currentSrc || img.src, 
                                width: Math.round(rect.width),
                                height: Math.round(rect.height),
                                natural: img.naturalWidth + 'x' + img.naturalHeight,
                                is_visible: rect.width > 0 && rect.height > 0
                            }
                        })
                    """)
                    
                    for img in imgs_desk:
                        src = img['src']
                        if not src or src.startswith('data:'): continue
                        
                        if src not in results: results[src] = {}
                        
                        if img['width'] > 0:
                            results[src]['Desktop'] = f"{img['width']}x{img['height']}"
                            results[src]['Natural'] = img['natural']
                            total_images_found += 1

                except Exception as e:
                    print(f"Desktop Error {url}: {e}")

                # --- MEASURE MOBILE ---
                try:
                    page_mob.goto(url, wait_until="domcontentloaded", timeout=20000)
                    page_mob.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                    time.sleep(0.5)
                    
                    imgs_mob = page_mob.evaluate("""
                        Array.from(document.querySelectorAll('img')).map(img => {
                            const rect = img.getBoundingClientRect();
                            return { src: img.currentSrc || img.src, width: Math.round(rect.width), height: Math.round(rect.height) }
                        })
                    """)
                    
                    for img in imgs_mob:
                        src = img['src']
                        if not src or src.startswith('data:'): continue
                        if src not in results: results[src] = {}
                        if img['width'] > 0:
                            results[src]['Mobile'] = f"{img['width']}x{img['height']}"

                except Exception:
                    pass

            browser.close()
            return results, total_images_found

    except Exception as e:
        error_details = traceback.format_exc()
        return {}, f"CRASH DETAILS:\n{error_details}"

# --- CRAWLER HANDLERS ---
def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, search_config=None, use_js=False, storage="RAM"):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector, search_config, use_js)
    crawler.set_base_url(start_url)
    
    if storage == "SQLite":
        init_db(st.session_state.db_file) 
    else:
        st.session_state.crawl_data = [] 
    
    urls_to_visit = deque([(start_url, 0)]) 
    visited_urls = set()
    st.session_state.total_crawled_count = 0
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    
    worker_count = 1 if use_js else 5
    if use_js: st.warning("🐢 JavaScript Rendering is ON. Speed reduced to 1 URL at a time to prevent crashes.")
    
    with ThreadPoolExecutor(max_workers=worker_count) as executor:
        while urls_to_visit and len(visited_urls) < max_urls:
            if st.session_state.stop_crawling: break
                
            current_batch = []
            batch_size = min(20, len(urls_to_visit), max_urls - len(visited_urls))
            
            for _ in range(batch_size):
                if urls_to_visit and not st.session_state.stop_crawling:
                    url, depth = urls_to_visit.popleft()
                    if url not in visited_urls and crawler.can_fetch(url):
                        current_batch.append((url, depth))
                        visited_urls.add(url)
            
            if not current_batch: break
            
            future_to_url = {executor.submit(crawler.extract_page_data, u): (u, d) for u, d in current_batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: f.cancel()
                    break
                try:
                    page_data = future.result(timeout=60 if use_js else 12) 
                    _, current_depth = future_to_url[future]
                    page_data['depth'] = current_depth
                    
                    if storage == "SQLite":
                        save_row_to_db(page_data, st.session_state.db_file) 
                    else:
                        st.session_state.crawl_data.append(page_data)

                    st.session_state.total_crawled_count += 1
                    
                    if not st.session_state.stop_crawling:
                        for link_data in page_data.get('internal_links', []):
                            link_url = link_data['url']
                            if (link_url not in visited_urls and 
                                not any(link_url == u[0] for u in urls_to_visit) and 
                                crawler.should_crawl_url(link_url) and 
                                len(visited_urls) + len(urls_to_visit) < max_urls):
                                urls_to_visit.append((link_url, current_depth + 1))
                    
                    progress = min(st.session_state.total_crawled_count / max_urls, 1.0)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {st.session_state.total_crawled_count} | Queue: {len(urls_to_visit)} | Speed: {st.session_state.total_crawled_count/max(1, time.time() - st.session_state.get('start_time', time.time())):.1f} URLs/sec")
                except Exception as e: st.error(f"Error: {e}")
    return True

def crawl_from_list(url_list, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, search_config=None, use_js=False, storage="RAM"):
    # --- FIX: Deduplicate the input list immediately ---
    # 1. Strip whitespace and remove empty lines
    clean_urls = [u.strip() for u in url_list if u.strip()]
    # 2. Convert to set to remove duplicates, then back to list
    unique_urls = list(set(clean_urls))
    
    # Show a message if duplicates were removed
    if len(clean_urls) > len(unique_urls):
        diff = len(clean_urls) - len(unique_urls)
        st.toast(f"🧹 Removed {diff} duplicate URLs from your list.", icon="ℹ️")

    # Initialize crawler with the CORRECT unique count
    crawler = UltraFrogCrawler(len(unique_urls), ignore_robots, custom_selector=custom_selector, link_selector=link_selector, search_config=search_config, use_js=use_js)
    
    if storage == "SQLite":
        init_db(st.session_state.db_file) 
    else:
        st.session_state.crawl_data = []

    st.session_state.total_crawled_count = 0
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    
    # Filter valid URLs (Robots.txt check)
    valid_urls = [url for url in unique_urls if crawler.can_fetch(url)]
    
    if not valid_urls: 
        st.error("No valid URLs found (check robots.txt or your list).")
        return False
    
    worker_count = 1 if use_js else 5
    if use_js: st.warning("🐢 JavaScript Rendering is ON. Speed reduced to 1 URL at a time.")

    with ThreadPoolExecutor(max_workers=worker_count) as executor:
        for i in range(0, len(valid_urls), 25):
            if st.session_state.stop_crawling: break
            batch = valid_urls[i:i + 25]
            future_to_url = {executor.submit(crawler.extract_page_data, url): url for url in batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: f.cancel()
                    break
                try:
                    page_data = future.result(timeout=60 if use_js else 12)
                    page_data['depth'] = 0 
                    
                    if storage == "SQLite":
                        save_row_to_db(page_data, st.session_state.db_file) 
                    else:
                        st.session_state.crawl_data.append(page_data)

                    st.session_state.total_crawled_count += 1
                    # Progress based on UNIQUE count
                    progress = st.session_state.total_crawled_count / len(valid_urls)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Processed: {st.session_state.total_crawled_count}/{len(valid_urls)}")
                except Exception as e: st.error(f"Error: {e}")
    return True

def crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, search_config=None, use_js=False, storage="RAM"):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, custom_selector=custom_selector, link_selector=link_selector, search_config=search_config, use_js=use_js)
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
    return crawl_from_list(sitemap_urls, progress_container, ignore_robots, custom_selector, link_selector, search_config, use_js, storage)

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
    use_js = st.checkbox("🐢 Enable JavaScript Rendering (Playwright)", help="Slow! Use for React/Angular sites only.")
    
    st.markdown("---")
    st.subheader("🔍 Custom Search")
    st.info("Find text, regex, or elements across pages (like Screaming Frog).")
    search_query = st.text_input("Search Text / Regex / Selector", help="Enter text to find")
    search_mode = st.selectbox("Search Type", ["Text (Case Insensitive)", "Text (Case Sensitive)", "Regex", "CSS Selector Existence"])
    search_scope = st.selectbox("Look In", ["Visible Text Content", "HTML Source Code"], disabled=(search_mode=="CSS Selector Existence"))
    
    st.markdown("---")
    st.subheader("⛏️ Custom Extraction")
    custom_selector = st.text_input("Data Selector (Optional)", placeholder=".price, h1, #sku", help="Extract text from specific elements")
    
    st.subheader("🎯 Link Scope (Optional)")
    link_selector = st.text_input("Link Area Selector", placeholder=".sidebar, #footer, .content", help="Only extract links found inside this element")
    
    st.markdown("---")
    st.subheader("⚡ PageSpeed Insights")
    psi_api_key = st.text_input("Google API Key (Optional)", type="password", help="AIzaSyDAdUhiOXqTRB-rvyfNmQkCAgYQkN8AjSE")

    st.markdown("---")
    st.subheader("📈 Search Console")
    
    if not HAS_GSC:
        st.error("Library missing. Run: `pip install google-api-python-client google-auth`")
    else:
        # Auto-Load Logic
        LOCAL_KEY_PATH = "gsc_config.json"
        existing_key = None
        if os.path.exists(LOCAL_KEY_PATH):
            st.success(f"🔑 Key loaded from {LOCAL_KEY_PATH}")
            with open(LOCAL_KEY_PATH, "r") as f: existing_key = f.read()
        
        if existing_key:
            with st.expander("🔄 Change JSON Key"):
                gsc_auth_file = st.file_uploader("Upload New JSON Key", type=['json'])
        else:
            gsc_auth_file = st.file_uploader("Upload JSON Key", type=['json'], help="Upload the Service Account JSON key.")
        
        current_file_content = None
        if gsc_auth_file:
            current_file_content = gsc_auth_file.getvalue().decode("utf-8")
            with open(LOCAL_KEY_PATH, "w") as f: f.write(current_file_content)
            st.rerun()
        elif existing_key:
            current_file_content = existing_key

        if current_file_content:
            if 'last_gsc_key' not in st.session_state or st.session_state.last_gsc_key != current_file_content:
                st.session_state.last_gsc_key = current_file_content
                st.session_state.gsc_service = authenticate_gsc(current_file_content)
                if st.session_state.gsc_service:
                    st.session_state.gsc_sites_list = list_gsc_sites(st.session_state.gsc_service)
            
            if st.session_state.gsc_sites_list:
                gsc_property = st.selectbox("Select GSC Property", st.session_state.gsc_sites_list)
                
                today = datetime.now().date()
                default_start = today - timedelta(days=28)
                
                date_range = st.date_input(
                    "📅 Select Date Range",
                    value=(default_start, today),
                    max_value=today,
                    format="DD/MM/YYYY"
                )
            else:
                st.warning("Authenticated, but no sites found. Did you add the service account email to your GSC property?")
                gsc_property = None
        else:
            gsc_property = None

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
        
        if "SQLite" in storage_option:
            st.session_state.storage_mode = "SQLite"
            st.session_state.crawl_data = [] 
            if os.path.exists(st.session_state.db_file):
                try: os.remove(st.session_state.db_file)
                except: pass
            st.session_state.db_file = f"battersea_data_{uuid.uuid4().hex}.db"
        else:
            st.session_state.storage_mode = "RAM"

        search_config = None
        if search_query:
            search_config = {
                "query": search_query,
                "mode": search_mode,
                "scope": search_scope
            }

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
            st.session_state.search_config = search_config
            st.rerun()
        else:
            st.error("Please provide valid input")
    
    if st.button("🗑️ Clear All Data"):
        st.session_state.crawl_data = []
        if os.path.exists(st.session_state.db_file):
            try: os.remove(st.session_state.db_file)
            except: pass
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
        s_conf = st.session_state.get('search_config', None)
        
        if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
            crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots, custom_sel, link_sel, s_conf, use_js, mode_val)
        elif crawl_mode == "📝 List Mode (Upload URLs)":
            if uploaded_file:
                content = uploaded_file.read().decode('utf-8')
                url_list = [line.strip() for line in content.split('\n') if line.strip()]
            else:
                url_list = [line.strip() for line in url_list_text.split('\n') if line.strip()]
            crawl_from_list(url_list, progress_container, ignore_robots, custom_sel, link_sel, s_conf, use_js, mode_val)
        else:
            crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots, custom_sel, link_sel, s_conf, use_js, mode_val)
        
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

if has_data and df is not None:
    inlinks_counter = Counter()
    for _, row in df.iterrows():
        links = row.get('internal_links', [])
        if isinstance(links, str): 
            try: links = json.loads(links)
            except: links = []
        for link in links:
            inlinks_counter[link['url']] += 1
            
    df['inlinks_count'] = df['url'].map(inlinks_counter).fillna(0).astype(int)
    
    if 'depth' not in df.columns: df['depth'] = 0
    else: df['depth'] = df['depth'].fillna(0).astype(int)

    if 'custom_search_count' not in df.columns: df['custom_search_count'] = 0
    else: df['custom_search_count'] = df['custom_search_count'].fillna(0).astype(int)

if has_data and df is not None:
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
    
    # Tabs - MODIFIED: Merged "Counts" and "Structure" into "Header Analysis"
    tab1, tab2, tab3, tab_meta_titles, tab_headers, tab7, tab8, tab9, tab10, tab11, tab13, tab14, tab15, tab16, tab_search, tab_interlink, tab_cannibal, tab_gsc, tab_audit = st.tabs([
        "🔗 Internal", "🌐 External", "🖼️ Images", "📝 Meta & Titles", "🏗️ Header Analysis", 
        "🔄 Redirects", "📊 Status", "🎯 Canonicals", "📱 Social", "🚀 Perf", 
        "👻 Orphans", "⛏️ Custom", "⚡ PSI", "🏗️ Schema", "🔍 Search Results", "💡 Interlink", "👯 Cannibalization", "📈 GSC Data", "📅 Content Audit"
    ])
    
    status_lookup = df[['url', 'status_code']].drop_duplicates()
    status_lookup.columns = ['Destination URL', 'Status Code']

   # --- ADD THIS IMPORT AT THE TOP IF MISSING ---
    import difflib 

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
                
                # Ensure all columns are present
                final_links = final_links[['Source URL', 'url', 'anchor_text', 'rel_status', 'target', 'placement', 'css_path']]
                final_links.columns = ['Source URL', 'Destination URL', 'Anchor Text', 'Link Type', 'Target', 'Placement', 'CSS Path']
                
                # --- ADD INLINKS & OUTLINKS COLUMNS ---
                counts_lookup = df[['url', 'inlinks_count', 'internal_links_count']].copy()
                counts_lookup.columns = ['Source URL', 'Source Inlinks', 'Source Outlinks']
                final_links = pd.merge(final_links, counts_lookup, on='Source URL', how='left')
                
                # --- ADD LINK SCOPE ---
                final_links['Link Scope'] = final_links.apply(
                    lambda x: '🔄 Same Page' if x['Source URL'] == x['Destination URL'] else '➡️ Different Page', 
                    axis=1
                )

                # Merge with Status Codes
                final_links = pd.merge(final_links, status_lookup, on='Destination URL', how='left')
                
                if 'link_status_cache' not in st.session_state:
                    st.session_state.link_status_cache = {}
                
                final_links['Status Code'] = final_links.apply(
                    lambda x: st.session_state.link_status_cache.get(x['Destination URL'], x['Status Code']), axis=1
                )
                final_links['Status Code'] = final_links['Status Code'].fillna('Not Crawled').astype(str)

                # --- TOOLBAR ---
                st.write("### 🛠️ Link Tools")
                c_btn1, c_btn2 = st.columns([1, 1])
                
                # Button 1: Status Check
                if c_btn1.button("🔍 Check Status Codes"):
                    uncrawled_list = final_links[final_links['Status Code'] == 'Not Crawled']['Destination URL'].unique().tolist()
                    if uncrawled_list:
                        progress_bar = st.progress(0)
                        status_text = st.empty()
                        temp_crawler = UltraFrogCrawler()
                        results = {}
                        
                        def fetch_status(url):
                            try:
                                r = temp_crawler.session.head(url, timeout=5, allow_redirects=True)
                                if r.status_code == 405:
                                    r = temp_crawler.session.get(url, timeout=5, stream=True)
                                return url, r.status_code
                            except: return url, "Error"

                        with ThreadPoolExecutor(max_workers=20) as executor:
                            futures = [executor.submit(fetch_status, u) for u in uncrawled_list]
                            for i, future in enumerate(as_completed(futures)):
                                u, code = future.result()
                                results[u] = code
                                if i % 5 == 0:
                                    progress_bar.progress((i + 1) / len(uncrawled_list))
                                    status_text.text(f"Checking: {u}")
                        
                        st.session_state.link_status_cache.update(results)
                        st.rerun()
                    else:
                        st.info("All statuses already checked.")

                # Button 2: Anchor Context Analysis
                calc_relevance = c_btn2.button("🧠 Analyze Anchor Relevance (0-100)")
                
                if calc_relevance:
                    with st.spinner("Comparing Anchor Text vs. Target URL Slug..."):
                        def get_anchor_score(row):
                            anchor = str(row['Anchor Text']).lower().strip()
                            url = str(row['Destination URL']).lower().strip()
                            
                            parsed = urlparse(url)
                            path = parsed.path
                            if '.' in path.split('/')[-1]: path = os.path.splitext(path)[0]
                            slug = path.replace('-', ' ').replace('_', ' ').replace('/', ' ').strip()
                            
                            if not slug or slug == "":
                                if "home" in anchor or "brand" in anchor: return 100
                                return 50 
                            
                            generics = ['click here', 'read more', 'learn more', 'here', 'website', 'link']
                            if anchor in generics: return 10
                            
                            score = difflib.SequenceMatcher(None, anchor, slug).ratio()
                            return int(score * 100)

                        final_links['Relevance Score'] = final_links.apply(get_anchor_score, axis=1)
                        st.success("Analysis Complete!")

                # --- DISPLAY ---
                st.markdown("---")
                
                col_config = {
                    "Source URL": st.column_config.LinkColumn("From Page"),
                    "Destination URL": st.column_config.LinkColumn("To Page"),
                    "Link Scope": st.column_config.TextColumn("Relationship", width="small"),
                    "Source Inlinks": st.column_config.NumberColumn("Page Inlinks", help="Total incoming links to the Source URL"),
                    "Source Outlinks": st.column_config.NumberColumn("Page Outlinks", help="Total outgoing links from the Source URL"),
                }
                
                # CORRECTED ORDER: Included Target, Placement, CSS Path
                cols_order = [
                    'Source URL', 'Source Inlinks', 'Source Outlinks', 
                    'Destination URL', 'Link Scope', 'Anchor Text', 'Link Type', 
                    'Target', 'Placement', 'CSS Path', 'Status Code'
                ]
                
                if 'Relevance Score' in final_links.columns:
                    col_config["Relevance Score"] = st.column_config.ProgressColumn(
                        "Anchor Match %", format="%d", min_value=0, max_value=100
                    )
                    cols_order.append('Relevance Score')
                    final_links = final_links.sort_values(by="Relevance Score", ascending=True)

                existing_cols = [c for c in cols_order if c in final_links.columns]
                
                st.dataframe(
                    final_links[existing_cols], 
                    use_container_width=True, 
                    column_config=col_config
                )
                
                # Stats
                c1, c2, c3, c4 = st.columns(4)
                c1.metric("Total Links", len(final_links))
                c2.metric("Self-Referencing", len(final_links[final_links['Link Scope'].str.contains('Same')]))
                c3.metric("Nofollow", len(final_links[final_links['Link Type'].str.contains('nofollow')]))
                c4.metric("Broken", len(final_links[final_links['Status Code'].str.match(r'4|5', na=False)]))
                
                csv = final_links.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Link Report", csv, "internal_links.csv", "text/csv")
            else:
                st.warning("No internal links found.")

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

    with tab3:
        st.subheader("🖼️ Images Analysis")
        
        # --- 1. PREPARE DATA ---
        images_data = []
        for _, row in df.iterrows():
            imgs = row.get('images', [])
            if isinstance(imgs, str):
                try: imgs = json.loads(imgs)
                except: imgs = []
                
            for img in imgs:
                html_w = str(img.get('width', '')).strip()
                html_h = str(img.get('height', '')).strip()
                
                if html_w and html_h: html_dim_str = f"{html_w}x{html_h}"
                elif html_w: html_dim_str = f"{html_w}x?"
                elif html_h: html_dim_str = f"?x{html_h}"
                else: html_dim_str = "Missing in HTML"

                images_data.append({
                    'source_url': row['url'],
                    'image_url': img['src'],
                    'alt_text': img['alt'],
                    'html_dimensions': html_dim_str,
                    'real_dimensions': 'Not Checked',
                    'rendered_desktop': 'Not Scanned',
                    'rendered_mobile': 'Not Scanned',
                    'size_kb': img.get('size_kb', 0),
                    'status': 'Pending Check'
                })
        
        if images_data:
            img_df = pd.DataFrame(images_data)
            
            # --- 2. CACHE MANAGEMENT ---
            if 'img_size_cache' not in st.session_state: st.session_state.img_size_cache = {}
            if st.session_state.img_size_cache:
                img_df['size_kb'] = img_df['image_url'].map(st.session_state.img_size_cache).fillna(img_df['size_kb'])

            if 'img_real_dim_cache' not in st.session_state: st.session_state.img_real_dim_cache = {}
            if st.session_state.img_real_dim_cache:
                img_df['real_dimensions'] = img_df.apply(lambda x: st.session_state.img_real_dim_cache.get(x['image_url'], x['real_dimensions']), axis=1)

            if 'img_rendered_cache' not in st.session_state: st.session_state.img_rendered_cache = {}
            
            # Smart Matching Logic
            def normalize_url(u):
                if not u: return ""
                u = u.split('?')[0].split('#')[0]
                return u.replace('https://', '').replace('http://', '').replace('www.', '')

            def get_rendered_data(img_url, key):
                cache = st.session_state.img_rendered_cache
                if not cache: return 'Not Scanned'
                if img_url in cache and key in cache[img_url]: return cache[img_url][key]
                clean_target = normalize_url(img_url)
                for cache_url, data in cache.items():
                    if clean_target in cache_url or normalize_url(cache_url) == clean_target:
                        return data.get(key, 'Not Scanned')
                return 'Not Scanned'

            if st.session_state.img_rendered_cache:
                img_df['rendered_desktop'] = img_df['image_url'].apply(lambda x: get_rendered_data(x, 'Desktop'))
                img_df['rendered_mobile'] = img_df['image_url'].apply(lambda x: get_rendered_data(x, 'Mobile'))
                def update_natural(row):
                    if row['real_dimensions'] == 'Not Checked':
                        return get_rendered_data(row['image_url'], 'Natural').replace('Not Scanned', 'Not Checked')
                    return row['real_dimensions']
                img_df['real_dimensions'] = img_df.apply(update_natural, axis=1)

            # --- 3. ACTION BUTTONS ---
            st.write("#### 🛠️ Image Tools")
            col_kb, col_px, col_vis = st.columns([1, 1, 1.5])
            
            with col_kb:
                if st.button("1️⃣ Check File Sizes"):
                    targets = img_df[img_df['size_kb'] == 0]['image_url'].unique().tolist()
                    if targets:
                        p_bar = st.progress(0)
                        crawler_temp = UltraFrogCrawler()
                        res = {}
                        with ThreadPoolExecutor(max_workers=20) as exe:
                            futures = {exe.submit(crawler_temp.get_file_size, u): u for u in targets}
                            for i, f in enumerate(as_completed(futures)):
                                u = futures[f]
                                try: res[u] = f.result()
                                except: res[u] = 0
                                if i%5==0: p_bar.progress((i+1)/len(targets))
                        st.session_state.img_size_cache.update(res)
                        st.rerun()

            with col_px:
                if st.button("2️⃣ Check Real Dims"):
                    targets = img_df[
                        (img_df['real_dimensions'] == 'Not Checked') | 
                        (img_df['real_dimensions'] == 'Error')
                    ]['image_url'].unique().tolist()
                    if targets:
                        p_bar = st.progress(0)
                        results_cache = {}
                        def get_pil_dims(u):
                            try:
                                r = requests.get(u, timeout=8, headers={'User-Agent': 'Mozilla/5.0'}, verify=False)
                                if r.status_code == 200:
                                    image_file = io.BytesIO(r.content)
                                    img = Image.open(image_file)
                                    return u, f"{img.width}x{img.height}"
                                return u, f"Error {r.status_code}"
                            except: return u, "Error"
                        
                        with ThreadPoolExecutor(max_workers=10) as exe:
                            futures = {exe.submit(get_pil_dims, u): u for u in targets}
                            for i, future in enumerate(as_completed(futures)):
                                url = futures[future]
                                try: results_cache[url] = future.result()[1]
                                except: results_cache[url] = "Error"
                                if i % 2 == 0: p_bar.progress((i + 1) / len(targets))
                        st.session_state.img_real_dim_cache.update(results_cache)
                        st.rerun()

            with col_vis:
                if st.button("3️⃣ Check Visual Dims (Playwright)"):
                    unique_pages = img_df['source_url'].unique().tolist()
                    if not HAS_PLAYWRIGHT: st.error("❌ Playwright not installed.")
                    elif not unique_pages: st.warning("No pages to scan.")
                    else:
                        p_bar = st.progress(0)
                        s_text = st.empty()
                        def update_prog(i, total, url):
                            p_bar.progress((i+1)/total)
                            s_text.text(f"Rendering {i+1}/{total}: {url}")
                        
                        scan_results, img_count = measure_rendered_images(unique_pages, update_prog)
                        if isinstance(scan_results, dict) and scan_results:
                            st.session_state.img_rendered_cache.update(scan_results)
                            st.success(f"✅ Scanned {len(unique_pages)} pages!")
                            time.sleep(1)
                            st.rerun()

            # --- 4. DISPLAY DATAFRAME ---
            st.markdown("---")
            
            def analyze_image_status(row):
                real = row['real_dimensions']
                html = row['html_dimensions']
                vis_d = row['rendered_desktop']
                
                status = []
                if html == 'Missing in HTML': status.append("⚠️ Missing HTML Attrs")
                
                if 'x' in str(real) and 'x' in str(vis_d) and real != 'Not Checked' and vis_d != 'Not Scanned':
                    try:
                        rw, rh = map(int, real.split('x'))
                        vw, vh = map(int, vis_d.split('x'))
                        if vw > 0 and rw < vw: status.append("⚠️ Pixelated (Real < Visible)")
                        if vw > 0 and rw > (vw * 3): status.append("⚠️ Too Big (Real > 3x Visible)")
                    except: pass
                    
                if not status: return "✅ Good"
                return " | ".join(status)

            if not img_df.empty:
                img_df['Analysis'] = img_df.apply(analyze_image_status, axis=1)

            st.dataframe(
                img_df, 
                use_container_width=True, 
                column_config={
                    "image_url": st.column_config.LinkColumn("Image Link"),
                    "source_url": st.column_config.LinkColumn("Found On Page"),
                    "size_kb": st.column_config.NumberColumn("KB", format="%.2f"),
                }
            )
            
            csv_img = img_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Image Report", csv_img, "images_report.csv", "text/csv")

            # --- 5. OPTIMIZATION TOOL ---
            st.markdown("---")
            st.subheader("📉 Optimize & Resize Images")
            
            if not HAS_PIL:
                st.error("❌ 'Pillow' library missing. Run `pip install Pillow`")
            else:
                st.info("Resize images to match their rendered size (Step 1) and then compress them (Step 2).")
                
                c1, c2, c3, c4 = st.columns(4)
                min_kb = c1.number_input("Filter Min KB:", 0, 10000, 100)
                reduc_pct = c2.slider("Quality %", 10, 90, 50, help="Lower = Smaller File")
                target_fmt_ui = c3.selectbox("Format", ["WebP", "JPEG", "PNG", "Original"])
                
                resize_mode = c4.selectbox("Resize To:", ["Original Size Only (No Resize)", "Desktop Rendered Size", "Mobile Rendered Size", "Both Desktop & Mobile"])

                if st.button("✨ Optimize Images"):
                    out_dir = "optimized_images"
                    if not os.path.exists(out_dir): os.makedirs(out_dir)

                    # Filter candidates
                    candidates = img_df[img_df['size_kb'] >= min_kb].drop_duplicates(subset=['image_url'])
                    
                    if candidates.empty:
                        st.warning("No images found matching your size filter.")
                    else:
                        progress = st.progress(0)
                        status = st.empty()
                        report_data = []
                        
                        target_urls = candidates['image_url'].tolist()
                        
                        # Process Single Image Variant
                        def process_variant(img_obj, url, variant_label, target_w, target_h, original_kb, original_dims_str, old_fmt):
                            try:
                                # 1. Resize if dimensions provided
                                if target_w and target_h:
                                    img_obj = img_obj.resize((target_w, target_h), Image.Resampling.LANCZOS)
                                
                                new_dims_str = f"{img_obj.width}x{img_obj.height}"
                                
                                # 2. Format & Compress
                                if target_fmt_ui == "Original": fmt = old_fmt
                                elif target_fmt_ui == "WebP": fmt = "WEBP"
                                elif target_fmt_ui == "JPEG": fmt = "JPEG"
                                elif target_fmt_ui == "PNG": fmt = "PNG"
                                else: fmt = old_fmt

                                if img_obj.mode in ("RGBA", "P") and fmt in ["JPEG"]:
                                    img_obj = img_obj.convert("RGB")
                                
                                buf = io.BytesIO()
                                save_args = {'format': fmt, 'optimize': True}
                                if fmt in ['JPEG', 'WEBP']: save_args['quality'] = reduc_pct
                                
                                img_obj.save(buf, **save_args)
                                new_data = buf.getvalue()
                                new_size_kb = len(new_data) / 1024

                                # 3. Save
                                base_name = url.split('/')[-1].split('?')[0].split('.')[0]
                                if not base_name: base_name = f"img_{uuid.uuid4().hex[:6]}"
                                base_name = "".join([c for c in base_name if c.isalnum() or c in '_-'])
                                
                                suffix = f"_{variant_label.lower()}" if variant_label != "Original" else ""
                                filename = f"{base_name}{suffix}.{fmt.lower()}"
                                local_path = os.path.abspath(os.path.join(out_dir, filename))
                                
                                with open(local_path, "wb") as f: f.write(new_data)
                                
                                return {
                                    "Original URL": url,
                                    "Variant": variant_label,
                                    "Old Size KB": round(original_kb, 2),
                                    "New Size KB": round(new_size_kb, 2),
                                    "Before Dimension": original_dims_str,
                                    "New Dimension": new_dims_str,
                                    "Old Format": old_fmt,
                                    "New Format": fmt,
                                    "Path": local_path
                                }
                            except Exception as e:
                                return None

                        # Main Processing Loop
                        def process_image_row(row_tuple):
                            url = row_tuple.image_url
                            
                            # Get Rendered Data from DF row
                            desk_render = row_tuple.rendered_desktop
                            mob_render = row_tuple.rendered_mobile
                            
                            try:
                                r = requests.get(url, timeout=10, headers={'User-Agent': 'Mozilla/5.0'}, verify=False)
                                if r.status_code != 200: return []
                                
                                # Capture Original Data
                                original_kb = len(r.content) / 1024
                                img_org = Image.open(io.BytesIO(r.content))
                                original_dims_str = f"{img_org.width}x{img_org.height}"
                                old_fmt = img_org.format if img_org.format else 'JPEG'

                                results = []
                                tasks = []
                                
                                # Define Tasks based on Selection
                                if resize_mode == "Original Size Only (No Resize)":
                                    tasks.append((None, None, "Original"))
                                    
                                elif resize_mode == "Desktop Rendered Size":
                                    if desk_render and 'x' in desk_render and desk_render != 'Not Scanned':
                                        dw, dh = map(int, desk_render.split('x'))
                                        tasks.append((dw, dh, "Desktop"))
                                    else:
                                        tasks.append((None, None, "Skipped (Missing Data)"))
                                        
                                elif resize_mode == "Mobile Rendered Size":
                                    if mob_render and 'x' in mob_render and mob_render != 'Not Scanned':
                                        mw, mh = map(int, mob_render.split('x'))
                                        tasks.append((mw, mh, "Mobile"))
                                    else:
                                        tasks.append((None, None, "Skipped (Missing Data)"))

                                elif resize_mode == "Both Desktop & Mobile":
                                    if desk_render and 'x' in desk_render and desk_render != 'Not Scanned':
                                        dw, dh = map(int, desk_render.split('x'))
                                        tasks.append((dw, dh, "Desktop"))
                                    else:
                                        tasks.append((None, None, "Skipped (Missing Data)"))
                                    
                                    if mob_render and 'x' in mob_render and mob_render != 'Not Scanned':
                                        mw, mh = map(int, mob_render.split('x'))
                                        tasks.append((mw, mh, "Mobile"))

                                # Execute Tasks
                                for w, h, label in tasks:
                                    # Always pass a copy so the original stays clean for the next loop
                                    res = process_variant(img_org.copy(), url, label, w, h, original_kb, original_dims_str, old_fmt)
                                    if res: results.append(res)
                                    
                                return results

                            except Exception: return []

                        with ThreadPoolExecutor(max_workers=5) as exe:
                            futures = [exe.submit(process_image_row, row) for row in candidates.itertuples()]
                            for i, f in enumerate(as_completed(futures)):
                                res_list = f.result()
                                if res_list: report_data.extend(res_list)
                                progress.progress((i + 1) / len(candidates))
                                status.text(f"Processing: {i+1}/{len(candidates)}")

                        if report_data:
                            st.success(f"✅ Generated {len(report_data)} optimized images!")
                            rep_df = pd.DataFrame(report_data)
                            st.dataframe(rep_df, use_container_width=True)
                            
                            # CSV Export
                            csv_rep = rep_df.to_csv(index=False).encode('utf-8')
                            st.download_button("📥 Download Full Report", csv_rep, "conversion_report.csv", "text/csv")
                        else:
                            st.warning("No images processed successfully.")
        else:
            st.info("No images found.")

    with tab_meta_titles:
        st.subheader("📝 Meta Tags & Titles Analysis")
        # Combined DataFrame View
        meta_view = df[['url', 'title', 'title_length', 'meta_description', 'meta_desc_length', 'h1_tags']].copy()
        st.dataframe(meta_view, use_container_width=True)
        csv_meta = meta_view.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download All Meta Data", csv_meta, "meta_titles.csv", "text/csv")

        st.markdown("---")
        with st.expander("✨ AI Content Generator (Titles & Meta)", expanded=False):
            st.info("Generate missing or improved tags using AI.")
            
            c1, c2 = st.columns(2)
            provider = c1.selectbox("Provider", ["Gemini", "OpenAI Compatible (Groq/Ollama/OpenAI)"])
            api_key_gen = c2.text_input("API Key (Leave empty for Ollama)", type="password")
            
            c3, c4 = st.columns(2)
            model_name = c3.text_input("Model Name", value="gemini-1.5-flash" if provider=="Gemini" else "lama-3.1-8b-instant")
            endpoint = c4.text_input("Endpoint URL (OpenAI/Ollama Only)", value="https://api.groq.com/openai/v1/chat/completions")
            
            action_type = st.radio("I want to generate:", ["Titles Only", "Meta Descriptions Only"], horizontal=True)
            filter_mode = st.radio("Generate for:", ["Only Missing Items (Empty)", "Regenerate All"], horizontal=True)
            
            if st.button("🚀 Generate Content"):
                # Filter Logic
                if action_type == "Titles Only":
                    if filter_mode == "Only Missing Items (Empty)":
                        targets = meta_view[meta_view['title_length'] == 0].copy()
                    else:
                        targets = meta_view.copy()
                else: # Meta Desc
                    if filter_mode == "Only Missing Items (Empty)":
                        targets = meta_view[meta_view['meta_desc_length'] == 0].copy()
                    else:
                        targets = meta_view.copy()
                
                if targets.empty:
                    st.warning("No pages match your criteria.")
                else:
                    st.write(f"Generating for {len(targets)} pages...")
                    progress_gen = st.progress(0)
                    results_gen = []
                    
                    def process_gen_row(row):
                        content_snippet = str(row.get('scope_content', df[df['url'] == row['url']]['scope_content'].values[0]))[:800]
                        if action_type == "Titles Only":
                            context = f"H1: {row.get('h1_tags', '')}\nContent: {content_snippet}"
                            prompt = f"Write a concise, high-CTR SEO Title (under 60 chars) for this page content:\n\n{context}"
                            col_name = "New AI Title"
                            old_val = row['title']
                        else:
                            context = f"Title: {row.get('title', '')}\nContent: {content_snippet}"
                            prompt = f"Write a persuasive SEO Meta Description (under 160 chars) for this page:\n\n{context}"
                            col_name = "New AI Description"
                            old_val = row['meta_description']
                        
                        generated = generate_ai_meta(provider, api_key_gen, model_name, endpoint, prompt)
                        return {"URL": row['url'], "Old Value": old_val, col_name: generated}

                    with ThreadPoolExecutor(max_workers=5) as executor:
                        futures = [executor.submit(process_gen_row, row) for _, row in targets.iterrows()]
                        for i, f in enumerate(as_completed(futures)):
                            res = f.result()
                            results_gen.append(res)
                            progress_gen.progress((i + 1) / len(targets))
                    
                    res_df = pd.DataFrame(results_gen)
                    st.success("✅ Generation Complete!")
                    st.dataframe(res_df, use_container_width=True)
                    csv_gen = res_df.to_csv(index=False).encode('utf-8')
                    st.download_button("📥 Download Generated Data", csv_gen, "ai_generated_tags.csv", "text/csv")

    with tab_headers:
        st.subheader("🏗️ Header Architecture & Counts")
        
        if 'header_structure' in df.columns:
            # 1. Prepare Data
            struct_df = df[['url', 'h1_count', 'h2_count', 'h3_count', 'h4_count', 'h1_tags', 'header_structure']].copy()
            
            analyzed_data = []
            problematic_urls = []
            bad_h1_count = 0
            broken_struct_count = 0
            
            # 2. Run Analysis Loop
            def get_struct_status(row):
                struct = row['header_structure']
                if isinstance(struct, str):
                    try: struct = json.loads(struct)
                    except: struct = []
                
                issues, h1_c = analyze_heading_structure(struct)
                
                # Logic for counters
                has_h1_issue = h1_c != 1
                has_hierarchy_issue = any("Skipped" in i for i in issues)
                
                if has_h1_issue: 
                    # We can't modify external variable easily in apply, so we handle counting differently or just use this for the DF
                    pass 
                
                status_label = "✅ Perfect"
                if has_h1_issue and has_hierarchy_issue: status_label = "❌ H1 & Hierarchy Errors"
                elif has_h1_issue: status_label = "❌ Bad H1 Count"
                elif has_hierarchy_issue: status_label = "⚠️ Skipped Levels"
                
                # Store for Visual Inspector
                analyzed_data.append({
                    'url': row['url'],
                    'structure': struct,
                    'issues': issues,
                    'h1_count': h1_c,
                    'status': status_label
                })
                
                if has_h1_issue or has_hierarchy_issue:
                    problematic_urls.append({
                        'URL': row['url'],
                        'H1 Count': h1_c,
                        'Hierarchy Issues': " | ".join(issues)
                    })
                    
                return status_label

            # Apply Analysis
            struct_df['Hierarchy Status'] = struct_df.apply(get_struct_status, axis=1)
            
            # Calculate Counts from the processed data
            bad_h1_count = len(struct_df[struct_df['h1_count'] != 1])
            broken_struct_count = len(struct_df[struct_df['Hierarchy Status'].str.contains("Skipped")])

            # 3. Top Metrics
            m1, m2, m3, m4 = st.columns(4)
            m1.metric("Total Pages", len(df))
            m2.metric("❌ Bad H1 Usage", bad_h1_count, help="Pages with 0 or >1 H1 tags")
            m3.metric("⚠️ Broken Levels", broken_struct_count, help="Pages skipping levels (e.g. H2->H4)")
            m4.metric("✅ Perfect Structure", len(df) - len(problematic_urls))

            st.divider()

            # 4. Main Data Table (Merged View)
            st.write("### 📊 Overview Table")
            
            # Reorder columns for readability
            cols_to_show = ['Hierarchy Status', 'url', 'h1_count', 'h2_count', 'h3_count', 'h1_tags']
            st.dataframe(
                struct_df[cols_to_show],
                use_container_width=True,
                column_config={
                    "url": st.column_config.LinkColumn("Page URL"),
                    "h1_tags": st.column_config.TextColumn("H1 Text", width="large"),
                    "Hierarchy Status": st.column_config.TextColumn("Status", width="medium"),
                }
            )
            
            csv = struct_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Header Report", csv, "header_analysis.csv", "text/csv")

            st.divider()

            # 5. Visual Hierarchy Inspector (The "Deep Dive")
            c_insp, c_tree = st.columns([1, 2])
            
            with c_insp:
                st.write("### 🔍 Visual Inspector")
                st.info("Select a page to visualize its Heading Tree (DOM).")
                
                filter_mode = st.radio("Filter List:", ["All Pages", "Only Pages with Issues"], horizontal=True)
                
                if filter_mode == "Only Pages with Issues":
                    options = [d['URL'] for d in problematic_urls]
                else:
                    options = [d['url'] for d in analyzed_data]
                
                if not options:
                    st.warning("No pages match this filter.")
                    selected_page = None
                else:
                    selected_page = st.selectbox("Select Page:", options, key="merged_struct_select")

            with c_tree:
                if selected_page:
                    page_data = next((item for item in analyzed_data if item['url'] == selected_page), None)
                    
                    if page_data:
                        st.markdown(f"**Analysis for:** `{selected_page}`")
                        
                        # Show Issues Badge
                        if page_data['issues']:
                            for issue in page_data['issues']:
                                if "❌" in issue: st.error(issue)
                                else: st.warning(issue)
                        else:
                            st.success("✅ Structure is perfectly logical.")

                        # Render Tree
                        st.markdown("#### 🌳 Heading Tree")
                        st.markdown("""
                        <style>
                        .header-node { padding: 3px 8px; border-left: 3px solid #ddd; margin-bottom: 3px; font-family: monospace; }
                        .h1-node { border-left-color: #ff4b4b; background-color: #ff4b4b1a; font-weight: bold; }
                        .h2-node { border-left-color: #ffbd45; background-color: #ffbd451a; }
                        .h3-node { border-left-color: #92c5de; }
                        .h4-node { border-left-color: #e0e0e0; color: #666; }
                        </style>
                        """, unsafe_allow_html=True)

                        if not page_data['structure']:
                            st.info("No headers found on this page.")
                        
                        for h in page_data['structure']:
                            lvl = h['level']
                            indent = (lvl - 1) * 20
                            # CSS Class based on level
                            css_class = "header-node"
                            if lvl == 1: css_class += " h1-node"
                            elif lvl == 2: css_class += " h2-node"
                            elif lvl == 3: css_class += " h3-node"
                            elif lvl >= 4: css_class += " h4-node"
                            
                            st.markdown(
                                f"<div class='{css_class}' style='margin-left: {indent}px;'>"
                                f"<span>{h['tag'].upper()}</span>: {h['text']}"
                                f"</div>", 
                                unsafe_allow_html=True
                            )
        else:
            st.warning("Header structure data not available. Please re-crawl the site.")

    with tab7:
        st.subheader("🔄 Redirects")
        redirect_df = df[df['redirect_count'] > 0].copy()
        if not redirect_df.empty:
            st.dataframe(redirect_df[['original_url', 'final_url', 'status_code']], use_container_width=True)
            csv = redirect_df[['original_url', 'final_url', 'status_code']].to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Redirects", csv, "redirects.csv", "text/csv")
        else:
            st.success("No redirects found.")

    with tab8:
        st.subheader("📊 Status Codes")
        st.dataframe(df[['url', 'status_code', 'indexability']], use_container_width=True)
        csv = df[['url', 'status_code']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Status", csv, "status_codes.csv", "text/csv")
        
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

    with tab10:
        st.subheader("📱 Social Tags")
        st.dataframe(df[['url', 'og_title', 'twitter_title']], use_container_width=True)
        csv = df[['url', 'og_title', 'twitter_title']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Social", csv, "social_tags.csv", "text/csv")

    with tab11:
        st.subheader("🚀 Performance Stats")
        st.dataframe(df[['url', 'response_time', 'word_count', 'content_length']], use_container_width=True)
        csv = df[['url', 'response_time']].to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Performance", csv, "performance.csv", "text/csv")

    with tab13:
        st.subheader("👻 Orphan Pages")
        if orphans:
            orphan_df = pd.DataFrame(orphans, columns=['Orphan URL'])
            st.dataframe(orphan_df, use_container_width=True)
            csv = orphan_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Orphans", csv, "orphans.csv", "text/csv")
        else:
            st.success("No orphans found (or no sitemap provided).")

    with tab14:
        st.subheader("⛏️ Custom Extracted Data")
        if custom_selector:
            st.info(f"Results for Selector: `{custom_selector}`")
            st.dataframe(df[['url', 'custom_extraction']], use_container_width=True)
            csv = df[['url', 'custom_extraction']].to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Custom Data", csv, "custom_data.csv", "text/csv")
        else:
            st.info("Enter a CSS Selector in the sidebar to extract custom data.")

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

    with tab_search:
        st.subheader("🔍 Custom Search Results")
        s_conf = st.session_state.get('search_config', None)
        if 'custom_search_count' not in df.columns:
            st.info("Please configure Custom Search in the Sidebar and run a new crawl.")
        elif s_conf:
            st.info(f"Results for search: **'{s_conf['query']}'** ({s_conf['mode']}) in **{s_conf['scope']}**")
            found_df = df[df['custom_search_count'] > 0][['url', 'custom_search_count']].copy()
            st.dataframe(found_df, use_container_width=True)
        else:
            st.warning("No search was configured.")

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
    
    with tab_cannibal:
        st.subheader("👯 Content Similarity & Pruning")
        st.markdown("""
        **Two-Step Pruning Strategy:**
        1. **Duplicates (High Match):** Pages that are copies. Action: *Delete or 301 Redirect.*
        2. **Cannibalization (Medium Match):** Different pages fighting for the same topic. Action: *Merge content.*
        """)
        
        if not HAS_SKLEARN:
            st.error("❌ 'scikit-learn' is not installed. Please run: `pip install scikit-learn`")
        else:
            col1, col2 = st.columns(2)
            
            # --- RESTORED SLIDERS ---
            merge_thresh = col1.slider("Merge Threshold % (Topic Overlap)", 30, 90, 60, help="Finds pages that talk about similar things.")
            dupe_thresh = col2.slider("Duplicate Threshold % (Exact Copies)", 80, 100, 90, help="Finds pages that are almost identical.")
            
            if st.button("🔍 Analyze Content Similarity"):
                with st.spinner("Comparing semantic fingerprints (Title + H1 + Body)..."):
                    if 'scope_content' not in df.columns:
                        st.error("Please re-crawl the website to capture content data.")
                    else:
                        cannibal_df = analyze_content_cannibalization(df, merge_threshold=merge_thresh/100, duplicate_threshold=dupe_thresh/100)
                        st.session_state.cannibal_data = cannibal_df
            
            # --- DISPLAY RESULTS ---
            if 'cannibal_data' in st.session_state:
                data = st.session_state.cannibal_data
                
                if data.empty:
                    st.success("✅ No similarity found above your thresholds.")
                else:
                    # SECTION 1: DUPLICATES (TO REMOVE)
                    duplicates = data[data['Recommendation'].str.contains("Remove")]
                    st.write("### 🚨 1. Duplicates (High Risk - Remove/Redirect)")
                    if not duplicates.empty:
                        st.error(f"Found {len(duplicates)} pages that look like copies.")
                        st.dataframe(
                            duplicates, 
                            use_container_width=True,
                            column_config={
                                "Similarity": st.column_config.ProgressColumn("Match %", format="%.1f%%", min_value=0, max_value=100),
                                "Page A": st.column_config.LinkColumn("Page A"),
                                "Page B": st.column_config.LinkColumn("Page B"),
                            }
                        )
                    else:
                        st.info("No exact duplicates found.")

                    st.divider()

                    # SECTION 2: MERGERS (TO COMBINE)
                    mergers = data[data['Recommendation'].str.contains("Merge")]
                    st.write("### 🤝 2. Merge Opportunities (Keyword Cannibalization)")
                    if not mergers.empty:
                        st.warning(f"Found {len(mergers)} pages covering similar topics.")
                        st.caption("These pages are likely competing for the same keywords. Pick the strongest one and merge the others into it.")
                        st.dataframe(
                            mergers, 
                            use_container_width=True,
                            column_config={
                                "Similarity": st.column_config.ProgressColumn("Match %", format="%.1f%%", min_value=0, max_value=100),
                                "Page A": st.column_config.LinkColumn("Page A"),
                                "Page B": st.column_config.LinkColumn("Page B"),
                            }
                        )
                    else:
                        st.info("No merge opportunities found with current settings.")
                    
                    st.divider()
                    
                    # Filter for Mergers
                    mergers = data[data['Recommendation'].str.contains("Merge")]
                    if not mergers.empty:
                        st.warning(f"🤝 Found {len(mergers)} pages covering similar topics (Keyword Cannibalization).")
                        st.dataframe(
                            mergers, 
                            use_container_width=True,
                            column_config={
                                "Similarity Score": st.column_config.ProgressColumn("Similarity", format="%.1f%%", min_value=0, max_value=100),
                                "Page A": st.column_config.LinkColumn("Keep This?"),
                                "Page B": st.column_config.LinkColumn("Redirect This?"),
                            }
                        )

    with tab_gsc:
        st.subheader("📈 Google Search Console Analysis")
        
        if not HAS_GSC:
            st.error("Missing libraries. Run: `pip install google-api-python-client google-auth`")
        elif not st.session_state.gsc_service or not gsc_property:
            st.info("👈 Please upload your JSON Key and select a property in the sidebar.")
        else:
            st.write("### 1. Performance Metrics")
            
            valid_dates = False
            start_d, end_d = None, None
            
            if 'date_range' in locals() and isinstance(date_range, tuple) and len(date_range) == 2:
                start_d, end_d = date_range
                st.caption(f"Fetching data from: **{start_d}** to **{end_d}**")
                valid_dates = True
            elif 'date_range' not in locals():
                 st.warning("⚠️ Date picker loading...")
            else:
                st.warning("⚠️ Please select both a Start Date and an End Date in the sidebar.")

            if st.button("🔄 Fetch Performance (Clicks, Imp, CTR, Pos)", disabled=not valid_dates):
                with st.spinner("Fetching performance data..."):
                    gsc_data = fetch_gsc_data(st.session_state.gsc_service, gsc_property, start_d, end_d)
                    
                    if not gsc_data.empty:
                        st.success(f"Fetched data for {len(gsc_data)} URLs!")
                        
                        if 'GSC CTR' in gsc_data.columns:
                            gsc_data['GSC CTR'] = (gsc_data['GSC CTR'] * 100).round(2).astype(str) + '%'
                        if 'GSC Position' in gsc_data.columns:
                            gsc_data['GSC Position'] = gsc_data['GSC Position'].round(1)

                        if df is not None and not df.empty:
                            df['url'] = df['url'].astype(str)
                            gsc_data['url'] = gsc_data['url'].astype(str)
                            
                            merged_gsc = pd.merge(df, gsc_data, on='url', how='left')
                            
                            zero_clicks = merged_gsc[merged_gsc['GSC Clicks'].fillna(0) == 0]
                            st.metric("Pages in List with 0 Clicks", len(zero_clicks))
                            
                            display_df = merged_gsc.copy()
                            complex_cols = ['schema_dump', 'internal_links', 'external_links', 
                                          'images', 'redirect_chain', 'header_structure', 'custom_extraction']
                            for col in complex_cols:
                                if col in display_df.columns:
                                    display_df[col] = display_df[col].astype(str)
                            
                            target_cols = ['url', 'GSC Clicks', 'GSC Impressions', 'GSC CTR', 'GSC Position']
                            final_cols = [c for c in target_cols if c in display_df.columns]
                            
                            st.dataframe(display_df[final_cols], use_container_width=True)
                            st.session_state.gsc_merged_data = merged_gsc
                        else:
                            st.dataframe(gsc_data, use_container_width=True)
                            st.session_state.gsc_merged_data = gsc_data
                    else:
                        st.warning("No data found in GSC for this period.")

            st.divider()

            st.write("### 2. Indexing & Canonical Inspection")
            st.info("ℹ️ Checks the live Google Index status. Use 'List Mode' crawl to define your URLs first.")
            
            available_urls = []
            if df is not None and not df.empty:
                available_urls = df['url'].tolist()
            elif 'gsc_merged_data' in st.session_state and not st.session_state.gsc_merged_data.empty:
                available_urls = st.session_state.gsc_merged_data['url'].tolist()
            
            if available_urls:
                st.write(f"**Ready to inspect {len(available_urls)} URLs**")
                
                col_i1, col_i2 = st.columns(2)
                do_inspect = False
                urls_to_run = []
                
                with col_i1:
                    specific_url = st.text_input("Inspect Single URL")
                    if st.button("🔎 Inspect One"):
                        if specific_url:
                            urls_to_run = [specific_url]
                            do_inspect = True
                        else:
                            st.warning("Enter a URL")

                with col_i2:
                    st.write(f"Batch Inspect ({len(available_urls)} URLs)")
                    if st.button(f"🚀 Inspect All {len(available_urls)} URLs"):
                        urls_to_run = available_urls
                        do_inspect = True
                
                if do_inspect:
                    with st.status("Inspecting URLs... (This can take a while)") as status:
                        insp_df = inspect_url_indexing(st.session_state.gsc_service, gsc_property, urls_to_run)
                        status.update(label="Inspection Complete!", state="complete")
                    
                    if not insp_df.empty:
                        if 'Google Canonical' in insp_df.columns and 'User Canonical' in insp_df.columns:
                            mismatches = insp_df[
                                (insp_df['Google Canonical'] != 'N/A') & 
                                (insp_df['Google Canonical'] != insp_df['User Canonical'])
                            ]
                            if not mismatches.empty:
                                st.error(f"⚠️ Found {len(mismatches)} Canonical Mismatches (Google chose differently)")
                                st.dataframe(mismatches, use_container_width=True)
                            else:
                                st.success("✅ Google respects all your canonical tags.")

                        st.dataframe(insp_df, use_container_width=True)
                        csv_insp = insp_df.to_csv(index=False).encode('utf-8')
                        st.download_button("📥 Download Inspection Report", csv_insp, "indexing_report.csv", "text/csv")
            else:
                st.warning("⚠️ No URLs found to inspect. Please run a Crawl (List Mode) or Fetch Performance Data first.")

    with tab_audit:
        st.subheader("📅 AI Content Relevance & Freshness Auditor")
        st.info("Identify 'Stale' or 'Zombie' pages that need to be updated or removed based on current real-world relevance.")
        
        c1, c2 = st.columns(2)
        with c1:
            aud_provider = st.selectbox("AI Provider", ["Gemini", "OpenAI Compatible (Groq/Ollama)"], key="aud_p")
            aud_key = st.text_input("API Key (or Ollama URL if empty)", type="password", key="aud_k")
        with c2:
            aud_model = st.text_input("Model", value="gemini-1.5-flash" if aud_provider=="Gemini" else "llama-3.3-70b-versatile", key="aud_m")
            aud_url = st.text_input("Endpoint (if needed)", value="https://api.groq.com/openai/v1/chat/completions", key="aud_u")

        audit_scope = st.radio("Audit Scope:", ["Top 10 High Traffic (GSC Needed)", "Custom List", "All Indexable Pages"], horizontal=True)

        if st.button("🚀 Start Content Audit"):
            targets = []
            if audit_scope == "All Indexable Pages":
                targets = df[df['indexability'] == 'Indexable'].to_dict('records')
            elif audit_scope == "Top 10 High Traffic (GSC Needed)":
                if 'gsc_merged_data' in st.session_state and not st.session_state.gsc_merged_data.empty:
                    targets = st.session_state.gsc_merged_data.sort_values(by='GSC Clicks', ascending=False).head(10).to_dict('records')
                else:
                    st.error("Please fetch GSC Performance data first.")
            else: 
                 st.info("Custom List logic would go here. Defaulting to first 5 indexable pages.")
                 targets = df[df['indexability'] == 'Indexable'].head(5).to_dict('records')
            
            if targets:
                progress_aud = st.progress(0)
                audit_results = []
                
                with ThreadPoolExecutor(max_workers=3) as executor:
                    futures = [executor.submit(analyze_content_freshness, t['url'], t.get('title', ''), t.get('scope_content', ''), aud_provider, aud_key, aud_model, aud_url) for t in targets]
                    for i, f in enumerate(as_completed(futures)):
                        audit_results.append(f.result())
                        progress_aud.progress((i + 1) / len(targets))
                
                aud_res_df = pd.DataFrame(audit_results)
                st.session_state.content_audit_data = aud_res_df
                st.success("✅ Audit Complete!")

        if 'content_audit_data' in st.session_state and not st.session_state.content_audit_data.empty:
            res = st.session_state.content_audit_data
            
            m1, m2, m3 = st.columns(3)
            m1.metric("KEEP", len(res[res['Decision'] == 'KEEP']))
            m2.metric("UPDATE", len(res[res['Decision'] == 'UPDATE']), delta_color="off")
            m3.metric("REMOVE", len(res[res['Decision'] == 'REMOVE']), delta="-"+str(len(res[res['Decision'] == 'REMOVE'])))
            
            st.dataframe(res, use_container_width=True, column_config={
                "Decision": st.column_config.SelectboxColumn("Decision", options=["KEEP", "UPDATE", "REMOVE"]),
                "URL": st.column_config.LinkColumn("Page URL")
            })
            
            csv_aud = res.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Audit Report", csv_aud, "content_audit.csv", "text/csv")

       # --- NEW SECTION: GRAMMAR CHECKER (UPDATED) ---
        st.markdown("---")
        st.subheader("📝 Grammar & Spelling Auditor")
        st.info("Checks for spelling and grammar errors. Works for any website.")

        if not HAS_LT:
            st.error("❌ `language_tool_python` is missing. Please run: `pip install language_tool_python`")
        else:
            gram_scope = st.radio("Grammar Scope:", ["Selected Pages Only (Use Filter below)", "All Pages (Slow)"], horizontal=True)
            
            # Allow filtering to test first
            if gram_scope == "Selected Pages Only (Use Filter below)":
                gram_targets = st.multiselect("Select URLs to Check:", df['url'].tolist(), default=df['url'].head(3).tolist())
            else:
                gram_targets = df['url'].tolist()

            if st.button("🔍 Check Grammar & Spelling"):
                if not gram_targets:
                    st.warning("No pages selected.")
                else:
                    progress_gram = st.progress(0)
                    status_gram = st.empty()
                    gram_results = []
                    
                    # 1. Initialize Tool
                    tool = None
                    use_cloud_fallback = False
                    
                    try:
                        status_gram.text("Initializing LanguageTool...")
                        tool = language_tool_python.LanguageTool('en-US') 
                    except Exception:
                        status_gram.text("⚠️ Java missing. Switching to Cloud API...")
                        use_cloud_fallback = True

                    total_g = len(gram_targets)
                    
                    for i, u in enumerate(gram_targets):
                        # Find data row
                        row_data = df[df['url'] == u].iloc[0]
                        
                        # Fields to check
                        check_map = {
                            'Title': row_data.get('title', ''),
                            'H1': row_data.get('h1_tags', ''),
                            'Meta Desc': row_data.get('meta_description', ''),
                            'Content': row_data.get('scope_content', '')[:2500] # Check first 2500 chars
                        }
                        
                        for field, text in check_map.items():
                            if text and len(text) > 5:
                                matches = []
                                
                                # A. Use Library (Local Java)
                                if tool:
                                    try:
                                        lt_matches = tool.check(text)
                                        for m in lt_matches:
                                            matches.append({
                                                'replacements': m.replacements[:3],
                                                'offset': m.offset,
                                                'length': m.errorLength
                                            })
                                    except: pass
                                
                                # B. Use Cloud Fallback (No Java)
                                elif use_cloud_fallback:
                                    matches = check_grammar_cloud(text)
                                    time.sleep(0.3) # Rate limit
                                
                                # Process Matches into Clean Table
                                for m in matches:
                                    # Extract the specific wrong word using offset slicing
                                    start = m['offset']
                                    end = m['offset'] + m['length']
                                    wrong_word = text[start:end]
                                    
                                    # Skip if it extracted nothing or just whitespace
                                    if not wrong_word.strip():
                                        continue

                                    gram_results.append({
                                        'Page URL': u,
                                        'Location': field,
                                        'Wrong Spelling': wrong_word,
                                        'Correct Spelling': ", ".join(m['replacements'])
                                    })
                        
                        progress_gram.progress((i + 1) / total_g)
                        status_gram.text(f"Checking {i+1}/{total_g}: {u}")

                    st.session_state.grammar_audit_data = pd.DataFrame(gram_results)
                    status_gram.success("✅ Grammar Check Complete!")

            # Display Results
            if 'grammar_audit_data' in st.session_state and not st.session_state.grammar_audit_data.empty:
                gdf = st.session_state.grammar_audit_data
                
                st.write(f"**Found {len(gdf)} potential errors.**")
                
                # Simple Clean Table
                st.dataframe(
                    gdf, 
                    use_container_width=True,
                    column_config={
                        "Page URL": st.column_config.LinkColumn("Page"),
                        "Wrong Spelling": st.column_config.TextColumn("Wrong Spelling", width="small"),
                        "Correct Spelling": st.column_config.TextColumn("Correct Spelling", width="medium"),
                    }
                )
                
                csv_gram = gdf.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Spelling Report", csv_gram, "spelling_report.csv", "text/csv")
            elif 'grammar_audit_data' in st.session_state:
                st.info("No spelling errors found in the selected pages.")

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
