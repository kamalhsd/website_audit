import streamlit as st
import requests
from bs4 import BeautifulSoup
import pandas as pd
from urllib.parse import urljoin, urlparse
import time
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from datetime import datetime
import xml.etree.ElementTree as ET
from urllib.robotparser import RobotFileParser
import networkx as nx
import streamlit.components.v1 as components
import html
import re
import csv
import os
import threading

# Try importing pyvis for graphing, handle if missing
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False

# Page config
st.set_page_config(page_title="Battersea Crawler", layout="wide", page_icon="🐸")

# --- GLOBAL CONFIG ---
CSV_FILE = "battersea_data.csv"
write_lock = threading.Lock()

# Initialize session state
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

# --- CSV HELPER FUNCTIONS ---
def init_csv():
    """Initializes the CSV file with headers."""
    headers = [
        'url', 'original_url', 'status_code', 'title', 'title_length', 
        'meta_description', 'meta_desc_length', 'canonical_url', 'meta_robots', 
        'is_noindex_follow', 'is_noindex_nofollow', 'h1_tags', 'h1_count', 
        'h2_tags', 'h2_count', 'h3_tags', 'h3_count', 'h4_tags', 'h4_count', 
        'word_count', 'response_time', 'content_length', 'internal_links_count', 
        'external_links_count', 'internal_links', 'external_links', 'images', 
        'image_count', 'images_without_alt', 'schema_types', 'schema_dump', 
        'schema_count', 'schema_validity', 'schema_errors', 'redirect_chain', 
        'redirect_count', 'css_files', 'js_files', 'og_title', 'og_description', 
        'twitter_title', 'custom_extraction', 'indexability', 'crawl_timestamp', 'error'
    ]
    with open(CSV_FILE, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=headers)
        writer.writeheader()

def save_row_to_csv(data):
    """Writes a single row of data to the CSV file safely."""
    row_data = data.copy()
    # Serialize lists/dicts to JSON for CSV storage
    for key in ['internal_links', 'external_links', 'images', 'redirect_chain', 'schema_dump']:
        if key in row_data:
            row_data[key] = json.dumps(row_data[key])
    
    headers = [
        'url', 'original_url', 'status_code', 'title', 'title_length', 
        'meta_description', 'meta_desc_length', 'canonical_url', 'meta_robots', 
        'is_noindex_follow', 'is_noindex_nofollow', 'h1_tags', 'h1_count', 
        'h2_tags', 'h2_count', 'h3_tags', 'h3_count', 'h4_tags', 'h4_count', 
        'word_count', 'response_time', 'content_length', 'internal_links_count', 
        'external_links_count', 'internal_links', 'external_links', 'images', 
        'image_count', 'images_without_alt', 'schema_types', 'schema_dump', 
        'schema_count', 'schema_validity', 'schema_errors', 'redirect_chain', 
        'redirect_count', 'css_files', 'js_files', 'og_title', 'og_description', 
        'twitter_title', 'custom_extraction', 'indexability', 'crawl_timestamp', 'error'
    ]
    
    with write_lock:
        with open(CSV_FILE, 'a', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=headers)
            writer.writerow({k: v for k, v in row_data.items() if k in headers})

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

    def extract_page_data(self, url):
        try:
            response = self.session.get(url, timeout=10, allow_redirects=True)
            soup = BeautifulSoup(response.content, 'html.parser')
            
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            
            # Indexing Check
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

            # Links
            internal_links = []
            external_links = []
            base_domain_clean = urlparse(url).netloc.replace('www.', '')
            
            search_area = soup
            if self.link_selector:
                specific_section = soup.select_one(self.link_selector)
                if specific_section:
                    search_area = specific_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(url, link['href'])
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
            
            # Images
            images = []
            for img in soup.find_all('img'):
                img_src = urljoin(url, img.get('src', ''))
                file_size = 0 
                # file_size = self.get_file_size(img_src) # Enable if needed
                images.append({
                    'src': img_src,
                    'alt': self.smart_clean(img.get('alt', '')),
                    'title': self.smart_clean(img.get('title', '')),
                    'width': img.get('width', ''),
                    'height': img.get('height', ''),
                    'size_kb': file_size
                })
            
            # Schema
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
                            if isinstance(data, dict) and '@type' in data:
                                schema_types.append(data['@type'])
                            elif isinstance(data, list):
                                for item in data:
                                    if isinstance(item, dict) and '@type' in item:
                                        schema_types.append(item['@type'])
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
                'url': response.url, 'original_url': url, 'status_code': response.status_code,
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
                'schema_types': '; '.join(schema_types), 'schema_dump': schema_dump, 
                'schema_count': len(schema_types), 'schema_validity': schema_validity,
                'schema_errors': '; '.join(schema_errors), 'redirect_chain': redirect_chain,
                'redirect_count': len(redirect_chain), 'css_files': css_files, 'js_files': js_files,
                'og_title': soup.find('meta', attrs={'property': 'og:title'}).get('content', '') if soup.find('meta', attrs={'property': 'og:title'}) else '',
                'og_description': soup.find('meta', attrs={'property': 'og:description'}).get('content', '') if soup.find('meta', attrs={'property': 'og:description'}) else '',
                'twitter_title': soup.find('meta', attrs={'name': 'twitter:title'}).get('content', '') if soup.find('meta', attrs={'name': 'twitter:title'}) else '',
                'custom_extraction': custom_data,
                'indexability': self.get_indexability_status(response.status_code, robots_content),
                'crawl_timestamp': datetime.now().isoformat()
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
                'custom_extraction': '', 'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat()
            }
    
    def get_indexability_status(self, status_code, robots_content):
        if status_code != 200:
            return 'Non-Indexable'
        if 'noindex' in robots_content.lower():
            return 'Non-Indexable'
        return 'Indexable'

# --- PSI HELPER FUNCTION ---
def run_psi_test(url, api_key):
    if not api_key: return {"error": "No API Key Provided"}
    api_url = f"https://www.googleapis.com/pagespeedonline/v5/runPagespeed?url={url}&strategy=mobile&key={api_key}"
    try:
        response = requests.get(api_url)
        data = response.json()
        if "error" in data: return {"error": data["error"]["message"]}
        lh_result = data["lighthouseResult"]
        return {
            "Score": lh_result["categories"]["performance"]["score"] * 100,
            "LCP": lh_result["audits"]["largest-contentful-paint"]["displayValue"],
            "FCP": lh_result["audits"]["first-contentful-paint"]["displayValue"],
            "CLS": lh_result["audits"]["cumulative-layout-shift"]["displayValue"],
            "INP": lh_result["audits"].get("interaction-to-next-paint", {}).get("displayValue", "N/A"),
            "TTI": lh_result["audits"]["interactive"]["displayValue"]
        }
    except Exception as e: return {"error": str(e)}

# --- CRAWLER HANDLERS (HYBRID RAM/CSV) ---
def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, storage="RAM"):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector)
    crawler.set_base_url(start_url)
    
    # Initialize Storage
    if storage == "CSV":
        init_csv()
    else:
        st.session_state.crawl_data = [] # Clear RAM if starting new RAM crawl
    
    urls_to_visit = deque([start_url])
    visited_urls = set()
    st.session_state.total_crawled_count = 0
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    
    with ThreadPoolExecutor(max_workers=10) as executor:
        while urls_to_visit and len(visited_urls) < max_urls:
            if st.session_state.stop_crawling: break
                
            current_batch = []
            batch_size = min(20, len(urls_to_visit), max_urls - len(visited_urls))
            
            for _ in range(batch_size):
                if urls_to_visit and not st.session_state.stop_crawling:
                    url = urls_to_visit.popleft()
                    if url not in visited_urls and crawler.can_fetch(url):
                        current_batch.append(url)
                        visited_urls.add(url)
            
            if not current_batch: break
            
            future_to_url = {executor.submit(crawler.extract_page_data, url): url for url in current_batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: f.cancel()
                    break
                try:
                    page_data = future.result(timeout=12)
                    
                    # --- HYBRID STORAGE LOGIC ---
                    if storage == "CSV":
                        save_row_to_csv(page_data)
                    else:
                        st.session_state.crawl_data.append(page_data)
                    # ----------------------------

                    st.session_state.total_crawled_count += 1
                    
                    if not st.session_state.stop_crawling:
                        for link_data in page_data.get('internal_links', []):
                            link_url = link_data['url']
                            if (link_url not in visited_urls and link_url not in urls_to_visit and 
                                crawler.should_crawl_url(link_url) and len(visited_urls) + len(urls_to_visit) < max_urls):
                                urls_to_visit.append(link_url)
                    
                    progress = min(st.session_state.total_crawled_count / max_urls, 1.0)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {st.session_state.total_crawled_count} | Queue: {len(urls_to_visit)} | Speed: {st.session_state.total_crawled_count/max(1, time.time() - st.session_state.get('start_time', time.time())):.1f} URLs/sec")
                except Exception as e: st.error(f"Error: {e}")
    return True

def crawl_from_list(url_list, progress_container, ignore_robots=False, custom_selector=None, link_selector=None, storage="RAM"):
    crawler = UltraFrogCrawler(len(url_list), ignore_robots, custom_selector=custom_selector, link_selector=link_selector)
    
    if storage == "CSV":
        init_csv()
    else:
        st.session_state.crawl_data = []

    st.session_state.total_crawled_count = 0
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    valid_urls = [url.strip() for url in url_list if crawler.can_fetch(url.strip())]
    
    if not valid_urls: return False
    
    with ThreadPoolExecutor(max_workers=15) as executor:
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
                    
                    if storage == "CSV":
                        save_row_to_csv(page_data)
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
    
    # --- NEW STORAGE SELECTOR ---
    storage_option = st.radio(
        "💾 Storage Mode", 
        ["RAM (Fast, <10k URLs)", "CSV Stream (Unlimited)"], 
        index=0,
        help="Use RAM for speed on small sites. Use CSV for 100k+ URLs to prevent crashing."
    )
    # ----------------------------

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
        
        # Set storage mode logic
        if "CSV" in storage_option:
            st.session_state.storage_mode = "CSV"
            # Clear old RAM data to free memory
            st.session_state.crawl_data = [] 
        else:
            st.session_state.storage_mode = "RAM"
            # Remove old CSV to prevent confusion
            if os.path.exists(CSV_FILE): os.remove(CSV_FILE)

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
        if os.path.exists(CSV_FILE): os.remove(CSV_FILE)
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
# Determine which dataset to load (RAM or CSV)
df = None
has_data = False

if st.session_state.storage_mode == "RAM" and st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    has_data = True
elif st.session_state.storage_mode == "CSV" and os.path.exists(CSV_FILE):
    # For Dashboard performance, only load first 20k rows if in CSV mode
    df = pd.read_csv(CSV_FILE, nrows=20000) 
    
    # Process complex columns for CSV data so they work with tabs
    for col in ['internal_links', 'external_links', 'images', 'redirect_chain', 'schema_dump']:
        if col in df.columns:
            df[col] = df[col].apply(lambda x: json.loads(x) if isinstance(x, str) else [])
    
    has_data = True
    total_in_csv = sum(1 for _ in open(CSV_FILE, 'r', encoding='utf-8')) - 1
    if total_in_csv > 20000:
        st.warning(f"⚠️ Displaying first 20,000 URLs for performance. Download the CSV below for the full dataset ({total_in_csv} URLs).")


if has_data and df is not None:
    # Summary stats
    st.header("📊 Battersea Analysis Dashboard")
    col1, col2, col3, col4, col5, col6 = st.columns(6)
    with col1: st.metric("Total URLs", len(df) if st.session_state.storage_mode == "RAM" else total_in_csv)
    with col2: st.metric("✅ Indexable", len(df[df['indexability'] == 'Indexable']))
    with col3: st.metric("❌ Non-Indexable", len(df[df['indexability'] == 'Non-Indexable']))
    with col4: st.metric("🔄 Redirects", len(df[df['redirect_count'] > 0]))
    with col5: st.metric("⚡ Avg Response", f"{df['response_time'].mean():.2f}s" if len(df)>0 else "0s")
    with col6:
        crawled_urls = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled_urls) if st.session_state.sitemap_urls_set else []
        st.metric("👻 Orphans", len(orphans))
    
    # Tabs
    tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab10, tab11, tab12, tab13, tab14, tab15, tab16 = st.tabs([
        "🔗 Internal Links", "🌐 External", "🖼️ Images", "📝 Titles", "📄 Meta Desc", "🏷️ Headers", 
        "🔄 Redirects", "📊 Status", "🎯 Canonicals", "📱 Social", "🚀 Performance", "🕸️ Graph", "👻 Orphans", "⛏️ Custom Data",
        "⚡ Speed (PSI)", "🏗️ Schema"
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
                
                # Ensure new columns exist
                if 'rel_status' not in final_links.columns: final_links['rel_status'] = 'dofollow'
                if 'target' not in final_links.columns: final_links['target'] = '_self'
                
                final_links = final_links[['Source URL', 'url', 'anchor_text', 'rel_status', 'target', 'placement', 'css_path']]
                final_links.columns = ['Source URL', 'Destination URL', 'Anchor Text', 'Link Type', 'Target', 'Placement', 'CSS Path']
                
                final_links = pd.merge(final_links, status_lookup, on='Destination URL', how='left')
                final_links['Status Code'] = final_links['Status Code'].fillna('Not Crawled').astype(str)

                st.dataframe(final_links, use_container_width=True)
                
                c1, c2, c3 = st.columns(3)
                c1.metric("Nofollow Links", len(final_links[final_links['Link Type'].str.contains('nofollow')]))
                c2.metric("Sponsored Links", len(final_links[final_links['Link Type'].str.contains('sponsored')]))
                c3.metric("New Tab (_blank)", len(final_links[final_links['Target'] == '_blank']))
                
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
            ext_df['Status Code'] = ext_df['Status Code'].fillna('Not Crawled').astype(str)

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
            for img in row.get('images', []):
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

    # TAB 6: HEADERS
    with tab6:
        st.subheader("🏷️ Headers (H1-H4)")
        header_df = df[['url', 'h1_count', 'h1_tags', 'h2_count']].copy()
        st.dataframe(header_df, use_container_width=True)
        csv = header_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Headers", csv, "headers.csv", "text/csv")

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
        st.dataframe(df[['url', 'canonical_url']], use_container_width=True)
        csv = df[['url', 'canonical_url']].to_csv(index=False).encode('utf-8')
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

    # TAB 12: GRAPH
    with tab12:
        st.subheader("🕸️ Visual Graph")
        if HAS_PYVIS:
            G = nx.DiGraph()
            max_nodes = 50
            subset = df.head(max_nodes)
            for _, row in subset.iterrows():
                src = row['url']
                G.add_node(src, title=row['title'][:50], color='#4CAF50', size=20)
                for link in row.get('internal_links', []):
                    dst = link['url']
                    if dst in subset['url'].values:
                        G.add_edge(src, dst, color='#aaaaaa')
            net = Network(height='600px', width='100%', bgcolor='#111111', font_color='white')
            net.from_nx(G)
            try:
                net.save_graph("graph.html")
                with open("graph.html", 'r', encoding='utf-8') as f:
                    components.html(f.read(), height=650)
            except: st.error("Graph error")
        else:
            st.error("Install pyvis to view graph.")

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
            urls_to_test = st.multiselect("Select URLs to Test (Max 5 recommended)", df['url'].head(20).tolist())
            
            if st.button("🏃 Run PageSpeed Test"):
                if not urls_to_test:
                    st.warning("Please select at least one URL.")
                else:
                    progress_psi = st.progress(0)
                    results = []
                    
                    for i, u in enumerate(urls_to_test):
                        res = run_psi_test(u, psi_api_key)
                        res['url'] = u
                        results.append(res)
                        progress_psi.progress((i + 1) / len(urls_to_test))
                    
                    st.session_state.psi_results = results
            
            if st.session_state.psi_results:
                psi_df = pd.DataFrame(st.session_state.psi_results)
                cols = ['url', 'Score', 'LCP', 'FCP', 'CLS', 'INP', 'TTI']
                available_cols = [c for c in cols if c in psi_df.columns]
                st.dataframe(psi_df[available_cols], use_container_width=True)
                
                csv_psi = psi_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download PSI Report", csv_psi, "psi_report.csv", "text/csv")
        else:
            st.warning("⚠️ PSI API Key is missing. Please add it in the sidebar.")

    # TAB 16: SCHEMA VALIDATOR
    with tab16:
        st.subheader("🏗️ Schema Markup Analysis")
        
        # Display Summary Table
        schema_df = df[['url', 'schema_types', 'schema_validity', 'schema_errors']].copy()
        st.dataframe(schema_df, use_container_width=True)
        
        # Detail View
        st.markdown("### 🔍 Schema Detail Viewer")
        selected_url = st.selectbox("Select URL to inspect Schema:", df['url'].tolist())
        
        if selected_url:
            row = df[df['url'] == selected_url].iloc[0]
            st.write(f"**Schema Status:** {row['schema_validity']}")
            if row['schema_errors']:
                st.error(f"Errors: {row['schema_errors']}")
            
            schema_json_str = row.get('schema_dump', '[]')
            try:
                # Handle double encoded JSON if loaded from CSV
                if isinstance(schema_json_str, str):
                    schema_json = json.loads(schema_json_str)
                else:
                    schema_json = schema_json_str
                    
                if schema_json:
                    st.json(schema_json)
                else:
                    st.info("No Schema JSON found on this page.")
            except:
                st.text(str(schema_json_str))

        # Indexing Check
        st.markdown("---")
        st.write("### 🤖 Indexing & Robots Directives")
        
        c1, c2 = st.columns(2)
        with c1:
            noindex_follow_df = df[df['is_noindex_follow'] == True][['url', 'meta_robots']]
            if not noindex_follow_df.empty:
                st.warning(f"⚠️ Found {len(noindex_follow_df)} pages with 'noindex, follow'")
                st.dataframe(noindex_follow_df, use_container_width=True)
            else:
                st.success("✅ No 'noindex, follow' pages.")

        with c2:
            noindex_nofollow_df = df[df['is_noindex_nofollow'] == True][['url', 'meta_robots']]
            if not noindex_nofollow_df.empty:
                st.error(f"⛔ Found {len(noindex_nofollow_df)} pages with 'noindex, nofollow'")
                st.dataframe(noindex_nofollow_df, use_container_width=True)
            else:
                st.success("✅ No 'noindex, nofollow' pages.")

    # Quick Download All
    st.markdown("---")
    st.header("📥 Full Report")
    
    if st.session_state.storage_mode == "CSV" and os.path.exists(CSV_FILE):
        with open(CSV_FILE, "rb") as file:
            st.download_button("📊 Download Complete Crawl Data (CSV)", file, "battersea_full_data.csv", "text/csv")
    else:
        csv_all = df.to_csv(index=False).encode('utf-8')
        st.download_button("📊 Download Complete Crawl Data", csv_all, "complete_crawl.csv", "text/csv")

else:
    st.info("👈 Configure your crawl settings and click '🚀 Start Crawl' to begin.")
