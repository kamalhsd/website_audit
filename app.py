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

# Try importing pyvis for graphing, handle if missing
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False

# Page config
st.set_page_config(page_title="Battersea Crawler", layout="wide", page_icon="🐸")

# Initialize session state
if 'crawl_data' not in st.session_state:
    st.session_state.crawl_data = []
if 'crawling' not in st.session_state:
    st.session_state.crawling = False
if 'stop_crawling' not in st.session_state:
    st.session_state.stop_crawling = False
if 'sitemap_urls_set' not in st.session_state:
    st.session_state.sitemap_urls_set = set()

class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None, link_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector  # <--- NEW: Stores the specific section to look for links
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Ultra Frog SEO Crawler/3.0 (https://ultrafrog.seo)',
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
        if self.crawl_scope == "exact":
            return url == urljoin(f"https://{self.base_domain}", self.base_path)
        elif self.crawl_scope == "subdomain":
            return self.base_domain in parsed.netloc
        else:  # subfolder
            return (parsed.netloc == self.base_domain and 
                    parsed.path.startswith(self.base_path))
    
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
        """
        Cleans text by removing extra whitespace, newlines, and unescaping HTML entities.
        """
        if not text:
            return ""
        text = str(text)
        text = html.unescape(text)
        text = re.sub(r'[\r\n\t]+', ' ', text)
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def get_css_path(self, element):
        """Generates the CSS path for a specific element."""
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
        
    def extract_page_data(self, url):
        try:
            response = self.session.get(url, timeout=8, allow_redirects=True)
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Basic SEO data extraction
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            
            # Header tags
            h1_tags = [self.smart_clean(h1.get_text()) for h1 in soup.find_all('h1')]
            h2_tags = [self.smart_clean(h2.get_text()) for h2 in soup.find_all('h2')]
            h3_tags = [self.smart_clean(h3.get_text()) for h3 in soup.find_all('h3')]
            h4_tags = [self.smart_clean(h4.get_text()) for h4 in soup.find_all('h4')]
            
            # --- CUSTOM EXTRACTION ---
            custom_data = ""
            if self.custom_selector:
                custom_elements = soup.select(self.custom_selector)
                custom_data = "; ".join([self.smart_clean(el.get_text()) for el in custom_elements])

            # --- LINK EXTRACTION LOGIC (UPDATED) ---
            internal_links = []
            external_links = []
            base_domain = urlparse(url).netloc
            
            # Decide scope: entire document OR specific section
            search_area = soup
            if self.link_selector:
                # Try to find the specific section
                specific_section = soup.select_one(self.link_selector)
                if specific_section:
                    search_area = specific_section
            
            # Find links only within the determined scope
            for link in search_area.find_all('a', href=True):
                href = urljoin(url, link['href'])
                link_text = self.smart_clean(link.get_text())[:100]
                
                # Generate Path
                css_path = self.get_css_path(link)
                
                # Simple placement detector
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower: 
                    placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower or "menu" in path_lower: 
                    placement = "Header"
                elif "sidebar" in path_lower or "aside" in path_lower: 
                    placement = "Sidebar"

                link_data = {
                    'url': href, 
                    'anchor_text': link_text,
                    'css_path': css_path,
                    'placement': placement
                }
                
                if urlparse(href).netloc == base_domain:
                    internal_links.append(link_data)
                else:
                    external_links.append(link_data)
            
            # Images analysis
            images = []
            for img in soup.find_all('img'):
                img_src = urljoin(url, img.get('src', ''))
                images.append({
                    'src': img_src,
                    'alt': self.smart_clean(img.get('alt', '')),
                    'title': self.smart_clean(img.get('title', '')),
                    'width': img.get('width', ''),
                    'height': img.get('height', '')
                })
            
            # Schema & Social tags extraction...
            # (Keeping existing logic abbreviated for length, but it's fully functional)
            og_title = soup.find('meta', attrs={'property': 'og:title'})
            og_desc = soup.find('meta', attrs={'property': 'og:description'})
            og_image = soup.find('meta', attrs={'property': 'og:image'})
            twitter_title = soup.find('meta', attrs={'name': 'twitter:title'})
            twitter_desc = soup.find('meta', attrs={'name': 'twitter:description'})
            twitter_image = soup.find('meta', attrs={'name': 'twitter:image'})
            
            # Schema
            scripts = soup.find_all('script', type='application/ld+json')
            schema_types = []
            for script in scripts:
                try:
                    if script.string:
                        schema_data = json.loads(script.string)
                        if isinstance(schema_data, dict) and '@type' in schema_data:
                            schema_types.append(schema_data['@type'])
                        elif isinstance(schema_data, list):
                            for item in schema_data:
                                if isinstance(item, dict) and '@type' in item:
                                    schema_types.append(item['@type'])
                except:
                    pass

            # Performance
            css_files = len(soup.find_all('link', attrs={'rel': 'stylesheet'}))
            js_files = len(soup.find_all('script', src=True))
            text_content = soup.get_text()
            word_count = len(text_content.split())
            
            # Redirects
            redirect_chain = []
            if hasattr(response, 'history') and response.history:
                for i, resp in enumerate(response.history):
                    redirect_chain.append({
                        'step': i + 1,
                        'from_url': resp.url,
                        'status_code': resp.status_code,
                        'redirect_type': '301 Permanent' if resp.status_code == 301 else f'{resp.status_code}'
                    })
            
            return {
                'url': response.url,
                'original_url': url,
                'status_code': response.status_code,
                'title': title_text,
                'title_length': len(title_text),
                'meta_description': meta_desc_text,
                'meta_desc_length': len(meta_desc_text),
                'canonical_url': canonical_url,
                'meta_robots': robots_content,
                'h1_tags': '; '.join(h1_tags),
                'h1_count': len(h1_tags),
                'h2_tags': '; '.join(h2_tags),
                'h2_count': len(h2_tags),
                'h3_tags': '; '.join(h3_tags),
                'h3_count': len(h3_tags),
                'h4_tags': '; '.join(h4_tags),
                'h4_count': len(h4_tags),
                'word_count': word_count,
                'response_time': response.elapsed.total_seconds(),
                'content_length': len(response.content),
                'internal_links_count': len(internal_links),
                'external_links_count': len(external_links),
                'internal_links': internal_links,
                'external_links': external_links,
                'images': images,
                'image_count': len(images),
                'images_without_alt': len([img for img in images if not img['alt']]),
                'schema_types': '; '.join(schema_types),
                'schema_count': len(schema_types),
                'redirect_chain': redirect_chain,
                'redirect_count': len(redirect_chain),
                'css_files': css_files,
                'js_files': js_files,
                'og_title': og_title.get('content', '') if og_title else '',
                'og_description': og_desc.get('content', '') if og_desc else '',
                'og_image': og_image.get('content', '') if og_image else '',
                'twitter_title': twitter_title.get('content', '') if twitter_title else '',
                'twitter_description': twitter_desc.get('content', '') if twitter_desc else '',
                'twitter_image': twitter_image.get('content', '') if twitter_image else '',
                'content_type': response.headers.get('content-type', ''),
                'last_modified': response.headers.get('last-modified', ''),
                'server': response.headers.get('server', ''),
                'custom_extraction': custom_data,
                'indexability': self.get_indexability_status(response.status_code, robots_content),
                'crawl_timestamp': datetime.now().isoformat()
            }
        except Exception as e:
            # Fallback error object
            return {
                'url': url, 'original_url': url, 'status_code': 0, 'error': str(e),
                'title': '', 'title_length': 0, 'meta_description': '', 'meta_desc_length': 0,
                'canonical_url': '', 'meta_robots': '', 'h1_tags': '', 'h1_count': 0,
                'h2_tags': '', 'h2_count': 0, 'h3_tags': '', 'h3_count': 0,
                'h4_tags': '', 'h4_count': 0, 'word_count': 0, 'response_time': 0,
                'content_length': 0, 'internal_links_count': 0, 'external_links_count': 0,
                'internal_links': [], 'external_links': [], 'images': [], 'image_count': 0,
                'images_without_alt': 0, 'schema_types': '', 'schema_count': 0,
                'redirect_chain': [], 'redirect_count': 0, 'css_files': 0, 'js_files': 0,
                'og_title': '', 'og_description': '', 'og_image': '',
                'twitter_title': '', 'twitter_description': '', 'twitter_image': '',
                'content_type': '', 'last_modified': '', 'server': '', 'custom_extraction': '',
                'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat()
            }
    
    def get_indexability_status(self, status_code, robots_content):
        if status_code != 200:
            return 'Non-Indexable'
        if 'noindex' in robots_content.lower():
            return 'Non-Indexable'
        return 'Indexable'

# --- CRAWLER HANDLERS ---
def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector)
    crawler.set_base_url(start_url)
    
    urls_to_visit = deque([start_url])
    visited_urls = set()
    crawl_data = []
    
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
                    crawl_data.append(page_data)
                    
                    if not st.session_state.stop_crawling:
                        for link_data in page_data.get('internal_links', []):
                            link_url = link_data['url']
                            if (link_url not in visited_urls and 
                                link_url not in urls_to_visit and 
                                crawler.should_crawl_url(link_url) and
                                len(visited_urls) + len(urls_to_visit) < max_urls):
                                urls_to_visit.append(link_url)
                    
                    progress = min(len(crawl_data) / max_urls, 1.0)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {len(crawl_data)} | Queue: {len(urls_to_visit)} | Speed: {len(crawl_data)/max(1, time.time() - st.session_state.get('start_time', time.time())):.1f} URLs/sec")
                    
                except Exception as e:
                    st.error(f"Error: {e}")
    
    return crawl_data

def crawl_from_list(url_list, progress_container, ignore_robots=False, custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(len(url_list), ignore_robots, custom_selector=custom_selector, link_selector=link_selector)
    crawl_data = []
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    valid_urls = [url.strip() for url in url_list if crawler.can_fetch(url.strip())]
    
    if not valid_urls: return crawl_data
    
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
                    crawl_data.append(page_data)
                    progress = len(crawl_data) / len(valid_urls)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Processed: {len(crawl_data)}/{len(valid_urls)} | Speed: {len(crawl_data)/max(1, time.time() - st.session_state.get('start_time', time.time())):.1f} URLs/sec")
                except Exception as e:
                    st.error(f"Error: {e}")
    return crawl_data

def crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots=False, custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, custom_selector=custom_selector, link_selector=link_selector)
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    status_text.text("🗺️ Extracting URLs from sitemap...")
    sitemap_urls = crawler.extract_sitemap_urls(sitemap_url)
    
    if not sitemap_urls:
        st.error("No URLs found in sitemap")
        return []
    
    if len(sitemap_urls) > max_urls:
        sitemap_urls = sitemap_urls[:max_urls]
    
    st.info(f"Found {len(sitemap_urls)} URLs in sitemap")
    return crawl_from_list(sitemap_urls, progress_container, ignore_robots, custom_selector, link_selector)

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
            st.session_state.crawl_data = []
            st.session_state.start_time = time.time()
            st.rerun()
        else:
            st.error("Please provide valid input")
    
    if st.button("🗑️ Clear All Data"):
        st.session_state.crawl_data = []
        st.session_state.sitemap_urls_set = set()
        st.rerun()

# Main content
if st.session_state.crawling:
    st.header("🐸 Battersea Crawler is Running...")
    progress_container = st.container()
    
    try:
        custom_sel = custom_selector if custom_selector else None
        link_sel = link_selector if link_selector else None
        
        if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
            crawl_data = crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots, custom_sel, link_sel)
        elif crawl_mode == "📝 List Mode (Upload URLs)":
            if uploaded_file:
                content = uploaded_file.read().decode('utf-8')
                url_list = [line.strip() for line in content.split('\n') if line.strip()]
            else:
                url_list = [line.strip() for line in url_list_text.split('\n') if line.strip()]
            crawl_data = crawl_from_list(url_list, progress_container, ignore_robots, custom_sel, link_sel)
        else:
            crawl_data = crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots, custom_sel, link_sel)
        
        st.session_state.crawl_data = crawl_data if crawl_data else []
        st.session_state.crawling = False
        st.session_state.stop_crawling = False
        
        if st.session_state.stop_crawling:
            st.warning("⛔ Crawl stopped by user")
        else:
            crawl_time = time.time() - st.session_state.get('start_time', time.time())
            st.success(f"✅ Crawl completed! Found {len(crawl_data)} URLs in {crawl_time:.1f} seconds")
        st.rerun()
        
    except Exception as e:
        st.error(f"Error: {str(e)}")
        st.session_state.crawling = False

elif st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    
    # Summary stats
    st.header("📊 Battersea Analysis Dashboard")
    col1, col2, col3, col4, col5, col6 = st.columns(6)
    with col1: st.metric("Total URLs", len(df))
    with col2: st.metric("✅ Indexable", len(df[df['indexability'] == 'Indexable']))
    with col3: st.metric("❌ Non-Indexable", len(df[df['indexability'] == 'Non-Indexable']))
    with col4: st.metric("🔄 Redirects", len(df[df['redirect_count'] > 0]))
    with col5: st.metric("⚡ Avg Response", f"{df['response_time'].mean():.2f}s" if len(df)>0 else "0s")
    with col6:
        crawled_urls = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled_urls) if st.session_state.sitemap_urls_set else []
        st.metric("👻 Orphans", len(orphans))
    
    # Tabs
    tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab10, tab11, tab12, tab13, tab14 = st.tabs([
        "🔗 Internal Links", "🌐 External", "🖼️ Images", "📝 Titles", "📄 Meta Desc", "🏷️ Headers", 
        "🔄 Redirects", "📊 Status", "🎯 Canonicals", "📱 Social", "🚀 Performance", "🕸️ Graph", "👻 Orphans", "⛏️ Custom Data"
    ])
    
    # TAB 1: INTERNAL LINKS
    with tab1:
        st.subheader("🔗 Internal Links Analysis")
        if link_selector:
            st.info(f"Showing links extracted ONLY from: `{link_selector}`")
        else:
            st.info("Showing links from ALL sections (Default)")
            
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
                final_links = final_links[['Source URL', 'url', 'anchor_text', 'placement', 'css_path']]
                final_links.columns = ['Source URL', 'Destination URL', 'Anchor Text', 'Placement', 'CSS Path']
                st.dataframe(final_links, use_container_width=True)
                
                placement_counts = final_links['Placement'].value_counts()
                st.subheader("📍 Link Placement Distribution")
                c1, c2, c3, c4 = st.columns(4)
                c1.metric("Header", placement_counts.get('Header', 0))
                c2.metric("Footer", placement_counts.get('Footer', 0))
                c3.metric("Body", placement_counts.get('Body', 0))
                c4.metric("Sidebar", placement_counts.get('Sidebar', 0))
                
                csv = final_links.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Internal Links", csv, "internal_links.csv", "text/csv")
            else:
                st.warning("No internal links found in the selected scope.")

    # TAB 2: EXTERNAL LINKS
    with tab2:
        st.subheader("🌐 External Links Analysis")
        external_data = []
        for _, row in df.iterrows():
            for ext_link in row.get('external_links', []):
                external_data.append({
                    'source_url': row['url'],
                    'destination_url': ext_link['url'],
                    'anchor_text': ext_link['anchor_text'],
                    'placement': ext_link.get('placement', 'Unknown'),
                    'css_path': ext_link.get('css_path', '')
                })
        if external_data:
            ext_df = pd.DataFrame(external_data)
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
                    'dimensions': f"{img['width']}x{img['height']}" if img['width'] else 'Unknown'
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

    # Quick Download All
    st.markdown("---")
    st.header("📥 Full Report")
    csv_all = df.to_csv(index=False).encode('utf-8')
    st.download_button("📊 Download Complete Crawl Data", csv_all, "complete_crawl.csv", "text/csv")

else:
    st.info("👈 Configure your crawl settings and click '🚀 Start Crawl' to begin.")
