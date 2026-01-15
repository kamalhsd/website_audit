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
import networkx as nx
import streamlit.components.v1 as components
import html
import re
import hashlib

# Try importing pyvis for graphing
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False

# Page config
st.set_page_config(
    page_title="Battersea Pro SEO Crawler", 
    layout="wide", 
    page_icon="🐸",
    initial_sidebar_state="expanded"
)

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

class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", 
                 custom_selector=None, link_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Ultra Frog SEO Crawler/4.0 (https://ultrafrog.seo)',
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
        """Cleans text by removing extra whitespace and unescaping HTML"""
        if not text:
            return ""
        text = str(text)
        text = html.unescape(text)
        text = re.sub(r'[\r\n\t]+', ' ', text)
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def get_css_path(self, element):
        """Generates CSS path for an element"""
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

    def extract_keywords(self, text, top_n=10):
        """Simple keyword extraction"""
        if not text:
            return []
        words = re.findall(r'\b[a-z]{4,}\b', text.lower())
        stop_words = {'this', 'that', 'with', 'from', 'have', 'been', 'will', 
                      'their', 'what', 'about', 'which', 'when', 'make', 'like', 
                      'time', 'just', 'know', 'take', 'them', 'into', 'year', 'your',
                      'good', 'some', 'could', 'them', 'than', 'then', 'more', 'very'}
        filtered = [w for w in words if w not in stop_words]
        counter = Counter(filtered)
        return [{'word': word, 'count': count} for word, count in counter.most_common(top_n)]

    def calculate_content_hash(self, text):
        """Generate hash for duplicate content detection"""
        clean = re.sub(r'\s+', '', text.lower())
        return hashlib.md5(clean.encode()).hexdigest()

    def detect_content_type(self, soup):
        """Detect page content type"""
        article = soup.find('article')
        if article:
            return 'Article'
        
        product_schema = soup.find('script', type='application/ld+json', string=re.compile(r'"@type"\s*:\s*"Product"'))
        if product_schema:
            return 'Product Page'
        
        form = soup.find('form')
        if form:
            return 'Form Page'
        
        return 'General Page'

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
            response = self.session.get(url, timeout=10, allow_redirects=True)
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # Basic SEO data
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            
            # Indexing checks
            is_noindex = 'noindex' in robots_content.lower()
            is_nofollow = 'nofollow' in robots_content.lower()
            is_noindex_follow = is_noindex and 'follow' in robots_content.lower()
            
            # X-Robots-Tag header
            x_robots = response.headers.get('X-Robots-Tag', '')
            
            # Header tags
            h1_tags = [self.smart_clean(h1.get_text()) for h1 in soup.find_all('h1')]
            h2_tags = [self.smart_clean(h2.get_text()) for h2 in soup.find_all('h2')]
            h3_tags = [self.smart_clean(h3.get_text()) for h3 in soup.find_all('h3')]
            h4_tags = [self.smart_clean(h4.get_text()) for h4 in soup.find_all('h4')]
            
            # Content analysis
            text_content = soup.get_text()
            word_count = len(text_content.split())
            content_hash = self.calculate_content_hash(text_content)
            content_type = self.detect_content_type(soup)
            top_keywords = self.extract_keywords(text_content)
            
            # Custom extraction
            custom_data = ""
            if self.custom_selector:
                custom_elements = soup.select(self.custom_selector)
                custom_data = "; ".join([self.smart_clean(el.get_text()) for el in custom_elements])

            # --- ENHANCED LINK EXTRACTION WITH NOFOLLOW/DOFOLLOW ---
            internal_links = []
            external_links = []
            base_domain = urlparse(url).netloc
            
            search_area = soup
            if self.link_selector:
                specific_section = soup.select_one(self.link_selector)
                if specific_section:
                    search_area = specific_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(url, link['href'])
                link_text = self.smart_clean(link.get_text())[:100]
                
                # Extract link attributes
                rel_attr = link.get('rel', [])
                if isinstance(rel_attr, str):
                    rel_attr = [rel_attr]
                
                is_nofollow_link = 'nofollow' in rel_attr
                is_sponsored = 'sponsored' in rel_attr
                is_ugc = 'ugc' in rel_attr
                
                follow_status = 'nofollow' if is_nofollow_link else 'dofollow'
                
                # Additional attributes
                target = link.get('target', '')
                
                css_path = self.get_css_path(link)
                
                # Placement detection
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
                    'follow_status': follow_status,
                    'rel_attributes': ', '.join(rel_attr) if rel_attr else 'none',
                    'is_sponsored': is_sponsored,
                    'is_ugc': is_ugc,
                    'target': target,
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
                loading = img.get('loading', '')
                images.append({
                    'src': img_src,
                    'alt': self.smart_clean(img.get('alt', '')),
                    'title': self.smart_clean(img.get('title', '')),
                    'width': img.get('width', ''),
                    'height': img.get('height', ''),
                    'loading': loading  # lazy loading detection
                })
            
            # --- ENHANCED SCHEMA EXTRACTION ---
            scripts = soup.find_all('script', type='application/ld+json')
            schema_types = []
            schema_validity = "No Schema"
            schema_errors = []
            schema_data_list = []
            
            if scripts:
                schema_validity = "Valid"
                for script in scripts:
                    try:
                        if script.string:
                            schema_obj = json.loads(script.string)
                            
                            # Handle both single objects and arrays
                            if isinstance(schema_obj, dict):
                                schema_list = [schema_obj]
                            elif isinstance(schema_obj, list):
                                schema_list = schema_obj
                            else:
                                continue
                            
                            for item in schema_list:
                                if isinstance(item, dict):
                                    schema_type = item.get('@type', 'Unknown')
                                    schema_types.append(schema_type)
                                    
                                    # Store detailed schema info
                                    schema_data_list.append({
                                        'type': schema_type,
                                        'context': item.get('@context', ''),
                                        'full_data': json.dumps(item, indent=2)[:500]  # First 500 chars
                                    })
                                    
                    except json.JSONDecodeError as e:
                        schema_validity = "Invalid JSON"
                        schema_errors.append(f"JSON Error: {str(e)[:100]}")
                    except Exception as e:
                        schema_validity = "Parse Error"
                        schema_errors.append(f"Error: {str(e)[:100]}")
            
            # Hreflang detection
            hreflang_tags = []
            for link in soup.find_all('link', attrs={'rel': 'alternate'}):
                hreflang = link.get('hreflang')
                if hreflang:
                    hreflang_tags.append({
                        'hreflang': hreflang,
                        'href': link.get('href', '')
                    })
            
            # Pagination detection
            prev_page = soup.find('link', attrs={'rel': 'prev'})
            next_page = soup.find('link', attrs={'rel': 'next'})
            has_pagination = bool(prev_page or next_page)
            
            # Breadcrumb detection
            breadcrumb_schema = any('@type' in str(s) and 'BreadcrumbList' in str(s) for s in scripts)
            breadcrumb_nav = soup.find('nav', attrs={'aria-label': re.compile('breadcrumb', re.I)})
            has_breadcrumbs = breadcrumb_schema or bool(breadcrumb_nav)
            
            # Social tags
            og_title = soup.find('meta', attrs={'property': 'og:title'})
            og_desc = soup.find('meta', attrs={'property': 'og:description'})
            og_image = soup.find('meta', attrs={'property': 'og:image'})
            og_type = soup.find('meta', attrs={'property': 'og:type'})
            twitter_card = soup.find('meta', attrs={'name': 'twitter:card'})
            twitter_title = soup.find('meta', attrs={'name': 'twitter:title'})
            twitter_desc = soup.find('meta', attrs={'name': 'twitter:description'})
            twitter_image = soup.find('meta', attrs={'name': 'twitter:image'})
            
            # Security headers
            security_headers = {
                'strict_transport_security': response.headers.get('Strict-Transport-Security', ''),
                'content_security_policy': response.headers.get('Content-Security-Policy', ''),
                'x_frame_options': response.headers.get('X-Frame-Options', ''),
                'x_content_type_options': response.headers.get('X-Content-Type-Options', '')
            }
            
            # Performance metrics
            css_files = len(soup.find_all('link', attrs={'rel': 'stylesheet'}))
            js_files = len(soup.find_all('script', src=True))
            inline_css = len(soup.find_all('style'))
            inline_js = len([s for s in soup.find_all('script') if not s.get('src')])
            
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
            
            # Mobile viewport
            viewport = soup.find('meta', attrs={'name': 'viewport'})
            has_viewport = bool(viewport)
            viewport_content = viewport.get('content', '') if viewport else ''
            
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
                'x_robots_tag': x_robots,
                'is_noindex': is_noindex,
                'is_nofollow': is_nofollow,
                'is_noindex_follow': is_noindex_follow,
                'h1_tags': '; '.join(h1_tags),
                'h1_count': len(h1_tags),
                'h2_tags': '; '.join(h2_tags),
                'h2_count': len(h2_tags),
                'h3_tags': '; '.join(h3_tags),
                'h3_count': len(h3_tags),
                'h4_tags': '; '.join(h4_tags),
                'h4_count': len(h4_tags),
                'word_count': word_count,
                'content_hash': content_hash,
                'content_type': content_type,
                'top_keywords': json.dumps(top_keywords),
                'response_time': response.elapsed.total_seconds(),
                'content_length': len(response.content),
                'internal_links_count': len(internal_links),
                'external_links_count': len(external_links),
                'internal_links': internal_links,
                'external_links': external_links,
                'images': images,
                'image_count': len(images),
                'images_without_alt': len([img for img in images if not img['alt']]),
                'images_lazy_loaded': len([img for img in images if img['loading'] == 'lazy']),
                'schema_types': '; '.join(schema_types),
                'schema_count': len(schema_types),
                'schema_validity': schema_validity,
                'schema_errors': '; '.join(schema_errors),
                'schema_data': schema_data_list,
                'hreflang_tags': hreflang_tags,
                'hreflang_count': len(hreflang_tags),
                'has_pagination': has_pagination,
                'has_breadcrumbs': has_breadcrumbs,
                'redirect_chain': redirect_chain,
                'redirect_count': len(redirect_chain),
                'css_files': css_files,
                'js_files': js_files,
                'inline_css': inline_css,
                'inline_js': inline_js,
                'og_title': og_title.get('content', '') if og_title else '',
                'og_description': og_desc.get('content', '') if og_desc else '',
                'og_image': og_image.get('content', '') if og_image else '',
                'og_type': og_type.get('content', '') if og_type else '',
                'twitter_card': twitter_card.get('content', '') if twitter_card else '',
                'twitter_title': twitter_title.get('content', '') if twitter_title else '',
                'twitter_description': twitter_desc.get('content', '') if twitter_desc else '',
                'twitter_image': twitter_image.get('content', '') if twitter_image else '',
                'has_viewport': has_viewport,
                'viewport_content': viewport_content,
                'security_headers': security_headers,
                'content_type_header': response.headers.get('content-type', ''),
                'last_modified': response.headers.get('last-modified', ''),
                'server': response.headers.get('server', ''),
                'custom_extraction': custom_data,
                'indexability': self.get_indexability_status(response.status_code, robots_content, x_robots),
                'crawl_timestamp': datetime.now().isoformat()
            }
        except Exception as e:
            return {
                'url': url, 'original_url': url, 'status_code': 0, 'error': str(e),
                'title': '', 'title_length': 0, 'meta_description': '', 'meta_desc_length': 0,
                'canonical_url': '', 'meta_robots': '', 'x_robots_tag': '', 
                'is_noindex': False, 'is_nofollow': False, 'is_noindex_follow': False,
                'h1_tags': '', 'h1_count': 0, 'h2_tags': '', 'h2_count': 0, 
                'h3_tags': '', 'h3_count': 0, 'h4_tags': '', 'h4_count': 0, 
                'word_count': 0, 'content_hash': '', 'content_type': '', 'top_keywords': '[]',
                'response_time': 0, 'content_length': 0, 
                'internal_links_count': 0, 'external_links_count': 0,
                'internal_links': [], 'external_links': [], 'images': [], 
                'image_count': 0, 'images_without_alt': 0, 'images_lazy_loaded': 0,
                'schema_types': '', 'schema_count': 0, 'schema_validity': 'Error', 
                'schema_errors': str(e), 'schema_data': [],
                'hreflang_tags': [], 'hreflang_count': 0,
                'has_pagination': False, 'has_breadcrumbs': False,
                'redirect_chain': [], 'redirect_count': 0, 
                'css_files': 0, 'js_files': 0, 'inline_css': 0, 'inline_js': 0,
                'og_title': '', 'og_description': '', 'og_image': '', 'og_type': '',
                'twitter_card': '', 'twitter_title': '', 'twitter_description': '', 'twitter_image': '',
                'has_viewport': False, 'viewport_content': '',
                'security_headers': {}, 'content_type_header': '', 'last_modified': '', 
                'server': '', 'custom_extraction': '', 'indexability': 'Error', 
                'crawl_timestamp': datetime.now().isoformat()
            }
    
    def get_indexability_status(self, status_code, robots_content, x_robots=''):
        if status_code != 200:
            return 'Non-Indexable'
        if 'noindex' in robots_content.lower() or 'noindex' in x_robots.lower():
            return 'Non-Indexable'
        return 'Indexable'

# PSI Helper
def run_psi_test(url, api_key):
    if not api_key:
        return {"error": "No API Key"}
    
    api_url = f"https://www.googleapis.com/pagespeedonline/v5/runPagespeed?url={url}&strategy=mobile&key={api_key}"
    try:
        response = requests.get(api_url, timeout=30)
        data = response.json()
        
        if "error" in data:
            return {"error": data["error"]["message"]}
            
        lh_result = data["lighthouseResult"]
        score = lh_result["categories"]["performance"]["score"] * 100
        
        metrics = {
            "URL": url,
            "Score": f"{score:.0f}",
            "LCP": lh_result["audits"]["largest-contentful-paint"]["displayValue"],
            "FCP": lh_result["audits"]["first-contentful-paint"]["displayValue"],
            "CLS": lh_result["audits"]["cumulative-layout-shift"]["displayValue"],
            "INP": lh_result["audits"].get("interaction-to-next-paint", {}).get("displayValue", "N/A"),
            "TTI": lh_result["audits"]["interactive"]["displayValue"]
        }
        return metrics
    except Exception as e:
        return {"error": str(e), "URL": url}

# Crawler handlers
def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, 
                  custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector)
    crawler.set_base_url(start_url)
    
    urls_to_visit = deque([start_url])
    visited_urls = set()
    crawl_data = []
    
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    
    with ThreadPoolExecutor(max_workers=10) as executor:
        while urls_to_visit and len(visited_urls) < max_urls:
            if st.session_state.stop_crawling: 
                break
                
            current_batch = []
            batch_size = min(20, len(urls_to_visit), max_urls - len(visited_urls))
            
            for _ in range(batch_size):
                if urls_to_visit and not st.session_state.stop_crawling:
                    url = urls_to_visit.popleft()
                    if url not in visited_urls and crawler.can_fetch(url):
                        current_batch.append(url)
                        visited_urls.add(url)
            
            if not current_batch: 
                break
            
            future_to_url = {executor.submit(crawler.extract_page_data, url): url 
                            for url in current_batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: 
                        f.cancel()
                    break
                    
                try:
                    page_data = future.result(timeout=15)
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
                    elapsed = time.time() - st.session_state.get('start_time', time.time())
                    speed = len(crawl_data) / max(1, elapsed)
                    status_text.text(f"🚀 Crawled: {len(crawl_data)} | Queue: {len(urls_to_visit)} | Speed: {speed:.1f} URLs/sec")
                    
                except Exception as e:
                    pass
    
    return crawl_data

def crawl_from_list(url_list, progress_container, ignore_robots=False, 
                    custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(len(url_list), ignore_robots, 
                              custom_selector=custom_selector, link_selector=link_selector)
    crawl_data = []
    progress_bar = progress_container.progress(0)
    status_text = progress_container.empty()
    valid_urls = [url.strip() for url in url_list if crawler.can_fetch(url.strip())]
    
    if not valid_urls: 
        return crawl_data
    
    with ThreadPoolExecutor(max_workers=15) as executor:
        for i in range(0, len(valid_urls), 25):
            if st.session_state.stop_crawling: 
                break
            batch = valid_urls[i:i + 25]
            future_to_url = {executor.submit(crawler.extract_page_data, url): url 
                            for url in batch}
            
            for future in as_completed(future_to_url):
                if st.session_state.stop_crawling:
                    for f in future_to_url: 
                        f.cancel()
                    break
                try:
                    page_data = future.result(timeout=15)
                    crawl_data.append(page_data)
                    progress = len(crawl_data) / len(valid_urls)
                    progress_bar.progress(progress)
                    elapsed = time.time() - st.session_state.get('start_time', time.time())
                    speed = len(crawl_data) / max(1, elapsed)
                    status_text.text(f"🚀 Processed: {len(crawl_data)}/{len(valid_urls)} | Speed: {speed:.1f} URLs/sec")
                except Exception as e:
                    pass
    return crawl_data

def crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots=False, 
                       custom_selector=None, link_selector=None):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, 
                              custom_selector=custom_selector, link_selector=link_selector)
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
    return crawl_from_list(sitemap_urls, progress_container, ignore_robots, 
                          custom_selector, link_selector)

# ENHANCED CSS STYLING
st.markdown("""
<style>
    /* Modern Professional Styling */
    @import url('https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&display=swap');
    
    * {
        font-family: 'Inter', -apple-system, BlinkMacSystemFont, sans-serif;
    }
    
    /* Main container */
    .main {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        padding: 0;
    }
    
    .block-container {
        padding-top: 2rem;
        padding-bottom: 2rem;
        max-width: 1400px;
    }
    
    /* Header */
    .main-header {
        background: linear-gradient(135deg, #1e3c72 0%, #2a5298 100%);
        padding: 2rem;
        border-radius: 15px;
        margin-bottom: 2rem;
        box-shadow: 0 10px 40px rgba(0,0,0,0.2);
        text-align: center;
    }
    
    .main-header h1 {
        color: white;
        margin: 0;
        font-weight: 700;
        font-size: 2.5rem;
        text-shadow: 2px 2px 4px rgba(0,0,0,0.3);
    }
    
    .main-header p {
        color: rgba(255,255,255,0.9);
        margin: 0.5rem 0 0 0;
        font-size: 1.1rem;
    }
    
    /* Sidebar */
    [data-testid="stSidebar"] {
        background: linear-gradient(180deg, #1a1a2e 0%, #16213e 100%);
    }
    
    [data-testid="stSidebar"] * {
        color: #e0e0e0 !important;
    }
    
    /* Tabs */
    .stTabs [data-baseweb="tab-list"] {
        gap: 8px;
        padding: 8px;
        border-radius: 12px;
        background: linear-gradient(135deg, #f5f7fa 0%, #c3cfe2 100%);
        box-shadow: 0 4px 15px rgba(0,0,0,0.1);
    }
    
    .stTabs [data-baseweb="tab"] {
        height: 55px;
        white-space: pre-wrap;
        border-radius: 10px;
        background: #ffffff !important;
        color: #2c3e50 !important;
        border: 2px solid transparent !important;
        font-weight: 500;
        transition: all 0.3s ease;
        box-shadow: 0 2px 8px rgba(0,0,0,0.05);
    }
    
    .stTabs [data-baseweb="tab"]:hover {
        transform: translateY(-2px);
        box-shadow: 0 4px 12px rgba(0,0,0,0.15);
    }
    
    .stTabs [aria-selected="true"] {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%) !important;
        color: #ffffff !important;
        border: 2px solid #5a67d8 !important;
        font-weight: 700;
        box-shadow: 0 6px 20px rgba(102, 126, 234, 0.4);
    }
    
    /* Metrics */
    [data-testid="stMetricValue"] {
        font-size: 2rem;
        font-weight: 700;
        color: #667eea;
    }
    
    /* Dataframes */
    .dataframe {
        border-radius: 10px;
        overflow: hidden;
        box-shadow: 0 4px 15px rgba(0,0,0,0.1);
    }
    
    /* Buttons */
    .stButton > button {
        border-radius: 8px;
        font-weight: 600;
        transition: all 0.3s ease;
        border: none;
        box-shadow: 0 4px 12px rgba(0,0,0,0.15);
    }
    
    .stButton > button:hover {
        transform: translateY(-2px);
        box-shadow: 0 6px 20px rgba(0,0,0,0.2);
    }
    
    /* Progress bar */
    .stProgress > div > div > div {
        background: linear-gradient(90deg, #667eea 0%, #764ba2 100%);
    }
    
    /* Cards */
    div[data-testid="column"] {
        background: white;
        padding: 1rem;
        border-radius: 10px;
        box-shadow: 0 2px 10px rgba(0,0,0,0.05);
    }
    
    /* Download buttons */
    .stDownloadButton > button {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white;
        border: none;
        font-weight: 600;
    }
    
    /* Info boxes */
    .stAlert {
        border-radius: 10px;
        border-left: 4px solid #667eea;
    }
    
    /* Success/Warning/Error boxes */
    .stSuccess {
        background-color: #d4edda;
        border-left: 4px solid #28a745;
    }
    
    .stWarning {
        background-color: #fff3cd;
        border-left: 4px solid #ffc107;
    }
    
    .stError {
        background-color: #f8d7da;
        border-left: 4px solid #dc3545;
    }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown("""
<div class="main-header">
    <h1>🐸 Battersea Pro SEO Crawler</h1>
    <p>Professional Edition • Advanced Technical SEO Analysis & Auditing Tool</p>
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
        sitemap_url_orphan = st.text_input("🗺️ Orphan Check Sitemap (Optional)", 
                                          placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs", min_value=1, max_value=100000, value=1000)
        crawl_scope = st.selectbox("🎯 Crawl Scope", ["subfolder", "subdomain", "exact"])
        
    elif crawl_mode == "📝 List Mode (Upload URLs)":
        uploaded_file = st.file_uploader("Choose file", type=['txt', 'csv'])
        url_list_text = st.text_area("Or paste URLs here (one per line)", height=100)
        
    elif crawl_mode == "🗺️ Sitemap Crawl (XML Sitemap)":
        sitemap_url = st.text_input("🗺️ Sitemap URL", 
                                    placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs", min_value=1, max_value=100000, value=5000)
    
    ignore_robots = st.checkbox("🤖 Ignore robots.txt")
    
    st.markdown("---")
    st.subheader("⛏️ Advanced Extraction")
    custom_selector = st.text_input("Custom Data Selector (Optional)", 
                                    placeholder=".price, h1, #sku", 
                                    help="Extract text from specific CSS selectors")
    
    st.subheader("🎯 Link Extraction Scope")
    link_selector = st.text_input("Link Area Selector (Optional)", 
                                  placeholder=".sidebar, #footer, .content", 
                                  help="Only extract links from this element")
    
    st.markdown("---")
    st.subheader("⚡ PageSpeed Insights")
    psi_api_key = st.text_input("Google PSI API Key (Optional)", 
                                type="password", 
                                help="Required for Speed Testing")

    col1, col2 = st.columns(2)
    with col1:
        start_btn = st.button("🚀 Start Crawl", type="primary", 
                             disabled=st.session_state.crawling, 
                             use_container_width=True)
    with col2:
        stop_btn = st.button("⛔ Stop Crawl", 
                            disabled=not st.session_state.crawling,
                            use_container_width=True)
    
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
                st.session_state.sitemap_urls_set = set(
                    crawler_temp.extract_sitemap_urls(sitemap_url_orphan)
                )
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
            st.error("❌ Please provide valid input")
    
    if st.button("🗑️ Clear All Data", use_container_width=True):
        st.session_state.crawl_data = []
        st.session_state.sitemap_urls_set = set()
        st.session_state.psi_results = {}
        st.rerun()

# Main content area
if st.session_state.crawling:
    st.header("🐸 Battersea Crawler is Running...")
    progress_container = st.container()
    
    try:
        custom_sel = custom_selector if custom_selector else None
        link_sel = link_selector if link_selector else None
        
        if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
            crawl_data = crawl_website(start_url, max_urls, crawl_scope, 
                                      progress_container, ignore_robots, 
                                      custom_sel, link_sel)
        elif crawl_mode == "📝 List Mode (Upload URLs)":
            if uploaded_file:
                content = uploaded_file.read().decode('utf-8')
                url_list = [line.strip() for line in content.split('\n') if line.strip()]
            else:
                url_list = [line.strip() for line in url_list_text.split('\n') if line.strip()]
            crawl_data = crawl_from_list(url_list, progress_container, 
                                        ignore_robots, custom_sel, link_sel)
        else:
            crawl_data = crawl_from_sitemap(sitemap_url, max_urls, 
                                           progress_container, ignore_robots, 
                                           custom_sel, link_sel)
        
        st.session_state.crawl_data = crawl_data if crawl_data else []
        st.session_state.crawling = False
        st.session_state.stop_crawling = False
        
        if st.session_state.stop_crawling:
            st.warning("⛔ Crawl stopped by user")
        else:
            crawl_time = time.time() - st.session_state.get('start_time', time.time())
            st.success(f"✅ Crawl completed! Analyzed {len(crawl_data)} URLs in {crawl_time:.1f} seconds")
        st.rerun()
        
    except Exception as e:
        st.error(f"❌ Error: {str(e)}")
        st.session_state.crawling = False

elif st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    
    # ENHANCED SUMMARY STATS
    st.header("📊 Battersea Pro Analysis Dashboard")
    
    col1, col2, col3, col4 = st.columns(4)
    with col1: 
        st.metric("🔍 Total URLs", len(df))
    with col2: 
        st.metric("✅ Indexable", len(df[df['indexability'] == 'Indexable']))
    with col3: 
        st.metric("❌ Non-Indexable", len(df[df['indexability'] == 'Non-Indexable']))
    with col4: 
        st.metric("🔄 Redirects", len(df[df['redirect_count'] > 0]))
    
    col5, col6, col7, col8 = st.columns(4)
    with col5:
        avg_response = df['response_time'].mean() if len(df) > 0 else 0
        st.metric("⚡ Avg Response", f"{avg_response:.2f}s")
    with col6:
        crawled_urls = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled_urls) if st.session_state.sitemap_urls_set else []
        st.metric("👻 Orphans", len(orphans))
    with col7:
        errors = len(df[df['status_code'] >= 400])
        st.metric("⚠️ Errors", errors)
    with col8:
        avg_words = df['word_count'].mean() if len(df) > 0 else 0
        st.metric("📝 Avg Words", f"{avg_words:.0f}")
    
    # Detect duplicates
    if 'content_hash' in df.columns:
        hash_counts = df['content_hash'].value_counts()
        duplicates = hash_counts[hash_counts > 1]
        duplicate_count = len(duplicates)
    else:
        duplicate_count = 0
    
    col9, col10, col11, col12 = st.columns(4)
    with col9:
        st.metric("🔗 Total Int. Links", df['internal_links_count'].sum())
    with col10:
        st.metric("🌐 Total Ext. Links", df['external_links_count'].sum())
    with col11:
        st.metric("🖼️ Total Images", df['image_count'].sum())
    with col12:
        st.metric("📋 Duplicate Content", duplicate_count)
    
    # ENHANCED TABS
    tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab10, tab11, tab12, tab13, tab14, tab15, tab16, tab17, tab18 = st.tabs([
        "🔗 Internal Links", 
        "🌐 External Links", 
        "🖼️ Images", 
        "📝 Titles & Meta", 
        "🏷️ Headers", 
        "🏗️ Schema & Structured Data",
        "🔄 Redirects", 
        "📊 Status Codes", 
        "🎯 Canonicals", 
        "📱 Social Tags", 
        "🚀 Performance",
        "🌍 Internationalization",
        "🔒 Security",
        "📋 Content Analysis",
        "🕸️ Link Graph", 
        "👻 Orphan Pages", 
        "⛏️ Custom Data",
        "⚡ PageSpeed Insights"
    ])
    
    # TAB 1: INTERNAL LINKS (WITH FOLLOW STATUS)
    with tab1:
        st.subheader("🔗 Internal Links Analysis (with Follow Status)")
        if link_selector:
            st.info(f"📍 Showing links extracted from: `{link_selector}`")
        else:
            st.info("📍 Showing links from all page sections")
            
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
                
                # Select relevant columns
                display_cols = ['Source URL', 'url', 'anchor_text', 'follow_status', 
                               'rel_attributes', 'placement', 'target']
                available_cols = [col for col in display_cols if col in final_links.columns]
                final_links_display = final_links[available_cols]
                final_links_display.columns = ['Source URL', 'Destination URL', 'Anchor Text', 
                                              'Follow Status', 'Rel Attributes', 'Placement', 'Target']
                
                st.dataframe(final_links_display, use_container_width=True, height=400)
                
                # Link statistics
                st.subheader("📊 Link Statistics")
                col1, col2, col3, col4 = st.columns(4)
                
                nofollow_count = len(final_links[final_links['follow_status'] == 'nofollow'])
                dofollow_count = len(final_links[final_links['follow_status'] == 'dofollow'])
                
                col1.metric("✅ Dofollow Links", dofollow_count)
                col2.metric("❌ Nofollow Links", nofollow_count)
                col3.metric("💰 Sponsored", len(final_links[final_links.get('is_sponsored', False) == True]))
                col4.metric("👥 UGC", len(final_links[final_links.get('is_ugc', False) == True]))
                
                # Placement distribution
                st.subheader("📍 Link Placement Distribution")
                placement_counts = final_links['placement'].value_counts()
                c1, c2, c3, c4 = st.columns(4)
                c1.metric("Header/Nav", placement_counts.get('Header', 0))
                c2.metric("Footer", placement_counts.get('Footer', 0))
                c3.metric("Body", placement_counts.get('Body', 0))
                c4.metric("Sidebar", placement_counts.get('Sidebar', 0))
                
                csv = final_links_display.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Internal Links Report", csv, 
                                 "internal_links_detailed.csv", "text/csv")
            else:
                st.warning("⚠️ No internal links found in the selected scope.")

    # TAB 2: EXTERNAL LINKS (WITH FOLLOW STATUS)
    with tab2:
        st.subheader("🌐 External Links Analysis (with Follow Status)")
        external_data = []
        for _, row in df.iterrows():
            for ext_link in row.get('external_links', []):
                external_data.append({
                    'source_url': row['url'],
                    'destination_url': ext_link['url'],
                    'anchor_text': ext_link['anchor_text'],
                    'follow_status': ext_link.get('follow_status', 'unknown'),
                    'rel_attributes': ext_link.get('rel_attributes', 'none'),
                    'is_sponsored': ext_link.get('is_sponsored', False),
                    'is_ugc': ext_link.get('is_ugc', False),
                    'placement': ext_link.get('placement', 'Unknown'),
                    'target': ext_link.get('target', '')
                })
        
        if external_data:
            ext_df = pd.DataFrame(external_data)
            st.dataframe(ext_df, use_container_width=True, height=400)
            
            # External link statistics
            st.subheader("📊 External Link Statistics")
            col1, col2, col3, col4 = st.columns(4)
            
            nofollow_ext = len(ext_df[ext_df['follow_status'] == 'nofollow'])
            dofollow_ext = len(ext_df[ext_df['follow_status'] == 'dofollow'])
            
            col1.metric("✅ Dofollow External", dofollow_ext)
            col2.metric("❌ Nofollow External", nofollow_ext)
            col3.metric("💰 Sponsored Links", len(ext_df[ext_df['is_sponsored'] == True]))
            col4.metric("👥 UGC Links", len(ext_df[ext_df['is_ugc'] == True]))
            
            # Top external domains
            st.subheader("🔝 Top External Domains")
            ext_df['domain'] = ext_df['destination_url'].apply(lambda x: urlparse(x).netloc)
            top_domains = ext_df['domain'].value_counts().head(10)
            st.bar_chart(top_domains)
            
            csv = ext_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download External Links Report", csv, 
                             "external_links_detailed.csv", "text/csv")
        else:
            st.info("ℹ️ No external links found.")

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
                    'loading': img.get('loading', 'eager'),
                    'has_alt': 'Yes' if img['alt'] else 'No'
                })
        
        if images_data:
            img_df = pd.DataFrame(images_data)
            st.dataframe(img_df, use_container_width=True, height=400)
            
            # Image statistics
            st.subheader("📊 Image Statistics")
            col1, col2, col3, col4 = st.columns(4)
            
            col1.metric("🖼️ Total Images", len(img_df))
            col2.metric("❌ Missing Alt Text", len(img_df[img_df['has_alt'] == 'No']))
            col3.metric("⚡ Lazy Loaded", len(img_df[img_df['loading'] == 'lazy']))
            col4.metric("✅ Alt Text Coverage", 
                       f"{(len(img_df[img_df['has_alt'] == 'Yes']) / len(img_df) * 100):.1f}%")
            
            csv = img_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Images Report", csv, "images_analysis.csv", "text/csv")
        else:
            st.info("ℹ️ No images found.")

    # TAB 4: TITLES & META
    with tab4:
        st.subheader("📝 Titles & Meta Descriptions Analysis")
        
        title_meta_df = df[['url', 'title', 'title_length', 'meta_description', 
                            'meta_desc_length']].copy()
        
        # Add status indicators
        title_meta_df['title_status'] = title_meta_df['title_length'].apply(
            lambda x: '✅ Good' if 30 <= x <= 60 else ('⚠️ Too Short' if x < 30 else '❌ Too Long') if x > 0 else '❌ Missing'
        )
        title_meta_df['meta_status'] = title_meta_df['meta_desc_length'].apply(
            lambda x: '✅ Good' if 120 <= x <= 160 else ('⚠️ Too Short' if x < 120 else '❌ Too Long') if x > 0 else '❌ Missing'
        )
        
        st.dataframe(title_meta_df, use_container_width=True, height=400)
        
        # Statistics
        st.subheader("📊 Title & Meta Statistics")
        col1, col2, col3, col4 = st.columns(4)
        
        col1.metric("❌ Missing Titles", len(title_meta_df[title_meta_df['title_length'] == 0]))
        col2.metric("❌ Missing Meta Desc", len(title_meta_df[title_meta_df['meta_desc_length'] == 0]))
        col3.metric("✅ Good Titles", len(title_meta_df[title_meta_df['title_status'] == '✅ Good']))
        col4.metric("✅ Good Meta Desc", len(title_meta_df[title_meta_df['meta_status'] == '✅ Good']))
        
        csv = title_meta_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Titles & Meta Report", csv, 
                         "titles_meta_analysis.csv", "text/csv")

    # TAB 5: HEADERS
    with tab5:
        st.subheader("🏷️ Headers Analysis (H1-H4)")
        header_df = df[['url', 'h1_count', 'h1_tags', 'h2_count', 'h2_tags', 
                        'h3_count', 'h4_count']].copy()
        
        # Add header issues
        header_df['h1_status'] = header_df['h1_count'].apply(
            lambda x: '✅ Good' if x == 1 else ('❌ Missing' if x == 0 else '⚠️ Multiple H1s')
        )
        
        st.dataframe(header_df, use_container_width=True, height=400)
        
        # Statistics
        st.subheader("📊 Header Statistics")
        col1, col2, col3, col4 = st.columns(4)
        
        col1.metric("❌ Missing H1", len(header_df[header_df['h1_count'] == 0]))
        col2.metric("⚠️ Multiple H1s", len(header_df[header_df['h1_count'] > 1]))
        col3.metric("📊 Avg H2 per Page", f"{header_df['h2_count'].mean():.1f}")
        col4.metric("📊 Avg H3 per Page", f"{header_df['h3_count'].mean():.1f}")
        
        csv = header_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Headers Report", csv, "headers_analysis.csv", "text/csv")

    # TAB 6: SCHEMA & STRUCTURED DATA (ENHANCED)
    with tab6:
        st.subheader("🏗️ Schema Markup & Structured Data Validator")
        
        schema_df = df[['url', 'schema_types', 'schema_count', 'schema_validity', 
                       'schema_errors']].copy()
        
        # Color coding function
        def highlight_schema(val):
            if 'Valid' in str(val):
                return 'background-color: #d4edda'
            elif 'Invalid' in str(val) or 'Error' in str(val):
                return 'background-color: #f8d7da'
            elif 'No Schema' in str(val):
                return 'background-color: #fff3cd'
            return ''
        
        styled_schema = schema_df.style.applymap(highlight_schema, subset=['schema_validity'])
        st.dataframe(styled_schema, use_container_width=True, height=400)
        
        # Schema Statistics
        st.subheader("📊 Schema Statistics")
        col1, col2, col3, col4 = st.columns(4)
        
        col1.metric("✅ Valid Schema", len(schema_df[schema_df['schema_validity'] == 'Valid']))
        col2.metric("❌ Invalid Schema", len(schema_df[schema_df['schema_validity'].str.contains('Invalid|Error', na=False)]))
        col3.metric("⚠️ No Schema", len(schema_df[schema_df['schema_validity'] == 'No Schema']))
        col4.metric("📊 Avg Schema/Page", f"{schema_df['schema_count'].mean():.1f}")
        
        # Schema type distribution
        st.subheader("📊 Schema Type Distribution")
        all_schema_types = []
        for types_str in schema_df['schema_types'].dropna():
            all_schema_types.extend([t.strip() for t in str(types_str).split(';') if t.strip()])
        
        if all_schema_types:
            schema_type_counts = pd.Series(all_schema_types).value_counts()
            st.bar_chart(schema_type_counts.head(10))
        
        # Detailed schema viewer
        st.subheader("🔍 Detailed Schema Data")
        if 'schema_data' in df.columns:
            for idx, row in df.iterrows():
                if row.get('schema_data') and len(row['schema_data']) > 0:
                    with st.expander(f"📄 {row['url']}"):
                        for schema_item in row['schema_data']:
                            st.json(schema_item)
        
        # Indexing check
        st.subheader("🤖 Robots Meta Tag Analysis")
        robots_df = df[['url', 'meta_robots', 'x_robots_tag', 'is_noindex', 
                       'is_nofollow', 'is_noindex_follow']].copy()
        
        st.dataframe(robots_df, use_container_width=True, height=300)
        
        col1, col2, col3 = st.columns(3)
        col1.metric("🚫 Noindex Pages", len(df[df['is_noindex'] == True]))
        col2.metric("🔗 Nofollow Pages", len(df[df['is_nofollow'] == True]))
        col3.metric("⚠️ Noindex,Follow", len(df[df['is_noindex_follow'] == True]))
        
        if len(df[df['is_noindex_follow'] == True]) > 0:
            st.warning("⚠️ Pages with 'noindex, follow' detected!")
            noindex_follow_urls = df[df['is_noindex_follow'] == True][['url', 'meta_robots']]
            st.dataframe(noindex_follow_urls, use_container_width=True)
        
        csv = schema_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Schema Report", csv, "schema_analysis.csv", "text/csv")

    # TAB 7: REDIRECTS
    with tab7:
        st.subheader("🔄 Redirects Analysis")
        redirect_df = df[df['redirect_count'] > 0].copy()
        
        if not redirect_df.empty:
            display_redirect = redirect_df[['url', 'original_url', 'status_code', 
                                          'redirect_count']].copy()
            st.dataframe(display_redirect, use_container_width=True, height=400)
            
            # Redirect statistics
            col1, col2, col3 = st.columns(3)
            col1.metric("🔄 Total Redirects", len(redirect_df))
            col2.metric("📊 Avg Redirect Chain", f"{redirect_df['redirect_count'].mean():.1f}")
            col3.metric("⚠️ Long Chains (3+)", len(redirect_df[redirect_df['redirect_count'] >= 3]))
            
            csv = display_redirect.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Redirects Report", csv, 
                             "redirects_analysis.csv", "text/csv")
        else:
            st.success("✅ No redirects found - excellent!")

    # TAB 8: STATUS CODES
    with tab8:
        st.subheader("📊 HTTP Status Codes Analysis")
        status_df = df[['url', 'status_code', 'indexability']].copy()
        st.dataframe(status_df, use_container_width=True, height=400)
        
        # Status code distribution
        st.subheader("📊 Status Code Distribution")
        status_counts = df['status_code'].value_counts()
        col1, col2 = st.columns([2, 1])
        
        with col1:
            st.bar_chart(status_counts)
        
        with col2:
            for code, count in status_counts.items():
                if code == 200:
                    st.metric(f"✅ {code} OK", count)
                elif code >= 300 and code < 400:
                    st.metric(f"🔄 {code} Redirect", count)
                elif code >= 400 and code < 500:
                    st.metric(f"⚠️ {code} Client Error", count)
                elif code >= 500:
                    st.metric(f"❌ {code} Server Error", count)
        
        # Show errors prominently
        error_df = df[df['status_code'] >= 400]
        if not error_df.empty:
            st.error(f"❌ Found {len(error_df)} pages with errors!")
            st.dataframe(error_df[['url', 'status_code']], use_container_width=True)
        
        csv = status_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Status Report", csv, "status_codes.csv", "text/csv")

    # TAB 9: CANONICALS
    with tab9:
        st.subheader("🎯 Canonical URLs Analysis")
        canonical_df = df[['url', 'canonical_url']].copy()
        
        # Detect canonical issues
        canonical_df['canonical_status'] = canonical_df.apply(
            lambda row: '✅ Self-Referencing' if row['url'] == row['canonical_url'] 
            else ('⚠️ Points Elsewhere' if row['canonical_url'] 
            else '❌ Missing'), axis=1
        )
        
        st.dataframe(canonical_df, use_container_width=True, height=400)
        
        # Statistics
        col1, col2, col3 = st.columns(3)
        col1.metric("✅ Self-Referencing", 
                   len(canonical_df[canonical_df['canonical_status'] == '✅ Self-Referencing']))
        col2.metric("⚠️ Points Elsewhere", 
                   len(canonical_df[canonical_df['canonical_status'] == '⚠️ Points Elsewhere']))
        col3.metric("❌ Missing Canonical", 
                   len(canonical_df[canonical_df['canonical_status'] == '❌ Missing']))
        
        csv = canonical_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Canonicals Report", csv, 
                         "canonicals_analysis.csv", "text/csv")

    # TAB 10: SOCIAL TAGS
    with tab10:
        st.subheader("📱 Open Graph & Twitter Cards Analysis")
        social_df = df[['url', 'og_title', 'og_description', 'og_image', 'og_type',
                       'twitter_card', 'twitter_title', 'twitter_description', 
                       'twitter_image']].copy()
        
        st.dataframe(social_df, use_container_width=True, height=400)
        
        # Statistics
        col1, col2, col3, col4 = st.columns(4)
        col1.metric("📘 Has OG Title", len(social_df[social_df['og_title'] != '']))
        col2.metric("🖼️ Has OG Image", len(social_df[social_df['og_image'] != '']))
        col3.metric("🐦 Has Twitter Card", len(social_df[social_df['twitter_card'] != '']))
        col4.metric("✅ Complete OG Tags", 
                   len(social_df[(social_df['og_title'] != '') & 
                                (social_df['og_description'] != '') & 
                                (social_df['og_image'] != '')]))
        
        csv = social_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Social Tags Report", csv, 
                         "social_tags_analysis.csv", "text/csv")

    # TAB 11: PERFORMANCE
    with tab11:
        st.subheader("🚀 Performance Metrics Analysis")
        perf_df = df[['url', 'response_time', 'word_count', 'content_length', 
                     'css_files', 'js_files', 'inline_css', 'inline_js', 
                     'image_count', 'images_lazy_loaded']].copy()
        
        st.dataframe(perf_df, use_container_width=True, height=400)
        
        # Performance statistics
        st.subheader("📊 Performance Statistics")
        col1, col2, col3, col4 = st.columns(4)
        
        col1.metric("⚡ Avg Response Time", f"{perf_df['response_time'].mean():.2f}s")
        col2.metric("📊 Avg Page Size", f"{perf_df['content_length'].mean()/1024:.1f} KB")
        col3.metric("📦 Avg CSS Files", f"{perf_df['css_files'].mean():.1f}")
        col4.metric("📦 Avg JS Files", f"{perf_df['js_files'].mean():.1f}")
        
        # Identify slow pages
        slow_pages = perf_df[perf_df['response_time'] > 3]
        if not slow_pages.empty:
            st.warning(f"⚠️ {len(slow_pages)} pages loading slower than 3 seconds!")
            st.dataframe(slow_pages[['url', 'response_time']], use_container_width=True)
        
        # Resource analysis
        st.subheader("📊 Resource Usage Distribution")
        col1, col2 = st.columns(2)
        
        with col1:
            st.write("**CSS Resources**")
            st.bar_chart(perf_df[['css_files', 'inline_css']])
        
        with col2:
            st.write("**JavaScript Resources**")
            st.bar_chart(perf_df[['js_files', 'inline_js']])
        
        csv = perf_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Performance Report", csv, 
                         "performance_analysis.csv", "text/csv")

    # TAB 12: INTERNATIONALIZATION
    with tab12:
        st.subheader("🌍 Internationalization & Hreflang Analysis")
        
        if 'hreflang_tags' in df.columns:
            hreflang_data = []
            for _, row in df.iterrows():
                if row.get('hreflang_tags') and len(row['hreflang_tags']) > 0:
                    for tag in row['hreflang_tags']:
                        hreflang_data.append({
                            'source_url': row['url'],
                            'hreflang': tag['hreflang'],
                            'target_url': tag['href']
                        })
            
            if hreflang_data:
                hreflang_df = pd.DataFrame(hreflang_data)
                st.dataframe(hreflang_df, use_container_width=True, height=400)
                
                # Statistics
                col1, col2, col3 = st.columns(3)
                col1.metric("🌍 Pages with Hreflang", len(df[df['hreflang_count'] > 0]))
                col2.metric("📊 Total Hreflang Tags", len(hreflang_df))
                col3.metric("🗣️ Languages Detected", hreflang_df['hreflang'].nunique())
                
                # Language distribution
                st.subheader("📊 Language Distribution")
                lang_counts = hreflang_df['hreflang'].value_counts()
                st.bar_chart(lang_counts)
                
                csv = hreflang_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Hreflang Report", csv, 
                                 "hreflang_analysis.csv", "text/csv")
            else:
                st.info("ℹ️ No hreflang tags found.")
        
        # Mobile viewport analysis
        st.subheader("📱 Mobile Viewport Analysis")
        viewport_df = df[['url', 'has_viewport', 'viewport_content']].copy()
        
        col1, col2 = st.columns(2)
        col1.metric("✅ Has Viewport Meta", len(df[df['has_viewport'] == True]))
        col2.metric("❌ Missing Viewport", len(df[df['has_viewport'] == False]))
        
        if len(df[df['has_viewport'] == False]) > 0:
            st.warning("⚠️ Pages missing viewport meta tag (not mobile-friendly):")
            st.dataframe(df[df['has_viewport'] == False][['url']], use_container_width=True)

    # TAB 13: SECURITY
    with tab13:
        st.subheader("🔒 Security Headers Analysis")
        
        if 'security_headers' in df.columns and len(df) > 0:
            # Extract security headers
            security_data = []
            for _, row in df.iterrows():
                headers = row.get('security_headers', {})
                if isinstance(headers, dict):
                    security_data.append({
                        'url': row['url'],
                        'https': row['url'].startswith('https://'),
                        'hsts': bool(headers.get('strict_transport_security')),
                        'csp': bool(headers.get('content_security_policy')),
                        'x_frame': bool(headers.get('x_frame_options')),
                        'x_content_type': bool(headers.get('x_content_type_options'))
                    })
            
            if security_data:
                security_df = pd.DataFrame(security_data)
                st.dataframe(security_df, use_container_width=True, height=400)
                
                # Security statistics
                st.subheader("📊 Security Statistics")
                col1, col2, col3, col4 = st.columns(4)
                
                col1.metric("🔒 HTTPS Pages", len(security_df[security_df['https'] == True]))
                col2.metric("🛡️ Has HSTS", len(security_df[security_df['hsts'] == True]))
                col3.metric("📋 Has CSP", len(security_df[security_df['csp'] == True]))
                col4.metric("🖼️ Has X-Frame-Options", len(security_df[security_df['x_frame'] == True]))
                
                # Security score
                security_df['security_score'] = (
                    security_df['https'].astype(int) +
                    security_df['hsts'].astype(int) +
                    security_df['csp'].astype(int) +
                    security_df['x_frame'].astype(int) +
                    security_df['x_content_type'].astype(int)
                ) * 20
                
                avg_score = security_df['security_score'].mean()
                st.metric("🎯 Average Security Score", f"{avg_score:.1f}%")
                
                # Show pages with low security
                low_security = security_df[security_df['security_score'] < 60]
                if not low_security.empty:
                    st.warning(f"⚠️ {len(low_security)} pages with low security score:")
                    st.dataframe(low_security[['url', 'security_score']], use_container_width=True)
                
                csv = security_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download Security Report", csv, 
                                 "security_analysis.csv", "text/csv")

    # TAB 14: CONTENT ANALYSIS
    with tab14:
        st.subheader("📋 Content Quality Analysis")
        
        content_df = df[['url', 'word_count', 'content_hash', 'content_type', 
                        'has_pagination', 'has_breadcrumbs']].copy()
        
        # Content quality score
        content_df['quality_status'] = content_df['word_count'].apply(
            lambda x: '✅ Good' if x >= 300 else ('⚠️ Thin Content' if x > 0 else '❌ No Content')
        )
        
        st.dataframe(content_df, use_container_width=True, height=400)
        
        # Statistics
        st.subheader("📊 Content Statistics")
        col1, col2, col3, col4 = st.columns(4)
        
        col1.metric("📝 Avg Word Count", f"{content_df['word_count'].mean():.0f}")
        col2.metric("⚠️ Thin Content", len(content_df[content_df['word_count'] < 300]))
        col3.metric("🍞 Has Breadcrumbs", len(df[df['has_breadcrumbs'] == True]))
        col4.metric("📄 Has Pagination", len(df[df['has_pagination'] == True]))
        
        # Duplicate content detection
        st.subheader("📋 Duplicate Content Detection")
        hash_counts = content_df['content_hash'].value_counts()
        duplicates = hash_counts[hash_counts > 1]
        
        if len(duplicates) > 0:
            st.warning(f"⚠️ Found {len(duplicates)} groups of duplicate content!")
            
            for content_hash, count in duplicates.items():
                with st.expander(f"Duplicate Group ({count} pages)"):
                    duplicate_urls = content_df[content_df['content_hash'] == content_hash]['url']
                    st.write(duplicate_urls.tolist())
        else:
            st.success("✅ No duplicate content detected!")
        
        # Content type distribution
        st.subheader("📊 Content Type Distribution")
        type_counts = content_df['content_type'].value_counts()
        st.bar_chart(type_counts)
        
        # Top keywords
        if 'top_keywords' in df.columns:
            st.subheader("🔑 Top Keywords Across Site")
            all_keywords = []
            for keywords_json in df['top_keywords'].dropna():
                try:
                    keywords = json.loads(keywords_json)
                    all_keywords.extend([(kw['word'], kw['count']) for kw in keywords])
                except:
                    pass
            
            if all_keywords:
                keyword_counter = Counter()
                for word, count in all_keywords:
                    keyword_counter[word] += count
                
                top_keywords_df = pd.DataFrame(keyword_counter.most_common(20), 
                                              columns=['Keyword', 'Frequency'])
                st.dataframe(top_keywords_df, use_container_width=True)
        
        csv = content_df.to_csv(index=False).encode('utf-8')
        st.download_button("📥 Download Content Report", csv, 
                         "content_analysis.csv", "text/csv")

    # TAB 15: LINK GRAPH
    with tab15:
        st.subheader("🕸️ Internal Link Graph Visualization")
        
        if HAS_PYVIS:
            max_nodes = st.slider("Maximum nodes to display", 10, 100, 50)
            
            G = nx.DiGraph()
            subset = df.head(max_nodes)
            
            for _, row in subset.iterrows():
                src = row['url']
                # Node size based on internal links
                node_size = min(row['internal_links_count'] * 2 + 10, 50)
                
                # Color based on indexability
                if row['indexability'] == 'Indexable':
                    color = '#4CAF50'
                else:
                    color = '#f44336'
                
                G.add_node(src, title=row['title'][:50], color=color, size=node_size)
                
                for link in row.get('internal_links', []):
                    dst = link['url']
                    if dst in subset['url'].values:
                        # Edge color based on follow status
                        edge_color = '#4CAF50' if link.get('follow_status') == 'dofollow' else '#FFA726'
                        G.add_edge(src, dst, color=edge_color, 
                                 title=link.get('anchor_text', '')[:30])
            
            net = Network(height='700px', width='100%', bgcolor='#1a1a1a', 
                         font_color='white', directed=True)
            net.from_nx(G)
            net.set_options("""
            {
                "physics": {
                    "forceAtlas2Based": {
                        "gravitationalConstant": -50,
                        "centralGravity": 0.01,
                        "springLength": 100,
                        "springConstant": 0.08
                    },
                    "maxVelocity": 50,
                    "solver": "forceAtlas2Based",
                    "timestep": 0.35,
                    "stabilization": {"iterations": 150}
                }
            }
            """)
            
            try:
                net.save_graph("link_graph.html")
                with open("link_graph.html", 'r', encoding='utf-8') as f:
                    components.html(f.read(), height=750)
                
                st.info("🟢 Green nodes = Indexable | 🔴 Red nodes = Non-indexable | 🟠 Orange edges = Nofollow")
            except Exception as e:
                st.error(f"Graph error: {e}")
        else:
            st.error("⚠️ Install pyvis to view graph: `pip install pyvis`")

    # TAB 16: ORPHAN PAGES
    with tab16:
        st.subheader("👻 Orphan Pages Detection")
        
        if orphans:
            orphan_df = pd.DataFrame(orphans, columns=['Orphan URL'])
            st.warning(f"⚠️ Found {len(orphans)} orphan pages (in sitemap but not crawled)")
            st.dataframe(orphan_df, use_container_width=True, height=400)
            
            st.info("💡 **What are orphan pages?** These pages exist in your sitemap but have no internal links pointing to them from your crawled pages.")
            
            csv = orphan_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Orphan Pages", csv, 
                             "orphan_pages.csv", "text/csv")
        else:
            st.success("✅ No orphan pages found (or no sitemap provided)!")

    # TAB 17: CUSTOM DATA
    with tab17:
        st.subheader("⛏️ Custom Extracted Data")
        
        if custom_selector:
            st.info(f"🎯 Results for CSS Selector: `{custom_selector}`")
            custom_df = df[['url', 'custom_extraction']].copy()
            st.dataframe(custom_df, use_container_width=True, height=400)
            
            csv = custom_df.to_csv(index=False).encode('utf-8')
            st.download_button("📥 Download Custom Data", csv, 
                             "custom_extraction.csv", "text/csv")
        else:
            st.info("ℹ️ Enter a CSS Selector in the sidebar to extract custom data from pages.")
            st.markdown("""
            **Examples:**
            - `.price` - Extract all elements with class 'price'
            - `#product-id` - Extract element with ID 'product-id'
            - `h1.title` - Extract H1 tags with class 'title'
            - `.author, .date` - Extract multiple elements (comma-separated)
            """)

    # TAB 18: PAGESPEED INSIGHTS
    with tab18:
        st.subheader("⚡ Google PageSpeed Insights Analysis")
        
        if psi_api_key:
            st.info("🔑 API Key detected. Select URLs to test below.")
            
            # URL selection
            urls_to_test = st.multiselect(
                "Select URLs to Test (Recommended: 5-10 URLs)", 
                df['url'].head(50).tolist(),
                help="Each test takes 30-60 seconds. Testing too many URLs will take a long time."
            )
            
            col1, col2 = st.columns([1, 3])
            with col1:
                run_psi = st.button("🚀 Run PageSpeed Tests", type="primary")
            with col2:
                if urls_to_test:
                    st.info(f"⏱️ Estimated time: {len(urls_to_test) * 45} seconds")
            
            if run_psi:
                if not urls_to_test:
                    st.warning("⚠️ Please select at least one URL.")
                else:
                    progress_psi = st.progress(0)
                    status_psi = st.empty()
                    results = []
                    
                    for i, u in enumerate(urls_to_test):
                        status_psi.text(f"Testing {i+1}/{len(urls_to_test)}: {u[:50]}...")
                        res = run_psi_test(u, psi_api_key)
                        results.append(res)
                        progress_psi.progress((i + 1) / len(urls_to_test))
                    
                    st.session_state.psi_results = results
                    status_psi.text("✅ All tests completed!")
            
            # Display results
            if st.session_state.psi_results:
                psi_df = pd.DataFrame(st.session_state.psi_results)
                
                # Reorder columns
                cols_order = ['URL', 'Score', 'LCP', 'FCP', 'CLS', 'INP', 'TTI']
                available_cols = [c for c in cols_order if c in psi_df.columns]
                psi_display = psi_df[available_cols]
                
                st.dataframe(psi_display, use_container_width=True)
                
                # Statistics
                if 'Score' in psi_df.columns:
                    try:
                        scores = pd.to_numeric(psi_df['Score'], errors='coerce')
                        avg_score = scores.mean()
                        
                        col1, col2, col3 = st.columns(3)
                        col1.metric("📊 Average Score", f"{avg_score:.1f}")
                        col2.metric("✅ Good (90+)", len(scores[scores >= 90]))
                        col3.metric("⚠️ Needs Work (<50)", len(scores[scores < 50]))
                    except:
                        pass
                
                csv_psi = psi_df.to_csv(index=False).encode('utf-8')
                st.download_button("📥 Download PSI Report", csv_psi, 
                                 "pagespeed_insights.csv", "text/csv")
        else:
            st.warning("⚠️ PSI API Key is required. Add it in the sidebar to use this feature.")
            st.markdown("""
            **How to get a Google PageSpeed Insights API Key:**
            1. Go to [Google Cloud Console](https://console.cloud.google.com/)
            2. Create a new project or select existing one
            3. Enable "PageSpeed Insights API"
            4. Go to Credentials and create an API key
            5. Copy the API key and paste it in the sidebar
            """)

    # COMPREHENSIVE REPORT DOWNLOAD
    st.markdown("---")
    st.header("📥 Complete SEO Audit Reports")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        csv_all = df.to_csv(index=False).encode('utf-8')
        st.download_button(
            "📊 Download Complete Dataset", 
            csv_all, 
            "complete_seo_audit.csv", 
            "text/csv",
            use_container_width=True
        )
    
    with col2:
        # Create summary report
        summary_data = {
            'Metric': [
                'Total URLs Crawled',
                'Indexable Pages',
                'Non-Indexable Pages',
                'Pages with Errors',
                'Average Response Time',
                'Total Internal Links',
                'Total External Links',
                'Total Images',
                'Images Missing Alt Text',
                'Pages with Valid Schema',
                'Pages with Redirects',
                'Orphan Pages',
                'Duplicate Content Groups'
            ],
            'Value': [
                len(df),
                len(df[df['indexability'] == 'Indexable']),
                len(df[df['indexability'] == 'Non-Indexable']),
                len(df[df['status_code'] >= 400]),
                f"{df['response_time'].mean():.2f}s",
                df['internal_links_count'].sum(),
                df['external_links_count'].sum(),
                df['image_count'].sum(),
                df['images_without_alt'].sum(),
                len(df[df['schema_validity'] == 'Valid']),
                len(df[df['redirect_count'] > 0]),
                len(orphans),
                duplicate_count
            ]
        }
        summary_df = pd.DataFrame(summary_data)
        summary_csv = summary_df.to_csv(index=False).encode('utf-8')
        st.download_button(
            "📋 Download Summary Report", 
            summary_csv, 
            "seo_audit_summary.csv", 
            "text/csv",
            use_container_width=True
        )
    
    with col3:
        # Create issues report
        issues_data = []
        
        for _, row in df.iterrows():
            issues = []
            if row['status_code'] >= 400:
                issues.append(f"HTTP {row['status_code']} Error")
            if row['title_length'] == 0:
                issues.append("Missing Title")
            if row['meta_desc_length'] == 0:
                issues.append("Missing Meta Description")
            if row['h1_count'] == 0:
                issues.append("Missing H1")
            if row['h1_count'] > 1:
                issues.append("Multiple H1s")
            if row['indexability'] == 'Non-Indexable':
                issues.append("Non-Indexable")
            if row['images_without_alt'] > 0:
                issues.append(f"{row['images_without_alt']} Images Missing Alt")
            if row['schema_validity'] in ['Invalid JSON', 'Error']:
                issues.append("Schema Issues")
            if not row.get('has_viewport', True):
                issues.append("Missing Viewport (Not Mobile-Friendly)")
            
            if issues:
                issues_data.append({
                    'URL': row['url'],
                    'Issues': '; '.join(issues),
                    'Issue Count': len(issues)
                })
        
        if issues_data:
            issues_df = pd.DataFrame(issues_data)
            issues_csv = issues_df.to_csv(index=False).encode('utf-8')
            st.download_button(
                "⚠️ Download Issues Report", 
                issues_csv, 
                "seo_issues_report.csv", 
                "text/csv",
                use_container_width=True
            )

else:
    # LANDING PAGE
    st.markdown("""
    <div style="text-align: center; padding: 3rem;">
        <h2>👈 Configure your crawl settings and click '🚀 Start Crawl' to begin</h2>
        <p style="font-size: 1.1rem; color: #666; margin-top: 1rem;">
            Professional SEO crawler with advanced technical analysis capabilities
        </p>
    </div>
    """, unsafe_allow_html=True)
    
    # Feature highlights
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("""
        ### 🔍 **Link Analysis**
        - Nofollow/Dofollow detection
        - Internal & external link tracking
        - Link placement analysis
        - Sponsored & UGC attributes
        """)
    
    with col2:
        st.markdown("""
        ### 🏗️ **Structured Data**
        - Schema.org validation
        - JSON-LD parsing
        - Detailed schema viewer
        - Robots meta analysis
        """)
    
    with col3:
        st.markdown("""
        ### 📊 **Technical SEO**
        - Content quality analysis
        - Duplicate content detection
        - Security headers check
        - Mobile-friendly detection
        """)
