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
if 'psi_results' not in st.session_state:
    st.session_state.psi_results = {}

class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None, link_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Ultra Frog SEO Crawler/3.0 (https://ultrafrog.seo)',
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
        if self.crawl_scope == "exact":
            return url == urljoin(f"https://{self.base_domain}", self.base_path)
        elif self.crawl_scope == "subdomain":
            return self.base_domain in parsed.netloc
        else:
            return (parsed.netloc == self.base_domain and parsed.path.startswith(self.base_path))
    
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
                except:
                    self.robots_cache[domain] = None
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
        
    def extract_page_data(self, url):
        try:
            response = self.session.get(url, timeout=8, allow_redirects=True)
            soup = BeautifulSoup(response.content, 'html.parser')
            
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            
            # Check specifically for 'noindex, follow'
            is_noindex_follow = False
            if robots_content:
                content_lower = robots_content.lower()
                if 'noindex' in content_lower and 'follow' in content_lower:
                    is_noindex_follow = True

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
            base_domain = urlparse(url).netloc
            search_area = soup
            if self.link_selector:
                specific_section = soup.select_one(self.link_selector)
                if specific_section: search_area = specific_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(url, link['href'])
                link_text = self.smart_clean(link.get_text())[:100]
                css_path = self.get_css_path(link)
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower: placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower: placement = "Header"
                elif "sidebar" in path_lower: placement = "Sidebar"

                link_data = {'url': href, 'anchor_text': link_text, 'css_path': css_path, 'placement': placement}
                if urlparse(href).netloc == base_domain: internal_links.append(link_data)
                else: external_links.append(link_data)
            
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
            
            og_title = soup.find('meta', attrs={'property': 'og:title'})
            og_desc = soup.find('meta', attrs={'property': 'og:description'})
            og_image = soup.find('meta', attrs={'property': 'og:image'})
            twitter_title = soup.find('meta', attrs={'name': 'twitter:title'})
            twitter_desc = soup.find('meta', attrs={'name': 'twitter:description'})
            twitter_image = soup.find('meta', attrs={'name': 'twitter:image'})
            
            scripts = soup.find_all('script', type='application/ld+json')
            schema_types = []
            schema_validity = "No Schema"
            schema_errors = []
            if scripts:
                schema_validity = "Valid"
                for script in scripts:
                    try:
                        if script.string:
                            schema_data = json.loads(script.string)
                            if isinstance(schema_data, dict) and '@type' in schema_data: schema_types.append(schema_data['@type'])
                            elif isinstance(schema_data, list):
                                for item in schema_data:
                                    if isinstance(item, dict) and '@type' in item: schema_types.append(item['@type'])
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
                        'step': i + 1, 'from_url': resp.url, 'status_code': resp.status_code,
                        'redirect_type': '301' if resp.status_code == 301 else f'{resp.status_code}'
                    })
            
            return {
                'url': response.url, 'original_url': url, 'status_code': response.status_code,
                'title': title_text, 'title_length': len(title_text), 'meta_description': meta_desc_text,
                'meta_desc_length': len(meta_desc_text), 'canonical_url': canonical_url, 'meta_robots': robots_content,
                'is_noindex_follow': is_noindex_follow,
                'h1_tags': '; '.join(h1_tags), 'h1_count': len(h1_tags), 'h2_tags': '; '.join(h2_tags), 'h2_count': len(h2_tags),
                'h3_tags': '; '.join(h3_tags), 'h3_count': len(h3_tags), 'h4_tags': '; '.join(h4_tags), 'h4_count': len(h4_tags),
                'word_count': word_count, 'response_time': response.elapsed.total_seconds(),
                'content_length': len(response.content), 'internal_links_count': len(internal_links),
                'external_links_count': len(external_links), 'internal_links': internal_links,
                'external_links': external_links, 'images': images, 'image_count': len(images),
                'images_without_alt': len([img for img in images if not img['alt']]), 'schema_types': '; '.join(schema_types),
                'schema_count': len(schema_types), 'schema_validity': schema_validity, 'schema_errors': '; '.join(schema_errors),
                'redirect_chain': redirect_chain, 'redirect_count': len(redirect_chain),
                'css_files': css_files, 'js_files': js_files,
                'og_title': og_title.get('content', '') if og_title else '', 'og_description': og_desc.get('content', '') if og_desc else '',
                'og_image': og_image.get('content', '') if og_image else '', 'twitter_title': twitter_title.get('content', '') if twitter_title else '',
                'twitter_description': twitter_desc.get('content', '') if twitter_desc else '', 'twitter_image': twitter_image.get('content', '') if twitter_image else '',
                'content_type': response.headers.get('content-type', ''), 'last_modified': response.headers.get('last-modified', ''),
                'server': response.headers.get('server', ''), 'custom_extraction': custom_data,
                'indexability': self.get_indexability_status(response.status_code, robots_content),
                'crawl_timestamp': datetime.now().isoformat()
            }
        except Exception as e:
            return {
                'url': url, 'original_url': url, 'status_code': 0, 'error': str(e),
                'title': '', 'title_length': 0, 'meta_description': '', 'meta_desc_length': 0,
                'canonical_url': '', 'meta_robots': '', 'is_noindex_follow': False,
                'h1_tags': '', 'h1_count': 0, 'h2_tags': '', 'h2_count': 0, 'h3_tags': '', 'h3_count': 0,
                'h4_tags': '', 'h4_count': 0, 'word_count': 0, 'response_time': 0,
                'content_length': 0, 'internal_links_count': 0, 'external_links_count': 0,
                'internal_links': [], 'external_links': [], 'images': [], 'image_count': 0,
                'images_without_alt': 0, 'schema_types': '', 'schema_count': 0, 'schema_validity': 'Error', 'schema_errors': '',
                'redirect_chain': [], 'redirect_count': 0, 'css_files': 0, 'js_files': 0,
                'og_title': '', 'og_description': '', 'og_image': '', 'twitter_title': '', 'twitter_description': '', 'twitter_image': '',
                'content_type': '', 'last_modified': '', 'server': '', 'custom_extraction': '',
                'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat()
            }
    
    def get_indexability_status(self, status_code, robots_content):
        if status_code != 200: return 'Non-Indexable'
        if 'noindex' in robots_content.lower(): return 'Non-Indexable'
        return 'Indexable'

def run_psi_test(url, api_key):
    if not api_key: return {"error": "No API Key Provided"}
    api_url = f"https://www.googleapis.com/pagespeedonline/v5/runPagespeed?url={url}&strategy=mobile&key={api_key}"
    try:
        response = requests.get(api_url)
        data = response.json()
        if "error" in data: return {"error": data["error"]["message"]}
        lh = data["lighthouseResult"]
        return {
            "Score": lh["categories"]["performance"]["score"] * 100,
            "LCP": lh["audits"]["largest-contentful-paint"]["displayValue"],
            "FCP": lh["audits"]["first-contentful-paint"]["displayValue"],
            "CLS": lh["audits"]["cumulative-layout-shift"]["displayValue"],
            "INP": lh["audits"].get("interaction-to-next-paint", {}).get("displayValue", "N/A"),
            "TTI": lh["audits"]["interactive"]["displayValue"]
        }
    except Exception as e: return {"error": str(e)}

def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots, custom_selector, link_selector):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector, link_selector)
    crawler.set_base_url(start_url)
    urls = deque([start_url])
    visited = set()
    data = []
    bar = progress_container.progress(0)
    txt = progress_container.empty()
    with ThreadPoolExecutor(max_workers=10) as exe:
        while urls and len(visited) < max_urls:
            if st.session_state.stop_crawling: break
            batch = []
            for _ in range(min(20, len(urls), max_urls - len(visited))):
                if urls and not st.session_state.stop_crawling:
                    u = urls.popleft()
                    if u not in visited and crawler.can_fetch(u):
                        batch.append(u)
                        visited.add(u)
            if not batch: break
            futures = {exe.submit(crawler.extract_page_data, u): u for u in batch}
            for f in as_completed(futures):
                if st.session_state.stop_crawling: break
                try:
                    res = f.result(timeout=12)
                    data.append(res)
                    if not st.session_state.stop_crawling:
                        for l in res.get('internal_links', []):
                            lu = l['url']
                            if lu not in visited and lu not in urls and crawler.should_crawl_url(lu): urls.append(lu)
                    bar.progress(min(len(data)/max_urls, 1.0))
                    txt.text(f"🚀 Crawled: {len(data)}")
                except: pass
    return data

def crawl_from_list(url_list, progress_container, ignore_robots, custom_selector, link_selector):
    crawler = UltraFrogCrawler(len(url_list), ignore_robots, "exact", custom_selector, link_selector)
    data = []
    bar = progress_container.progress(0)
    txt = progress_container.empty()
    valid = [u.strip() for u in url_list if crawler.can_fetch(u.strip())]
    if not valid: return []
    with ThreadPoolExecutor(max_workers=15) as exe:
        for i in range(0, len(valid), 25):
            if st.session_state.stop_crawling: break
            futures = {exe.submit(crawler.extract_page_data, u): u for u in valid[i:i+25]}
            for f in as_completed(futures):
                try:
                    res = f.result(timeout=12)
                    data.append(res)
                    bar.progress(len(data)/len(valid))
                    txt.text(f"🚀 Processed: {len(data)}/{len(valid)}")
                except: pass
    return data

def crawl_from_sitemap(sitemap_url, max_urls, progress_container, ignore_robots, custom_selector, link_selector):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, "exact", custom_selector, link_selector)
    progress_container.text("🗺️ Reading sitemap...")
    urls = crawler.extract_sitemap_urls(sitemap_url)
    if not urls: return []
    if len(urls) > max_urls: urls = urls[:max_urls]
    return crawl_from_list(urls, progress_container, ignore_robots, custom_selector, link_selector)

st.markdown("""<style>.stTabs [data-baseweb="tab-list"]{gap:10px;padding:6px;background:#eef2f6;}.stTabs [data-baseweb="tab"]{height:50px;background:#fff;border:1px solid #d1d5db;}.stTabs [aria-selected="true"]{background:#4CAF50 !important;color:#fff !important;}</style>""", unsafe_allow_html=True)
st.markdown("""<div class="main-header"><h1 style="color:white;">Battersea Crawler</h1><p style="color:white;opacity:0.9;">Professional Edition • Full SEO Analysis</p></div>""", unsafe_allow_html=True)

with st.sidebar:
    st.header("🔧 Configuration")
    mode = st.selectbox("🎯 Mode", ["🕷️ Spider Crawl", "📝 List Mode", "🗺️ Sitemap Crawl"])
    sm_orphan = ""
    if mode == "🕷️ Spider Crawl":
        start_url = st.text_input("🌐 Website URL", "https://example.com")
        sm_orphan = st.text_input("🗺️ Orphan Check Sitemap (Optional)")
        max_urls = st.number_input("📊 Max URLs", 1, 100000, 1000)
        scope = st.selectbox("🎯 Scope", ["subfolder", "subdomain", "exact"])
    elif mode == "📝 List Mode":
        up_file = st.file_uploader("Upload URLs", type=['txt','csv'])
        txt_urls = st.text_area("Paste URLs")
    elif mode == "🗺️ Sitemap Crawl":
        sm_url = st.text_input("🗺️ Sitemap URL")
        max_urls = st.number_input("📊 Max URLs", 1, 100000, 5000)
    
    ignore_robots = st.checkbox("🤖 Ignore robots.txt")
    st.markdown("---")
    st.subheader("⛏️ Custom Extraction")
    custom_sel = st.text_input("Data Selector", placeholder=".price, h1")
    link_sel = st.text_input("Link Scope", placeholder=".footer, .content")
    st.markdown("---")
    st.subheader("⚡ PageSpeed")
    psi_key = st.text_input("API Key (Optional)", type="password")
    
    c1, c2 = st.columns(2)
    with c1: start = st.button("🚀 Start", type="primary", disabled=st.session_state.crawling)
    with c2: stop = st.button("⛔ Stop", disabled=not st.session_state.crawling)
    
    if stop:
        st.session_state.stop_crawling = True
        st.session_state.crawling = False
        st.rerun()
    
    if start:
        valid = False
        if mode == "🕷️ Spider Crawl" and start_url:
            valid = True
            if sm_orphan: st.session_state.sitemap_urls_set = set(UltraFrogCrawler().extract_sitemap_urls(sm_orphan))
            else: st.session_state.sitemap_urls_set = set()
        elif mode == "📝 List Mode" and (up_file or txt_urls): valid = True
        elif mode == "🗺️ Sitemap Crawl" and sm_url: valid = True
        
        if valid:
            st.session_state.crawling = True
            st.session_state.stop_crawling = False
            st.session_state.crawl_data = []
            st.session_state.psi_results = {}
            st.rerun()

    if st.button("🗑️ Reset"):
        st.session_state.crawl_data = []
        st.session_state.sitemap_urls_set = set()
        st.session_state.psi_results = {}
        st.rerun()

if st.session_state.crawling:
    st.header("🐸 Crawling...")
    prog = st.container()
    try:
        c_sel = custom_sel if custom_sel else None
        l_sel = link_sel if link_sel else None
        if mode == "🕷️ Spider Crawl": data = crawl_website(start_url, max_urls, scope, prog, ignore_robots, c_sel, l_sel)
        elif mode == "📝 List Mode":
            u = []
            if up_file: u = [l.strip() for l in up_file.read().decode('utf-8').split('\n') if l.strip()]
            else: u = [l.strip() for l in txt_urls.split('\n') if l.strip()]
            data = crawl_from_list(u, prog, ignore_robots, c_sel, l_sel)
        else: data = crawl_from_sitemap(sm_url, max_urls, prog, ignore_robots, c_sel, l_sel)
        st.session_state.crawl_data = data
        st.session_state.crawling = False
        st.rerun()
    except Exception as e:
        st.error(f"Error: {e}")
        st.session_state.crawling = False

elif st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    st.header("📊 Battersea Analysis Dashboard")
    
    # Tabs
    tabs = st.tabs([
        "🔗 Links", "🌐 External", "🖼️ Images", "📝 Titles", "📄 Meta", "🏷️ Headers", 
        "🔄 Redirects", "📊 Status", "🎯 Canonicals", "📱 Social", "🚀 Tech", 
        "🕸️ Graph", "👻 Orphans", "⛏️ Custom", "⚡ Speed (PSI)", "🏗️ Schema"
    ])
    
    # 1. Links
    with tabs[0]:
        st.subheader("Internal Links")
        if 'internal_links' in df.columns:
            base = df[['url', 'internal_links']].copy().rename(columns={'url':'Source'})
            exp = base.explode('internal_links').dropna()
            if not exp.empty:
                norm = pd.json_normalize(exp['internal_links'])
                final = pd.concat([exp['Source'].reset_index(drop=True), norm.reset_index(drop=True)], axis=1)
                st.dataframe(final, use_container_width=True)
            else: st.warning("No links found")
            
    # 2. External
    with tabs[1]:
        st.subheader("External Links")
        ext_data = []
        for _, r in df.iterrows():
            for l in r.get('external_links', []):
                ext_data.append({'Source': r['url'], 'Dest': l['url'], 'Anchor': l['anchor_text']})
        st.dataframe(pd.DataFrame(ext_data), use_container_width=True)

    # 3. Images
    with tabs[2]:
        st.subheader("Images")
        img_data = []
        for _, r in df.iterrows():
            for i in r.get('images', []):
                img_data.append({'Source': r['url'], 'Img': i['src'], 'Alt': i['alt']})
        st.dataframe(pd.DataFrame(img_data), use_container_width=True)

    # 4-11 Standard Tabs
    with tabs[3]: st.dataframe(df[['url', 'title', 'title_length']], use_container_width=True)
    with tabs[4]: st.dataframe(df[['url', 'meta_description', 'meta_desc_length']], use_container_width=True)
    with tabs[5]: st.dataframe(df[['url', 'h1_tags', 'h2_tags']], use_container_width=True)
    with tabs[6]: st.dataframe(df[df['redirect_count']>0][['url','status_code','redirect_count']], use_container_width=True)
    with tabs[7]: st.dataframe(df[['url', 'status_code', 'indexability']], use_container_width=True)
    with tabs[8]: st.dataframe(df[['url', 'canonical_url']], use_container_width=True)
    with tabs[9]: st.dataframe(df[['url', 'og_title', 'twitter_title']], use_container_width=True)
    with tabs[10]: st.dataframe(df[['url', 'response_time', 'word_count']], use_container_width=True)
    
    # 12. Graph
    with tabs[11]:
        if HAS_PYVIS:
            G = nx.DiGraph()
            sub = df.head(50)
            for _, r in sub.iterrows():
                G.add_node(r['url'], label=r['title'][:20], color='#4CAF50')
                for l in r.get('internal_links', []):
                    if l['url'] in sub['url'].values: G.add_edge(r['url'], l['url'])
            net = Network(height='500px', width='100%', bgcolor='#222', font_color='white')
            net.from_nx(G)
            try:
                net.save_graph("g.html")
                with open("g.html",'r',encoding='utf-8') as f: components.html(f.read(), height=550)
            except: st.error("Graph Error")
        else: st.error("Install pyvis")

    # 13. Orphans
    with tabs[12]:
        crawled = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled) if st.session_state.sitemap_urls_set else []
        st.dataframe(pd.DataFrame(orphans, columns=['Orphan URL']), use_container_width=True)

    # 14. Custom
    with tabs[13]: st.dataframe(df[['url', 'custom_extraction']], use_container_width=True)

    # 15. Speed (PSI)
    with tabs[14]:
        st.subheader("⚡ Google PageSpeed Insights")
        if psi_key:
            u_test = st.multiselect("Select URLs", df['url'].head(10).tolist())
            if st.button("Run Test"):
                res = []
                p = st.progress(0)
                for i, u in enumerate(u_test):
                    res.append({**{'url': u}, **run_psi_test(u, psi_key)})
                    p.progress((i+1)/len(u_test))
                st.session_state.psi_results = res
            
            if st.session_state.psi_results:
                st.dataframe(pd.DataFrame(st.session_state.psi_results), use_container_width=True)
        else: st.warning("Enter API Key in Sidebar")

    # 16. Schema & Indexing
    with tabs[15]:
        st.subheader("🏗️ Schema Validator")
        st.dataframe(df[['url', 'schema_types', 'schema_validity', 'schema_errors']], use_container_width=True)
        
        st.divider()
        st.subheader("🤖 Indexing Check (noindex, follow)")
        noindex = df[df['is_noindex_follow']==True][['url', 'meta_robots']]
        if not noindex.empty:
            st.error(f"Found {len(noindex)} pages with 'noindex, follow'")
            st.dataframe(noindex, use_container_width=True)
        else: st.success("No 'noindex, follow' pages found.")

    # 📥 EXPORT ALL CENTER 📥
    st.markdown("---")
    st.header("📥 Export Center")
    st.info("Download individual reports for specific analysis.")
    
    ec1, ec2, ec3, ec4 = st.columns(4)
    
    # Preparing DataFrames for Export
    # Internal Links
    df_int = pd.DataFrame()
    if 'internal_links' in df.columns:
        base = df[['url', 'internal_links']].copy().rename(columns={'url':'Source'})
        exp = base.explode('internal_links').dropna()
        if not exp.empty:
            norm = pd.json_normalize(exp['internal_links'])
            df_int = pd.concat([exp['Source'].reset_index(drop=True), norm.reset_index(drop=True)], axis=1)

    # External
    ext_list = []
    for _, r in df.iterrows():
        for l in r.get('external_links', []):
            ext_list.append({'Source': r['url'], 'Dest': l['url'], 'Anchor': l['anchor_text']})
    df_ext = pd.DataFrame(ext_list)

    # Images
    img_list = []
    for _, r in df.iterrows():
        for i in r.get('images', []):
            img_list.append({'Source': r['url'], 'Img': i['src'], 'Alt': i['alt']})
    df_img = pd.DataFrame(img_list)

    # Button Grid
    with ec1:
        st.download_button("🔗 Internal Links", df_int.to_csv(index=False).encode('utf-8'), "internal_links.csv", "text/csv")
        st.download_button("📄 Meta Desc", df[['url','meta_description']].to_csv(index=False).encode('utf-8'), "meta.csv", "text/csv")
        st.download_button("🎯 Canonicals", df[['url','canonical_url']].to_csv(index=False).encode('utf-8'), "canonicals.csv", "text/csv")
        st.download_button("👻 Orphans", pd.DataFrame(orphans, columns=['Orphan']).to_csv(index=False).encode('utf-8'), "orphans.csv", "text/csv")

    with ec2:
        st.download_button("🌐 External Links", df_ext.to_csv(index=False).encode('utf-8'), "external_links.csv", "text/csv")
        st.download_button("🏷️ Headers", df[['url','h1_tags','h2_tags']].to_csv(index=False).encode('utf-8'), "headers.csv", "text/csv")
        st.download_button("📱 Social Tags", df[['url','og_title','twitter_title']].to_csv(index=False).encode('utf-8'), "social.csv", "text/csv")
        st.download_button("⛏️ Custom Data", df[['url','custom_extraction']].to_csv(index=False).encode('utf-8'), "custom.csv", "text/csv")

    with ec3:
        st.download_button("🖼️ Images", df_img.to_csv(index=False).encode('utf-8'), "images.csv", "text/csv")
        st.download_button("🔄 Redirects", df[df['redirect_count']>0].to_csv(index=False).encode('utf-8'), "redirects.csv", "text/csv")
        st.download_button("🚀 Performance", df[['url','response_time','word_count']].to_csv(index=False).encode('utf-8'), "performance.csv", "text/csv")
        
    with ec4:
        st.download_button("📝 Titles", df[['url','title']].to_csv(index=False).encode('utf-8'), "titles.csv", "text/csv")
        st.download_button("📊 Status Codes", df[['url','status_code']].to_csv(index=False).encode('utf-8'), "status.csv", "text/csv")
        # Graph is visual, skipping CSV
        if st.session_state.psi_results:
            st.download_button("⚡ Speed (PSI)", pd.DataFrame(st.session_state.psi_results).to_csv(index=False).encode('utf-8'), "psi.csv", "text/csv")
        else:
            st.button("⚡ Speed (Run Test First)", disabled=True)

    st.markdown("---")
    st.download_button("📥 DOWNLOAD COMPLETE DATASET", df.to_csv(index=False).encode('utf-8'), "full_crawl_complete.csv", "text/csv", use_container_width=True)

else:
    st.info("Ready to crawl.")
