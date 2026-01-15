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

# Try importing pyvis for graphing
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False

# --- 1. PAGE CONFIGURATION & STYLING ---
st.set_page_config(page_title="Battersea Crawler Pro", layout="wide", page_icon="🐸")

# Custom CSS for better scrolling and structure
st.markdown("""
<style>
    /* Main Layout adjustment */
    .block-container { padding-top: 2rem; padding-bottom: 3rem; }
    
    /* Tab Styling */
    .stTabs [data-baseweb="tab-list"] { gap: 8px; background-color: #f8f9fa; padding: 10px; border-radius: 10px; }
    .stTabs [data-baseweb="tab"] { height: 45px; background-color: #ffffff; border-radius: 6px; padding: 0 20px; border: 1px solid #e0e0e0; }
    .stTabs [aria-selected="true"] { background-color: #ff4b4b; color: white !important; border: 1px solid #ff4b4b; }
    
    /* Metrics Styling */
    div[data-testid="stMetricValue"] { font-size: 24px; font-weight: 700; }
    
    /* Table Scrolling Fix */
    .stDataFrame { width: 100%; }
    
    /* Headers */
    .main-header { background: linear-gradient(90deg, #1e3a8a, #3b82f6); padding: 1.5rem; border-radius: 10px; color: white; margin-bottom: 2rem; }
    .main-header h1 { color: white; margin: 0; font-size: 2rem; }
    .main-header p { color: #e0e7ff; margin: 0; font-size: 1rem; }
</style>
""", unsafe_allow_html=True)

# --- 2. SESSION STATE INITIALIZATION ---
if 'crawl_data' not in st.session_state: st.session_state.crawl_data = []
if 'crawling' not in st.session_state: st.session_state.crawling = False
if 'stop_crawling' not in st.session_state: st.session_state.stop_crawling = False
if 'sitemap_urls_set' not in st.session_state: st.session_state.sitemap_urls_set = set()
if 'psi_results' not in st.session_state: st.session_state.psi_results = {}

# --- 3. CRAWLER LOGIC CLASS ---
class UltraFrogCrawler:
    def __init__(self, max_urls=1000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None, link_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector
        self.link_selector = link_selector
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Ultra Frog SEO Crawler/3.0 (Internal Analysis)',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Connection': 'keep-alive'
        })
        # Optimize connection pool
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
        else: # subfolder
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
        return " > ".join(path)

    def extract_sitemap_urls(self, sitemap_url):
        urls = []
        try:
            response = self.session.get(sitemap_url, timeout=10)
            if response.status_code == 200:
                root = ET.fromstring(response.content)
                namespaces = {'sitemap': 'http://www.sitemaps.org/schemas/sitemap/0.9'}
                # Check for index
                sitemapindex = root.findall('.//sitemap:sitemap', namespaces)
                if sitemapindex:
                    for s in sitemapindex:
                        loc = s.find('sitemap:loc', namespaces)
                        if loc is not None: urls.extend(self.extract_sitemap_urls(loc.text))
                else:
                    url_elements = root.findall('.//sitemap:url', namespaces)
                    for u in url_elements:
                        loc = u.find('sitemap:loc', namespaces)
                        if loc is not None: urls.append(loc.text)
        except: pass
        return urls
        
    def extract_page_data(self, url):
        try:
            response = self.session.get(url, timeout=10, allow_redirects=True)
            soup = BeautifulSoup(response.content, 'html.parser')
            
            # --- 1. BASIC SEO ---
            title = soup.find('title')
            title_text = self.smart_clean(title.get_text()) if title else ""
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = self.smart_clean(meta_desc.get('content', '')) if meta_desc else ""
            canonical = soup.find('link', attrs={'rel': 'canonical'})
            canonical_url = canonical.get('href') if canonical else ""
            
            # --- 2. INDEXING ---
            meta_robots = soup.find('meta', attrs={'name': 'robots'})
            robots_content = meta_robots.get('content', '') if meta_robots else ""
            is_noindex_follow = 'noindex' in robots_content.lower() and 'follow' in robots_content.lower()

            # --- 3. HEADINGS ---
            h1s = [self.smart_clean(h.get_text()) for h in soup.find_all('h1')]
            h2s = [self.smart_clean(h.get_text()) for h in soup.find_all('h2')]
            
            # --- 4. LINKS (Scoped) ---
            internal_links = []
            external_links = []
            base_domain = urlparse(url).netloc
            
            # Determine search area
            search_area = soup
            if self.link_selector:
                found_section = soup.select_one(self.link_selector)
                if found_section: search_area = found_section
            
            for link in search_area.find_all('a', href=True):
                href = urljoin(url, link['href'])
                link_text = self.smart_clean(link.get_text())[:100]
                css_path = self.get_css_path(link)
                
                # Placement Detection
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower: placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower: placement = "Header"
                elif "sidebar" in path_lower: placement = "Sidebar"

                link_data = {'url': href, 'anchor_text': link_text, 'css_path': css_path, 'placement': placement}
                if urlparse(href).netloc == base_domain: internal_links.append(link_data)
                else: external_links.append(link_data)
            
            # --- 5. IMAGES ---
            images = []
            for img in soup.find_all('img'):
                images.append({
                    'src': urljoin(url, img.get('src', '')),
                    'alt': self.smart_clean(img.get('alt', '')),
                    'title': self.smart_clean(img.get('title', ''))
                })
            
            # --- 6. SCHEMA (Enhanced) ---
            schema_scripts = soup.find_all('script', type='application/ld+json')
            schema_validity = "No Schema"
            schema_types = []
            schema_raw_data = [] # Store full JSON objects
            schema_errors = []

            if schema_scripts:
                schema_validity = "Valid"
                for script in schema_scripts:
                    try:
                        # robust text extraction
                        content = script.string if script.string else script.get_text()
                        if content:
                            data = json.loads(content)
                            schema_raw_data.append(data) # Store raw
                            
                            # Extract types
                            if isinstance(data, dict):
                                if '@type' in data: schema_types.append(data['@type'])
                                if '@graph' in data: # Handle Yoast style graph
                                    for node in data['@graph']:
                                        if '@type' in node: schema_types.append(node['@type'])
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

            # --- 7. REDIRECTS ---
            redirect_chain = []
            if hasattr(response, 'history') and response.history:
                for i, resp in enumerate(response.history):
                    redirect_chain.append({
                        'step': i+1, 'from': resp.url, 'code': resp.status_code
                    })

            # --- 8. CUSTOM EXTRACTION ---
            custom_data = ""
            if self.custom_selector:
                els = soup.select(self.custom_selector)
                custom_data = "; ".join([self.smart_clean(e.get_text()) for e in els])

            return {
                'url': response.url, 'status_code': response.status_code,
                'title': title_text, 'title_length': len(title_text),
                'meta_description': meta_desc_text, 'meta_desc_length': len(meta_desc_text),
                'canonical_url': canonical_url, 'meta_robots': robots_content,
                'is_noindex_follow': is_noindex_follow,
                'h1_tags': "; ".join(h1s), 'h1_count': len(h1s),
                'h2_tags': "; ".join(h2s), 'h2_count': len(h2s),
                'internal_links': internal_links, 'internal_count': len(internal_links),
                'external_links': external_links, 'external_count': len(external_links),
                'images': images, 'image_count': len(images),
                'schema_types': "; ".join(schema_types), 'schema_validity': schema_validity,
                'schema_raw': json.dumps(schema_raw_data, indent=2) if schema_raw_data else "", # Store Raw
                'schema_errors': "; ".join(schema_errors),
                'redirect_chain': redirect_chain, 'redirect_count': len(redirect_chain),
                'response_time': response.elapsed.total_seconds(),
                'word_count': len(soup.get_text().split()),
                'custom_extraction': custom_data,
                'crawl_time': datetime.now().isoformat()
            }
        except Exception as e:
            return {'url': url, 'status_code': 0, 'error': str(e)}

# --- 4. HELPER FUNCTIONS ---
def run_psi_test(url, api_key):
    if not api_key: return {"error": "No API Key"}
    api_url = f"https://www.googleapis.com/pagespeedonline/v5/runPagespeed?url={url}&strategy=mobile&key={api_key}"
    try:
        r = requests.get(api_url)
        d = r.json()
        if "error" in d: return {"error": d["error"]["message"]}
        lh = d["lighthouseResult"]
        return {
            "Score": lh["categories"]["performance"]["score"] * 100,
            "LCP": lh["audits"]["largest-contentful-paint"]["displayValue"],
            "CLS": lh["audits"]["cumulative-layout-shift"]["displayValue"],
            "FID": lh["audits"]["max-potential-fid"]["displayValue"],
            "INP": lh["audits"].get("interaction-to-next-paint", {}).get("displayValue", "N/A")
        }
    except Exception as e: return {"error": str(e)}

def execute_crawl(mode, start_url, up_file, txt_urls, sm_url, max_urls, ignore, custom_sel, link_sel, sm_orphan):
    crawler = UltraFrogCrawler(max_urls, ignore, "exact" if mode!="🕷️ Spider Crawl" else "subfolder", custom_sel, link_sel)
    
    if sm_orphan:
        st.session_state.sitemap_urls_set = set(crawler.extract_sitemap_urls(sm_orphan))
    
    urls = []
    if mode == "🕷️ Spider Crawl":
        crawler.set_base_url(start_url)
        urls = deque([start_url])
    elif mode == "📝 List Mode":
        if up_file: urls = deque([l.strip() for l in up_file.read().decode('utf-8').split('\n') if l.strip()])
        else: urls = deque([l.strip() for l in txt_urls.split('\n') if l.strip()])
    elif mode == "🗺️ Sitemap Crawl":
        urls = deque(crawler.extract_sitemap_urls(sm_url)[:max_urls])

    visited = set()
    data = []
    
    # Progress UI
    bar = st.progress(0)
    status = st.empty()
    
    with ThreadPoolExecutor(max_workers=10) as exe:
        while urls and len(visited) < max_urls:
            if st.session_state.stop_crawling: break
            
            # Batching
            batch = []
            for _ in range(min(20, len(urls))):
                if urls:
                    u = urls.popleft()
                    if u not in visited:
                        batch.append(u)
                        visited.add(u)
            
            if not batch: break
            
            futures = {exe.submit(crawler.extract_page_data, u): u for u in batch}
            
            for f in as_completed(futures):
                if st.session_state.stop_crawling: break
                try:
                    res = f.result()
                    if res.get('status_code') != 0:
                        data.append(res)
                        # Spider Logic
                        if mode == "🕷️ Spider Crawl":
                            for l in res.get('internal_links', []):
                                lu = l['url']
                                if lu not in visited and lu not in urls and crawler.should_crawl_url(lu):
                                    urls.append(lu)
                    
                    # Update UI
                    prog_val = min(len(data) / max_urls, 1.0)
                    bar.progress(prog_val)
                    status.text(f"🚀 Crawled: {len(data)} pages")
                    
                except: pass
                
    return data

# --- 5. MAIN UI LAYOUT ---

# HEADER
st.markdown("""
<div class="main-header">
    <h1>Battersea Crawler Pro</h1>
    <p>Professional SEO Audit Tool • Schema Validation • PageSpeed • Structure Analysis</p>
</div>
""", unsafe_allow_html=True)

# SIDEBAR
with st.sidebar:
    st.header("⚙️ Configuration")
    crawl_mode = st.selectbox("Method", ["🕷️ Spider Crawl", "📝 List Mode", "🗺️ Sitemap Crawl"])
    
    # Dynamic Inputs based on mode
    start_url, sm_orphan, up_file, txt_urls, sm_url = None, None, None, None, None
    
    if crawl_mode == "🕷️ Spider Crawl":
        start_url = st.text_input("Start URL", "https://example.com")
        sm_orphan = st.text_input("Sitemap (Orphan Check)", placeholder="Optional")
    elif crawl_mode == "📝 List Mode":
        up_file = st.file_uploader("Upload URLs", type=['txt','csv'])
        txt_urls = st.text_area("Paste URLs")
    elif crawl_mode == "🗺️ Sitemap Crawl":
        sm_url = st.text_input("Sitemap URL")

    max_urls = st.number_input("Max Pages", 1, 50000, 500)
    ignore_robots = st.checkbox("Ignore Robots.txt", value=False)
    
    st.markdown("---")
    st.subheader("⛏️ Extraction")
    custom_sel = st.text_input("CSS Data Selector", placeholder=".price, #sku")
    link_sel = st.text_input("Link Scope Selector", placeholder="#footer, .sidebar")
    
    st.markdown("---")
    st.subheader("⚡ PageSpeed")
    psi_key = st.text_input("Google API Key", type="password")
    
    c1, c2 = st.columns(2)
    start_btn = c1.button("🚀 Run", type="primary", disabled=st.session_state.crawling)
    stop_btn = c2.button("⛔ Stop")

    if stop_btn:
        st.session_state.stop_crawling = True
        st.session_state.crawling = False
        st.rerun()

    if start_btn:
        st.session_state.crawling = True
        st.session_state.stop_crawling = False
        st.session_state.crawl_data = []
        st.session_state.psi_results = {}
        st.rerun()

    if st.sidebar.button("🗑️ Clear All"):
        st.session_state.crawl_data = []
        st.session_state.psi_results = {}
        st.rerun()

# MAIN EXECUTION
if st.session_state.crawling:
    st.info("🐸 Crawling started... Please wait.")
    data = execute_crawl(crawl_mode, start_url, up_file, txt_urls, sm_url, max_urls, ignore_robots, custom_sel, link_sel, sm_orphan)
    st.session_state.crawl_data = data
    st.session_state.crawling = False
    st.success("Crawl Complete!")
    st.rerun()

# RESULTS DISPLAY
if st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    
    # 1. METRICS ROW
    m1, m2, m3, m4, m5 = st.columns(5)
    m1.metric("Total URLs", len(df))
    m2.metric("200 OK", len(df[df['status_code'] == 200]))
    m3.metric("Errors", len(df[df['status_code'] != 200]))
    m4.metric("Avg Speed", f"{df['response_time'].mean():.2f}s" if 'response_time' in df else "0s")
    if 'schema_validity' in df:
        m5.metric("Valid Schema", len(df[df['schema_validity'] == 'Valid']))

    st.markdown("---")

    # 2. ANALYSIS TABS
    tabs = st.tabs([
        "🔗 Internal Links", "🌐 External", "🖼️ Images", "📝 Titles & Meta", "🏷️ Headers",
        "🏗️ Schema", "⚡ Speed (PSI)", "📊 Status", "🔄 Redirects", "🎯 Canonicals",
        "📱 Social", "👻 Orphans", "⛏️ Custom Data"
    ])

    # --- TAB LOGIC ---
    
    # Links
    with tabs[0]:
        st.subheader("Internal Links Analysis")
        if 'internal_links' in df.columns:
            # Flatten links for display
            link_rows = []
            for _, row in df.iterrows():
                for l in row.get('internal_links', []):
                    link_rows.append({
                        'Source': row['url'], 
                        'Destination': l['url'], 
                        'Anchor': l['anchor_text'],
                        'Placement': l['placement']
                    })
            df_int = pd.DataFrame(link_rows)
            st.dataframe(df_int, use_container_width=True) # Full width scroll
        else: st.warning("No internal link data.")

    # External
    with tabs[1]:
        st.subheader("External Links")
        if 'external_links' in df.columns:
            ext_rows = []
            for _, row in df.iterrows():
                for l in row.get('external_links', []):
                    ext_rows.append({'Source': row['url'], 'External URL': l['url'], 'Anchor': l['anchor_text']})
            df_ext = pd.DataFrame(ext_rows)
            st.dataframe(df_ext, use_container_width=True)

    # Images
    with tabs[2]:
        st.subheader("Image Audit")
        if 'images' in df.columns:
            img_rows = []
            for _, row in df.iterrows():
                for i in row.get('images', []):
                    img_rows.append({'Source': row['url'], 'Image': i['src'], 'Alt': i['alt'], 'Title': i['title']})
            df_img = pd.DataFrame(img_rows)
            st.dataframe(df_img, use_container_width=True)

    # Titles & Meta
    with tabs[3]:
        st.subheader("Content Tags")
        cols = ['url', 'title', 'title_length', 'meta_description', 'meta_desc_length']
        st.dataframe(df[[c for c in cols if c in df]], use_container_width=True)

    # Headers
    with tabs[4]:
        st.subheader("Heading Structure")
        st.dataframe(df[['url', 'h1_tags', 'h2_tags', 'h1_count']], use_container_width=True)

    # SCHEMA VALIDATOR (FIXED)
    with tabs[5]:
        st.subheader("🏗️ Schema Validation")
        
        # Overview Table
        s_df = df[['url', 'schema_types', 'schema_validity', 'schema_errors']].copy()
        
        def color_schema(val):
            color = '#ffcccc' if 'Error' in val or 'Invalid' in val else '#ccffcc' if val == 'Valid' else '#fff'
            return f'background-color: {color}'
        
        st.dataframe(s_df.style.applymap(color_schema, subset=['schema_validity']), use_container_width=True)
        
        # Raw Data Inspector
        with st.expander("🔍 Inspect Raw Schema JSON"):
            selected_url = st.selectbox("Select Page to Inspect", df['url'].tolist())
            if selected_url:
                row = df[df['url'] == selected_url].iloc[0]
                if row['schema_raw']:
                    st.code(row['schema_raw'], language='json')
                else:
                    st.warning("No Schema found on this page.")

    # PSI Speed
    with tabs[6]:
        st.subheader("⚡ Core Web Vitals")
        if psi_key:
            targets = st.multiselect("Select URLs to Test", df['url'].head(10).tolist())
            if st.button("Run PageSpeed"):
                res = []
                bar = st.progress(0)
                for i, u in enumerate(targets):
                    data = run_psi_test(u, psi_key)
                    data['url'] = u
                    res.append(data)
                    bar.progress((i+1)/len(targets))
                st.session_state.psi_results = res
            
            if st.session_state.psi_results:
                psi_df = pd.DataFrame(st.session_state.psi_results)
                st.dataframe(psi_df, use_container_width=True)
        else: st.warning("Please enter Google API Key in Sidebar")

    # Status
    with tabs[7]:
        st.subheader("Status Codes")
        st.dataframe(df[['url', 'status_code']], use_container_width=True)

    # Redirects
    with tabs[8]:
        st.subheader("Redirect Chains")
        if 'redirect_chain' in df.columns:
            # Flatten for display
            red_rows = []
            for _, row in df.iterrows():
                if row['redirect_count'] > 0:
                    red_rows.append({
                        'Original': row['url'],
                        'Chain Length': row['redirect_count'],
                        'Chain Details': str(row['redirect_chain'])
                    })
            if red_rows: st.dataframe(pd.DataFrame(red_rows), use_container_width=True)
            else: st.success("No redirects found.")

    # Canonicals
    with tabs[9]:
        st.subheader("Canonical Checks")
        st.dataframe(df[['url', 'canonical_url']], use_container_width=True)

    # Social
    with tabs[10]:
        st.subheader("Open Graph / Twitter")
        st.dataframe(df[['url', 'og_title', 'twitter_title']], use_container_width=True)

    # Orphans
    with tabs[11]:
        st.subheader("Orphan Pages")
        crawled = set(df['url'])
        orphans = list(st.session_state.sitemap_urls_set - crawled) if st.session_state.sitemap_urls_set else []
        if orphans:
            st.dataframe(pd.DataFrame(orphans, columns=['Orphan URL']), use_container_width=True)
        else: st.info("No orphans detected (Ensure Sitemap is provided).")

    # Custom
    with tabs[12]:
        st.subheader("Custom Extraction")
        st.dataframe(df[['url', 'custom_extraction']], use_container_width=True)

    # 3. DOWNLOAD CENTER (SEPARATE BUTTONS)
    st.markdown("### 📥 Download Reports")
    
    # Helper to safe download
    def convert_df(dataframe):
        return dataframe.to_csv(index=False).encode('utf-8')

    d1, d2, d3, d4 = st.columns(4)
    
    with d1:
        # Re-generate internal link DF for download
        l_rows = []
        for _, r in df.iterrows():
            for l in r.get('internal_links', []):
                l_rows.append({'Source': r['url'], 'Dest': l['url'], 'Anchor': l['anchor_text']})
        
        st.download_button("🔗 Internal Links", convert_df(pd.DataFrame(l_rows)), "internal_links.csv", "text/csv")
        st.download_button("📝 Titles", convert_df(df[['url', 'title', 'title_length']]), "titles.csv", "text/csv")
        st.download_button("🎯 Canonicals", convert_df(df[['url', 'canonical_url']]), "canonicals.csv", "text/csv")
        st.download_button("👻 Orphans", convert_df(pd.DataFrame(orphans, columns=['Url'])), "orphans.csv", "text/csv")

    with d2:
        # Re-generate external DF
        e_rows = []
        for _, r in df.iterrows():
            for l in r.get('external_links', []):
                e_rows.append({'Source': r['url'], 'Dest': l['url'], 'Anchor': l['anchor_text']})
                
        st.download_button("🌐 External Links", convert_df(pd.DataFrame(e_rows)), "external.csv", "text/csv")
        st.download_button("📄 Meta Desc", convert_df(df[['url', 'meta_description']]), "meta.csv", "text/csv")
        st.download_button("📱 Social", convert_df(df[['url', 'og_title']]), "social.csv", "text/csv")
        st.download_button("⛏️ Custom Data", convert_df(df[['url', 'custom_extraction']]), "custom.csv", "text/csv")

    with d3:
        # Re-generate Image DF
        i_rows = []
        for _, r in df.iterrows():
            for i in r.get('images', []):
                i_rows.append({'Source': r['url'], 'Img': i['src'], 'Alt': i['alt']})
                
        st.download_button("🖼️ Images", convert_df(pd.DataFrame(i_rows)), "images.csv", "text/csv")
        st.download_button("🏷️ Headers", convert_df(df[['url', 'h1_tags', 'h2_tags']]), "headers.csv", "text/csv")
        st.download_button("🚀 Performance", convert_df(df[['url', 'response_time', 'word_count']]), "perf.csv", "text/csv")

    with d4:
        st.download_button("🔄 Redirects", convert_df(df[df['redirect_count']>0]), "redirects.csv", "text/csv")
        st.download_button("📊 Status Codes", convert_df(df[['url', 'status_code']]), "status.csv", "text/csv")
        st.download_button("🏗️ Schema", convert_df(df[['url', 'schema_types', 'schema_validity']]), "schema.csv", "text/csv")
        
    st.markdown("---")
    st.download_button("📦 DOWNLOAD FULL RAW DATASET", convert_df(df), "full_crawl_data.csv", "text/csv", use_container_width=True)

else:
    st.info("Ready. Configure settings in the sidebar and click 'Run'.")
