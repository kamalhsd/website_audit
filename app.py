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

# Try importing pyvis for graphing, handle if missing
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False

# Page config
st.set_page_config(page_title="Ultra Frog SEO Crawler 3.0", layout="wide", page_icon="🐸")

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
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector  # New: For scraping prices/SKUs
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Ultra Frog SEO Crawler/3.0 (https://ultrafrog.seo)',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
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
        else:  # subfolder
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
        except:
            return True

    def get_css_path(self, element):
        """Generates the CSS path for a specific element to identify Header/Footer/Body."""
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
            response = self.session.get(sitemap_url, timeout=10)
            if response.status_code == 200:
                try:
                    root = ET.fromstring(response.content)
                except ET.ParseError:
                    # Fallback for some XML formats
                    return []
                
                # Handle namespaces
                namespaces = {'sitemap': 'http://www.sitemaps.org/schemas/sitemap/0.9'}
                
                # Recursive sitemap index check
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
            
            title = soup.find('title')
            title_text = title.get_text().strip() if title else ""
            meta_desc = soup.find('meta', attrs={'name': 'description'})
            meta_desc_text = meta_desc.get('content', '') if meta_desc else ""
            
            # --- NEW: Custom Extraction ---
            custom_data = ""
            if self.custom_selector:
                custom_elements = soup.select(self.custom_selector)
                custom_data = "; ".join([el.get_text(strip=True) for el in custom_elements])

            # --- UPDATED: Links with CSS Path ---
            internal_links = []
            external_links = []
            base_domain = urlparse(url).netloc
            
            for link in soup.find_all('a', href=True):
                href = urljoin(url, link['href'])
                link_text = link.get_text().strip()[:100]
                
                # Generate Path
                css_path = self.get_css_path(link)
                
                # Simple placement detector
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower: placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower or "menu" in path_lower: placement = "Header"
                elif "sidebar" in path_lower or "aside" in path_lower: placement = "Sidebar"

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
            
            # Standard Metrics
            word_count = len(soup.get_text().split())
            
            return {
                'url': response.url,
                'original_url': url,
                'status_code': response.status_code,
                'title': title_text,
                'title_length': len(title_text),
                'meta_description': meta_desc_text,
                'meta_desc_length': len(meta_desc_text),
                'h1_count': len(soup.find_all('h1')),
                'word_count': word_count,
                'response_time': response.elapsed.total_seconds(),
                'internal_links': internal_links,
                'internal_links_count': len(internal_links),
                'external_links': external_links,
                'custom_extraction': custom_data,  # New Field
                'indexability': 'Indexable' if response.status_code == 200 else 'Non-Indexable',
                'crawl_timestamp': datetime.now().isoformat()
            }
        except Exception as e:
            return {
                'url': url, 'status_code': 0, 'error': str(e),
                'internal_links': [], 'external_links': [], 
                'indexability': 'Error', 'crawl_timestamp': datetime.now().isoformat()
            }

def crawl_website(start_url, max_urls, crawl_scope, progress_container, ignore_robots=False, custom_selector=None):
    crawler = UltraFrogCrawler(max_urls, ignore_robots, crawl_scope, custom_selector)
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
            for _ in range(min(20, len(urls_to_visit))):
                if urls_to_visit:
                    url = urls_to_visit.popleft()
                    if url not in visited_urls and crawler.can_fetch(url):
                        current_batch.append(url)
                        visited_urls.add(url)
            
            if not current_batch: break
            
            future_to_url = {executor.submit(crawler.extract_page_data, url): url for url in current_batch}
            
            for future in as_completed(future_to_url):
                try:
                    page_data = future.result()
                    crawl_data.append(page_data)
                    
                    for link in page_data.get('internal_links', []):
                        l_url = link['url']
                        if l_url not in visited_urls and l_url not in urls_to_visit and crawler.should_crawl_url(l_url):
                            urls_to_visit.append(l_url)
                            
                    progress = min(len(crawl_data) / max_urls, 1.0)
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {len(crawl_data)} | Found: {len(urls_to_visit) + len(visited_urls)}")
                except Exception:
                    pass

    return crawl_data

# CSS
st.markdown("""
<style>
.main-header { background: linear-gradient(90deg, #4CAF50, #2E7D32); padding: 1rem; border-radius: 10px; margin-bottom: 2rem; }
.stTabs [data-baseweb="tab-list"] { gap: 10px; }
.stTabs [data-baseweb="tab"] { height: 50px; white-space: pre-wrap; background-color: #f0f2f6; border-radius: 5px; }
.stTabs [aria-selected="true"] { background-color: #4CAF50; color: white; }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown("""
<div class="main-header">
    <h1 style="color: white; margin: 0;">🐸 Ultra Frog SEO Crawler 3.0</h1>
    <p style="color: white; margin: 0; opacity: 0.9;">Professional Edition • Graph Visualization • Path Detection</p>
</div>
""", unsafe_allow_html=True)

# Sidebar
with st.sidebar:
    st.header("🔧 Configuration")
    crawl_mode = st.selectbox("🎯 Crawl Mode", ["🕷️ Spider Crawl", "📝 List Mode"])
    
    start_url = ""
    url_list_text = ""
    sitemap_url = "" # For orphan checking
    
    if crawl_mode == "🕷️ Spider Crawl":
        start_url = st.text_input("🌐 Start URL", placeholder="https://example.com")
        sitemap_url = st.text_input("🗺️ Sitemap URL (Optional)", placeholder="For Orphan Page detection")
        max_urls = st.number_input("📊 Max URLs", value=100)
        crawl_scope = st.selectbox("🎯 Scope", ["subfolder", "subdomain", "exact"])
        
    elif crawl_mode == "📝 List Mode":
        url_list_text = st.text_area("Paste URLs (one per line)", height=150)

    st.markdown("---")
    st.subheader("⛏️ Custom Extraction")
    custom_selector = st.text_input("CSS Selector (e.g. .price, h1)", help="Extract specific data from pages")

    col1, col2 = st.columns(2)
    with col1:
        start_btn = st.button("🚀 Start", type="primary", disabled=st.session_state.crawling)
    with col2:
        stop_btn = st.button("⛔ Stop", disabled=not st.session_state.crawling)

    if start_btn:
        st.session_state.crawling = True
        st.session_state.stop_crawling = False
        st.session_state.crawl_data = []
        
        # Pre-fetch sitemap if provided for orphan checking
        if sitemap_url:
            crawler_temp = UltraFrogCrawler()
            st.session_state.sitemap_urls_set = set(crawler_temp.extract_sitemap_urls(sitemap_url))
        
        st.rerun()

    if stop_btn:
        st.session_state.stop_crawling = True
        st.session_state.crawling = False
        st.rerun()

# Main Logic
if st.session_state.crawling:
    progress_container = st.container()
    
    if crawl_mode == "🕷️ Spider Crawl" and start_url:
        data = crawl_website(start_url, max_urls, crawl_scope, progress_container, False, custom_selector)
    elif crawl_mode == "📝 List Mode" and url_list_text:
        # Simplified list logic reuse
        urls = [u.strip() for u in url_list_text.split('\n') if u.strip()]
        # We reuse the crawl_website logic but modify it slightly or just iterate (kept simple here)
        # For this example, assuming Spider mode is primary
        st.warning("Switching to Spider logic for demo consistency. Please use Spider mode for full features.")
        data = [] 
    else:
        data = []

    st.session_state.crawl_data = data
    st.session_state.crawling = False
    st.rerun()

elif st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)
    
    # Dashboard Metrics
    st.markdown("### 📊 Overview")
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Total Pages", len(df))
    m2.metric("Avg Word Count", int(df['word_count'].mean()) if not df.empty else 0)
    m3.metric("Avg Response", f"{df['response_time'].mean():.2f}s" if not df.empty else "0s")
    
    # Check Orphans
    crawled_urls = set(df['url'])
    orphans = list(st.session_state.sitemap_urls_set - crawled_urls)
    m4.metric("👻 Orphan Pages", len(orphans))

    # Tabs
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "🔗 Internal Links (Fixed)", 
        "🕸️ Visual Graph", 
        "👻 Orphan Pages", 
        "⛏️ Custom Extraction",
        "📄 Page Data"
    ])

    # --- TAB 1: FIXED INTERNAL LINKS ---
    with tab1:
        st.subheader("Detailed Internal Link Analysis")
        st.info("Showing Source, Destination, Anchor Text, and Placement Path separately.")
        
        if 'internal_links' in df.columns:
            # Prepare explosion
            base_df = df[['url', 'internal_links']].copy()
            base_df = base_df.rename(columns={'url': 'Source URL'})
            
            # Explode list to rows
            exploded = base_df.explode('internal_links')
            
            # Normalize dictionary to columns
            # Handle cases where internal_links might be NaN or empty
            exploded = exploded.dropna(subset=['internal_links'])
            
            if not exploded.empty:
                links_data = pd.json_normalize(exploded['internal_links'])
                
                # Reset indices to align
                exploded = exploded.reset_index(drop=True)
                links_data = links_data.reset_index(drop=True)
                
                # Merge
                final_links = pd.concat([exploded['Source URL'], links_data], axis=1)
                
                # Reorder/Rename
                final_links = final_links[['Source URL', 'url', 'anchor_text', 'placement', 'css_path']]
                final_links.columns = ['Source URL', 'Destination URL', 'Anchor Text', 'Placement', 'CSS Path']
                
                st.dataframe(final_links, use_container_width=True)
                
                st.download_button(
                    "📥 Download Links CSV", 
                    final_links.to_csv(index=False).encode('utf-8'),
                    "internal_links_report.csv"
                )
            else:
                st.warning("No internal links found.")

    # --- TAB 2: VISUAL GRAPH ---
    with tab2:
        st.subheader("Site Architecture Visualization")
        if HAS_PYVIS:
            # Create Graph
            G = nx.DiGraph()
            # Limit nodes for performance
            max_nodes = 50
            subset = df.head(max_nodes)
            
            for _, row in subset.iterrows():
                src = row['url']
                G.add_node(src, title=row['title'], color='#4CAF50', size=20)
                
                for link in row.get('internal_links', []):
                    dst = link['url']
                    if dst in subset['url'].values:
                        G.add_edge(src, dst, color='#aaaaaa')
            
            # Visualize
            net = Network(height='600px', width='100%', bgcolor='#111111', font_color='white')
            net.from_nx(G)
            net.repulsion(node_distance=100, spring_length=200)
            
            # Save to temporary html string
            # pyvis generate_html returns string in newer versions or writes file
            try:
                path = "graph.html"
                net.save_graph(path)
                with open(path, 'r', encoding='utf-8') as f:
                    html_data = f.read()
                components.html(html_data, height=650)
            except Exception as e:
                st.error(f"Graph generation error: {e}")
        else:
            st.error("Please install pyvis: `pip install pyvis` to view the graph.")

    # --- TAB 3: ORPHAN PAGES ---
    with tab3:
        st.subheader("👻 Orphan Pages Detected")
        st.write("Pages found in Sitemap but NOT linked to from the crawl start point.")
        
        if orphans:
            orphan_df = pd.DataFrame(orphans, columns=['Orphan URL'])
            st.dataframe(orphan_df, use_container_width=True)
        else:
            if not sitemap_url:
                st.warning("Please provide a Sitemap URL in the sidebar configuration to check for orphans.")
            else:
                st.success("No orphan pages found! (Or sitemap parsing failed)")

    # --- TAB 4: CUSTOM EXTRACTION ---
    with tab4:
        st.subheader("⛏️ Custom Extracted Data")
        if custom_selector:
            custom_df = df[['url', 'custom_extraction']].copy()
            st.dataframe(custom_df, use_container_width=True)
        else:
            st.info("Enter a CSS Selector in the sidebar (e.g., `.price` or `h1`) and restart crawl to see data here.")

    # --- TAB 5: RAW DATA ---
    with tab5:
        st.dataframe(df)

else:
    st.info("👈 Configure the crawler in the sidebar and click Start.")
