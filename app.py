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
import streamlit.components.v1 as components

import networkx as nx

# Optional graph rendering (pyvis)
try:
    from pyvis.network import Network
    HAS_PYVIS = True
except ImportError:
    HAS_PYVIS = False


# -----------------------------
# Page config + session
# -----------------------------
st.set_page_config(page_title="Ultra Frog SEO Crawler 3.1", layout="wide", page_icon="🐸")

if "crawl_data" not in st.session_state:
    st.session_state.crawl_data = []
if "crawling" not in st.session_state:
    st.session_state.crawling = False
if "stop_crawling" not in st.session_state:
    st.session_state.stop_crawling = False
if "start_time" not in st.session_state:
    st.session_state.start_time = None
if "sitemap_urls_set" not in st.session_state:
    st.session_state.sitemap_urls_set = set()
if "crawl_params" not in st.session_state:
    st.session_state.crawl_params = {}


# -----------------------------
# Crawler
# -----------------------------
class UltraFrogCrawler:
    def __init__(self, max_urls=100000, ignore_robots=False, crawl_scope="subfolder", custom_selector=None):
        self.max_urls = max_urls
        self.ignore_robots = ignore_robots
        self.crawl_scope = crawl_scope
        self.custom_selector = custom_selector

        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "Ultra Frog SEO Crawler/3.1 (https://ultrafrog.seo)",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Encoding": "gzip, deflate",
            "Connection": "keep-alive",
            "Upgrade-Insecure-Requests": "1"
        })

        adapter = requests.adapters.HTTPAdapter(pool_connections=25, pool_maxsize=25, max_retries=1)
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)

        self.robots_cache = {}
        self.base_domain = None
        self.base_path = None

    def set_base_url(self, url):
        parsed = urlparse(url)
        self.base_domain = parsed.netloc
        self.base_path = parsed.path.rstrip("/") or "/"

    def should_crawl_url(self, url):
        parsed = urlparse(url)

        if not parsed.scheme.startswith("http"):
            return False

        if self.crawl_scope == "exact":
            return url.rstrip("/") == urljoin(f"https://{self.base_domain}", self.base_path).rstrip("/")
        elif self.crawl_scope == "subdomain":
            return self.base_domain in parsed.netloc
        else:  # subfolder
            return (parsed.netloc == self.base_domain and parsed.path.startswith(self.base_path))

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

            rp = self.robots_cache.get(domain)
            if rp is None:
                return True
            return rp.can_fetch("*", url)
        except:
            return True

    def get_css_path(self, element):
        """Generates CSS-ish path to help detect Header/Footer/Body for link placement."""
        path = []
        for parent in element.parents:
            if parent.name == "[document]":
                break
            selector = parent.name
            if parent.get("id"):
                selector += f"#{parent['id']}"
            elif parent.get("class"):
                selector += f".{parent.get('class')[0]}"
            path.append(selector)
        path.reverse()

        element_selector = element.name
        if element.get("class"):
            element_selector += f".{element.get('class')[0]}"
        path.append(element_selector)

        return " > ".join(path)

    def extract_sitemap_urls(self, sitemap_url):
        urls = []
        try:
            resp = self.session.get(sitemap_url, timeout=10)
            if resp.status_code != 200:
                return urls

            try:
                root = ET.fromstring(resp.content)
            except ET.ParseError:
                return urls

            ns = {"sitemap": "http://www.sitemaps.org/schemas/sitemap/0.9"}

            sitemapindex = root.findall(".//sitemap:sitemap", ns)
            if sitemapindex:
                for sitemap in sitemapindex:
                    loc = sitemap.find("sitemap:loc", ns)
                    if loc is not None and loc.text:
                        urls.extend(self.extract_sitemap_urls(loc.text.strip()))
                return urls

            for url_elem in root.findall(".//sitemap:url", ns):
                loc = url_elem.find("sitemap:loc", ns)
                if loc is not None and loc.text:
                    urls.append(loc.text.strip())
        except Exception:
            pass
        return urls

    def get_indexability_status(self, status_code, robots_content):
        if status_code != 200:
            return "Non-Indexable"
        if robots_content and "noindex" in robots_content.lower():
            return "Non-Indexable"
        return "Indexable"

    def extract_page_data(self, url):
        """FULL v2 extraction restored + v3 link placement + custom extraction."""
        try:
            response = self.session.get(url, timeout=10, allow_redirects=True)
            final_url = response.url
            soup = BeautifulSoup(response.content, "html.parser")

            # Basic SEO
            title_tag = soup.find("title")
            title_text = title_tag.get_text(strip=True) if title_tag else ""

            meta_desc = soup.find("meta", attrs={"name": "description"})
            meta_desc_text = meta_desc.get("content", "").strip() if meta_desc else ""

            canonical = soup.find("link", attrs={"rel": "canonical"})
            canonical_url = canonical.get("href", "").strip() if canonical else ""

            meta_robots = soup.find("meta", attrs={"name": "robots"})
            robots_content = meta_robots.get("content", "").strip() if meta_robots else ""

            # Social tags
            og_title = soup.find("meta", attrs={"property": "og:title"})
            og_desc = soup.find("meta", attrs={"property": "og:description"})
            og_image = soup.find("meta", attrs={"property": "og:image"})

            twitter_title = soup.find("meta", attrs={"name": "twitter:title"})
            twitter_desc = soup.find("meta", attrs={"name": "twitter:description"})
            twitter_image = soup.find("meta", attrs={"name": "twitter:image"})

            # Headers
            h1_tags = [h.get_text(strip=True) for h in soup.find_all("h1")]
            h2_tags = [h.get_text(strip=True) for h in soup.find_all("h2")]
            h3_tags = [h.get_text(strip=True) for h in soup.find_all("h3")]
            h4_tags = [h.get_text(strip=True) for h in soup.find_all("h4")]

            # Links with placement
            internal_links = []
            external_links = []
            base_domain = urlparse(final_url).netloc

            for link in soup.find_all("a", href=True):
                href = urljoin(final_url, link.get("href", ""))
                if not href:
                    continue
                if href.startswith("mailto:") or href.startswith("tel:") or href.startswith("javascript:"):
                    continue

                link_text = link.get_text(strip=True)[:100]
                css_path = self.get_css_path(link)
                placement = "Body"
                path_lower = css_path.lower()
                if "footer" in path_lower:
                    placement = "Footer"
                elif "header" in path_lower or "nav" in path_lower or "menu" in path_lower:
                    placement = "Header"
                elif "sidebar" in path_lower or "aside" in path_lower:
                    placement = "Sidebar"

                link_data = {"url": href, "anchor_text": link_text, "css_path": css_path, "placement": placement}

                if urlparse(href).netloc == base_domain:
                    internal_links.append(link_data)
                else:
                    external_links.append(link_data)

            # Images
            images = []
            for img in soup.find_all("img"):
                img_src = urljoin(final_url, img.get("src", ""))
                images.append({
                    "src": img_src,
                    "alt": img.get("alt", ""),
                    "title": img.get("title", ""),
                    "width": img.get("width", ""),
                    "height": img.get("height", "")
                })

            # Schema types
            schema_types = []
            for script in soup.find_all("script", type="application/ld+json"):
                try:
                    if script.string:
                        data = json.loads(script.string)
                        if isinstance(data, dict) and "@type" in data:
                            schema_types.append(str(data["@type"]))
                        elif isinstance(data, list):
                            for item in data:
                                if isinstance(item, dict) and "@type" in item:
                                    schema_types.append(str(item["@type"]))
                except:
                    pass

            # Performance indicators
            css_files = len(soup.find_all("link", attrs={"rel": "stylesheet"}))
            js_files = len(soup.find_all("script", src=True))

            text_content = soup.get_text(" ")
            word_count = len(text_content.split())

            # Redirect chain
            redirect_chain = []
            if getattr(response, "history", None):
                for i, resp in enumerate(response.history):
                    redirect_chain.append({
                        "step": i + 1,
                        "from_url": resp.url,
                        "to_url": resp.headers.get("location", ""),
                        "status_code": resp.status_code,
                        "redirect_type": "301 Permanent" if resp.status_code == 301 else
                                         "302 Temporary" if resp.status_code == 302 else
                                         f"{resp.status_code} Redirect"
                    })

            # Custom extraction
            custom_data = ""
            if self.custom_selector:
                try:
                    els = soup.select(self.custom_selector)
                    custom_data = "; ".join([el.get_text(strip=True) for el in els])
                except:
                    custom_data = ""

            # Indexability
            indexability = self.get_indexability_status(response.status_code, robots_content)

            return {
                "url": final_url,
                "original_url": url,
                "status_code": response.status_code,

                "title": title_text,
                "title_length": len(title_text),

                "meta_description": meta_desc_text,
                "meta_desc_length": len(meta_desc_text),

                "canonical_url": canonical_url,
                "meta_robots": robots_content,

                "h1_tags": "; ".join(h1_tags),
                "h1_count": len(h1_tags),
                "h2_tags": "; ".join(h2_tags),
                "h2_count": len(h2_tags),
                "h3_tags": "; ".join(h3_tags),
                "h3_count": len(h3_tags),
                "h4_tags": "; ".join(h4_tags),
                "h4_count": len(h4_tags),

                "word_count": word_count,
                "response_time": response.elapsed.total_seconds(),
                "content_length": len(response.content),

                "internal_links": internal_links,
                "external_links": external_links,
                "internal_links_count": len(internal_links),
                "external_links_count": len(external_links),

                "images": images,
                "image_count": len(images),
                "images_without_alt": len([im for im in images if not im.get("alt")]),

                "schema_types": "; ".join(schema_types),
                "schema_count": len(schema_types),

                "redirect_chain": redirect_chain,
                "redirect_count": len(redirect_chain),

                "css_files": css_files,
                "js_files": js_files,

                "og_title": og_title.get("content", "") if og_title else "",
                "og_description": og_desc.get("content", "") if og_desc else "",
                "og_image": og_image.get("content", "") if og_image else "",
                "twitter_title": twitter_title.get("content", "") if twitter_title else "",
                "twitter_description": twitter_desc.get("content", "") if twitter_desc else "",
                "twitter_image": twitter_image.get("content", "") if twitter_image else "",

                "content_type": response.headers.get("content-type", ""),
                "last_modified": response.headers.get("last-modified", ""),
                "server": response.headers.get("server", ""),

                "custom_extraction": custom_data,

                "indexability": indexability,
                "crawl_timestamp": datetime.now().isoformat()
            }

        except Exception as e:
            return {
                "url": url,
                "original_url": url,
                "status_code": 0,
                "error": str(e),

                "title": "",
                "title_length": 0,
                "meta_description": "",
                "meta_desc_length": 0,
                "canonical_url": "",
                "meta_robots": "",

                "h1_tags": "",
                "h1_count": 0,
                "h2_tags": "",
                "h2_count": 0,
                "h3_tags": "",
                "h3_count": 0,
                "h4_tags": "",
                "h4_count": 0,

                "word_count": 0,
                "response_time": 0,
                "content_length": 0,

                "internal_links": [],
                "external_links": [],
                "internal_links_count": 0,
                "external_links_count": 0,

                "images": [],
                "image_count": 0,
                "images_without_alt": 0,

                "schema_types": "",
                "schema_count": 0,

                "redirect_chain": [],
                "redirect_count": 0,

                "css_files": 0,
                "js_files": 0,

                "og_title": "",
                "og_description": "",
                "og_image": "",
                "twitter_title": "",
                "twitter_description": "",
                "twitter_image": "",

                "content_type": "",
                "last_modified": "",
                "server": "",

                "custom_extraction": "",
                "indexability": "Error",
                "crawl_timestamp": datetime.now().isoformat()
            }


# -----------------------------
# Crawl runners
# -----------------------------
def normalize_url(u: str) -> str:
    u = u.strip()
    if not u:
        return ""
    if not u.startswith("http://") and not u.startswith("https://"):
        u = "https://" + u
    return u

def crawl_spider(start_url, max_urls, crawl_scope, progress_container, ignore_robots, custom_selector):
    crawler = UltraFrogCrawler(max_urls=max_urls, ignore_robots=ignore_robots, crawl_scope=crawl_scope, custom_selector=custom_selector)
    crawler.set_base_url(start_url)

    urls_to_visit = deque([start_url])
    visited = set()
    crawl_data = []

    progress_bar = progress_container.progress(0.0)
    status_text = progress_container.empty()

    start_time = st.session_state.start_time or time.time()

    with ThreadPoolExecutor(max_workers=12) as executor:
        while urls_to_visit and len(visited) < max_urls:
            if st.session_state.stop_crawling:
                break

            current_batch = []
            batch_size = min(25, len(urls_to_visit), max_urls - len(visited))
            for _ in range(batch_size):
                if st.session_state.stop_crawling:
                    break
                u = urls_to_visit.popleft()
                if u in visited:
                    continue
                if not crawler.can_fetch(u):
                    visited.add(u)
                    continue
                current_batch.append(u)
                visited.add(u)

            if not current_batch:
                break

            future_map = {executor.submit(crawler.extract_page_data, u): u for u in current_batch}

            for fut in as_completed(future_map):
                if st.session_state.stop_crawling:
                    for f in future_map:
                        f.cancel()
                    break

                try:
                    page_data = fut.result(timeout=15)
                    crawl_data.append(page_data)

                    # enqueue internal links
                    for link in page_data.get("internal_links", []):
                        link_url = normalize_url(link.get("url", ""))
                        if not link_url:
                            continue
                        if link_url in visited or link_url in urls_to_visit:
                            continue
                        if crawler.should_crawl_url(link_url) and (len(visited) + len(urls_to_visit) < max_urls):
                            urls_to_visit.append(link_url)

                    # progress
                    progress = min(len(crawl_data) / max_urls, 1.0)
                    elapsed = max(1e-6, time.time() - start_time)
                    speed = len(crawl_data) / elapsed
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Crawled: {len(crawl_data)} | Queue: {len(urls_to_visit)} | Speed: {speed:.1f} URLs/sec")
                except Exception:
                    pass

    return crawl_data

def crawl_list(url_list, progress_container, ignore_robots, custom_selector):
    urls = [normalize_url(u) for u in url_list]
    urls = [u for u in urls if u]
    if not urls:
        return []

    crawler = UltraFrogCrawler(max_urls=len(urls), ignore_robots=ignore_robots, crawl_scope="subdomain", custom_selector=custom_selector)

    progress_bar = progress_container.progress(0.0)
    status_text = progress_container.empty()

    start_time = st.session_state.start_time or time.time()
    crawl_data = []

    with ThreadPoolExecutor(max_workers=15) as executor:
        for i in range(0, len(urls), 30):
            if st.session_state.stop_crawling:
                break

            batch = urls[i:i+30]
            future_map = {executor.submit(crawler.extract_page_data, u): u for u in batch}

            for fut in as_completed(future_map):
                if st.session_state.stop_crawling:
                    for f in future_map:
                        f.cancel()
                    break
                try:
                    page_data = fut.result(timeout=15)
                    crawl_data.append(page_data)

                    progress = min(len(crawl_data) / len(urls), 1.0)
                    elapsed = max(1e-6, time.time() - start_time)
                    speed = len(crawl_data) / elapsed
                    progress_bar.progress(progress)
                    status_text.text(f"🚀 Processed: {len(crawl_data)}/{len(urls)} | Speed: {speed:.1f} URLs/sec")
                except Exception:
                    pass

    return crawl_data

def crawl_sitemap(sitemap_url, max_urls, progress_container, ignore_robots, custom_selector):
    crawler = UltraFrogCrawler(max_urls=max_urls, ignore_robots=ignore_robots)
    urls = crawler.extract_sitemap_urls(sitemap_url)
    urls = [normalize_url(u) for u in urls]
    urls = [u for u in urls if u]
    if not urls:
        return []
    if len(urls) > max_urls:
        urls = urls[:max_urls]
    return crawl_list(urls, progress_container, ignore_robots, custom_selector)


# -----------------------------
# UI styling
# -----------------------------
st.markdown("""
<style>
.main-header {
    background: linear-gradient(90deg, #4CAF50, #2E7D32);
    padding: 1rem;
    border-radius: 10px;
    margin-bottom: 1.5rem;
}
.stTabs [data-baseweb="tab-list"] { gap: 10px; }
.stTabs [data-baseweb="tab"] {
    height: 48px;
    white-space: pre-wrap;
    background-color: #f0f2f6;
    border-radius: 8px;
}
.stTabs [aria-selected="true"] { background-color: #4CAF50 !important; color: white !important; }
</style>
""", unsafe_allow_html=True)

st.markdown("""
<div class="main-header">
    <h1 style="color: white; margin: 0;">🐸 Ultra Frog SEO Crawler 3.1</h1>
    <p style="color: white; margin: 0; opacity: 0.9;">v2 SEO Tabs Restored + v3 Interlinking + Graph + Orphans + Custom Extraction</p>
</div>
""", unsafe_allow_html=True)


# -----------------------------
# Sidebar controls
# -----------------------------
with st.sidebar:
    st.header("🔧 Crawl Configuration")

    crawl_mode = st.selectbox("🎯 Crawl Mode", [
        "🕷️ Spider Crawl (Follow Links)",
        "📝 List Mode (Paste/Upload URLs)",
        "🗺️ Sitemap Crawl (XML Sitemap)"
    ])

    start_url = ""
    sitemap_url = ""
    max_urls = 500
    crawl_scope = "subfolder"
    url_list_text = ""
    uploaded_file = None

    if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
        start_url = st.text_input("🌐 Start URL", placeholder="https://example.com")
        sitemap_url = st.text_input("🗺️ Sitemap URL (Optional - Orphan check)", placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs to crawl", min_value=1, max_value=100000, value=500)
        crawl_scope = st.selectbox("🎯 Crawl Scope", ["subfolder", "subdomain", "exact"])

    elif crawl_mode == "📝 List Mode (Paste/Upload URLs)":
        uploaded_file = st.file_uploader("Upload URL file", type=["txt", "csv"])
        url_list_text = st.text_area("Or paste URLs (one per line)", height=150)
        sitemap_url = st.text_input("🗺️ Sitemap URL (Optional - Orphan check)", placeholder="https://example.com/sitemap.xml")

    else:  # sitemap mode
        sitemap_url = st.text_input("🗺️ Sitemap URL", placeholder="https://example.com/sitemap.xml")
        max_urls = st.number_input("📊 Max URLs from sitemap", min_value=1, max_value=100000, value=5000)

    st.markdown("---")
    st.subheader("⛏️ Custom Extraction")
    custom_selector = st.text_input("CSS Selector (e.g. .price, h1)", help="Extract specific elements from pages")

    ignore_robots = st.checkbox("🤖 Ignore robots.txt")

    c1, c2 = st.columns(2)
    with c1:
        start_btn = st.button("🚀 Start Crawl", type="primary", disabled=st.session_state.crawling)
    with c2:
        stop_btn = st.button("⛔ Stop", disabled=not st.session_state.crawling)

    if stop_btn:
        st.session_state.stop_crawling = True
        st.session_state.crawling = False
        st.rerun()

    if st.button("🗑️ Clear Data"):
        st.session_state.crawl_data = []
        st.session_state.sitemap_urls_set = set()
        st.session_state.crawl_params = {}
        st.rerun()

    if start_btn:
        # Validate input
        valid = False
        params = {
            "crawl_mode": crawl_mode,
            "ignore_robots": ignore_robots,
            "custom_selector": custom_selector,
            "crawl_scope": crawl_scope,
            "max_urls": int(max_urls) if max_urls else 500
        }

        if crawl_mode == "🕷️ Spider Crawl (Follow Links)":
            start_url_n = normalize_url(start_url)
            if start_url_n:
                params["start_url"] = start_url_n
                params["sitemap_url"] = normalize_url(sitemap_url) if sitemap_url else ""
                valid = True

        elif crawl_mode == "📝 List Mode (Paste/Upload URLs)":
            urls = []
            if uploaded_file:
                content = uploaded_file.read().decode("utf-8", errors="ignore")
                urls = [line.strip() for line in content.splitlines() if line.strip()]
            if url_list_text.strip():
                urls += [line.strip() for line in url_list_text.splitlines() if line.strip()]
            urls = list(dict.fromkeys(urls))  # de-dupe preserving order
            if urls:
                params["url_list"] = urls
                params["sitemap_url"] = normalize_url(sitemap_url) if sitemap_url else ""
                valid = True

        else:  # sitemap
            sitemap_n = normalize_url(sitemap_url)
            if sitemap_n:
                params["sitemap_url"] = sitemap_n
                valid = True

        if valid:
            st.session_state.crawling = True
            st.session_state.stop_crawling = False
            st.session_state.crawl_data = []
            st.session_state.start_time = time.time()
            st.session_state.crawl_params = params

            # Pre-fetch sitemap set (for orphan check) if provided
            orphan_sitemap = params.get("sitemap_url", "")
            if orphan_sitemap and crawl_mode != "🗺️ Sitemap Crawl (XML Sitemap)":
                try:
                    temp = UltraFrogCrawler(ignore_robots=ignore_robots)
                    st.session_state.sitemap_urls_set = set(temp.extract_sitemap_urls(orphan_sitemap))
                except:
                    st.session_state.sitemap_urls_set = set()

            st.rerun()
        else:
            st.error("Please provide valid input.")


# -----------------------------
# Run crawl when active
# -----------------------------
if st.session_state.crawling:
    st.header("🐸 Ultra Frog is Crawling...")
    progress_container = st.container()

    params = st.session_state.crawl_params or {}
    mode = params.get("crawl_mode", "")
    ignore_robots = params.get("ignore_robots", False)
    custom_selector = params.get("custom_selector", None)

    try:
        data = []
        if mode == "🕷️ Spider Crawl (Follow Links)":
            data = crawl_spider(
                start_url=params["start_url"],
                max_urls=params["max_urls"],
                crawl_scope=params.get("crawl_scope", "subfolder"),
                progress_container=progress_container,
                ignore_robots=ignore_robots,
                custom_selector=custom_selector
            )

        elif mode == "📝 List Mode (Paste/Upload URLs)":
            data = crawl_list(
                url_list=params.get("url_list", []),
                progress_container=progress_container,
                ignore_robots=ignore_robots,
                custom_selector=custom_selector
            )

        else:  # sitemap
            data = crawl_sitemap(
                sitemap_url=params.get("sitemap_url", ""),
                max_urls=params.get("max_urls", 5000),
                progress_container=progress_container,
                ignore_robots=ignore_robots,
                custom_selector=custom_selector
            )

        st.session_state.crawl_data = data if data else []
        st.session_state.crawling = False
        stopped = st.session_state.stop_crawling
        st.session_state.stop_crawling = False

        crawl_time = max(0.001, time.time() - (st.session_state.start_time or time.time()))
        if stopped:
            st.warning(f"⛔ Crawl stopped by user. Collected {len(st.session_state.crawl_data)} URLs.")
        else:
            st.success(f"✅ Crawl completed! Found {len(st.session_state.crawl_data)} URLs in {crawl_time:.1f}s "
                       f"({len(st.session_state.crawl_data)/crawl_time:.1f} URLs/sec)")

        st.rerun()

    except Exception as e:
        st.error(f"Error: {e}")
        st.session_state.crawling = False


# -----------------------------
# Display results
# -----------------------------
elif st.session_state.crawl_data:
    df = pd.DataFrame(st.session_state.crawl_data)

    st.header("📊 Ultra Frog Analysis Dashboard")
    c1, c2, c3, c4, c5 = st.columns(5)
    with c1:
        st.metric("Total URLs", len(df))
    with c2:
        st.metric("✅ Indexable", int((df.get("indexability") == "Indexable").sum()) if "indexability" in df.columns else 0)
    with c3:
        st.metric("❌ Non-Indexable", int((df.get("indexability") == "Non-Indexable").sum()) if "indexability" in df.columns else 0)
    with c4:
        st.metric("🔄 Redirects", int((df.get("redirect_count", 0) > 0).sum()) if "redirect_count" in df.columns else 0)
    with c5:
        st.metric("⚡ Avg Response", f"{df.get('response_time', pd.Series([0])).mean():.2f}s" if "response_time" in df.columns else "0.00s")

    # Orphan pages (if sitemap set loaded)
    crawled_urls = set(df["url"]) if "url" in df.columns else set()
    sitemap_set = st.session_state.sitemap_urls_set or set()
    orphans = list(set(sitemap_set) - crawled_urls) if sitemap_set else []

    # Tabs (RESTORED)
    tab_internal, tab_external, tab_images, tab_titles, tab_meta, tab_headers, tab_redirects, tab_status, tab_canon, tab_social, tab_perf, tab_graph, tab_orphan, tab_custom, tab_raw = st.tabs([
        "🔗 Internal (Interlinking)",
        "🌐 External",
        "🖼️ Images",
        "📝 Titles",
        "📄 Meta Desc",
        "🏷️ Headers",
        "🔄 Redirects",
        "📊 Status",
        "🎯 Canonicals",
        "📱 Social",
        "🚀 Performance",
        "🕸️ Visual Graph",
        "👻 Orphan Pages",
        "⛏️ Custom Extraction",
        "📄 Raw Data"
    ])

    # -------------------------
    # Internal (Interlinking)
    # -------------------------
    with tab_internal:
        st.subheader("Detailed Internal Link Analysis (Source → Destination)")
        if "internal_links" in df.columns:
            base_df = df[["url", "internal_links"]].copy().rename(columns={"url": "Source URL"})
            exploded = base_df.explode("internal_links").dropna(subset=["internal_links"])
            if not exploded.empty:
                links_data = pd.json_normalize(exploded["internal_links"]).reset_index(drop=True)
                exploded = exploded.reset_index(drop=True)
                final_links = pd.concat([exploded["Source URL"], links_data], axis=1)

                # keep only expected cols if present
                keep = [c for c in ["Source URL", "url", "anchor_text", "placement", "css_path"] if c in final_links.columns]
                final_links = final_links[keep].copy()
                final_links.columns = ["Source URL", "Destination URL", "Anchor Text", "Placement", "CSS Path"][:len(final_links.columns)]

                st.dataframe(final_links, use_container_width=True)
                st.download_button("📥 Download Internal Links CSV",
                                   final_links.to_csv(index=False).encode("utf-8"),
                                   "internal_links_report.csv", "text/csv")
            else:
                st.info("No internal links found.")
        else:
            st.warning("Internal link data not found in crawl output.")

    # -------------------------
    # External
    # -------------------------
    with tab_external:
        st.subheader("🌐 External Links Analysis")
        external_data = []
        if "external_links" in df.columns:
            for _, row in df.iterrows():
                for ext in row.get("external_links", []):
                    external_data.append({
                        "source_url": row.get("url", ""),
                        "destination_url": ext.get("url", ""),
                        "anchor_text": ext.get("anchor_text", ""),
                        "placement": ext.get("placement", ""),
                        "css_path": ext.get("css_path", "")
                    })
        if external_data:
            ext_df = pd.DataFrame(external_data)
            st.dataframe(ext_df, use_container_width=True)
            st.download_button("📥 Download External CSV",
                               ext_df.to_csv(index=False).encode("utf-8"),
                               "external_links_report.csv", "text/csv")
        else:
            st.info("No external links found.")

    # -------------------------
    # Images
    # -------------------------
    with tab_images:
        st.subheader("🖼️ Images Analysis")
        images_data = []
        if "images" in df.columns:
            for _, row in df.iterrows():
                for img in row.get("images", []):
                    images_data.append({
                        "source_url": row.get("url", ""),
                        "image_url": img.get("src", ""),
                        "alt_text": img.get("alt", ""),
                        "title": img.get("title", ""),
                        "dimensions": f"{img.get('width','')}x{img.get('height','')}".strip("x") or "Unknown"
                    })
        if images_data:
            img_df = pd.DataFrame(images_data)
            st.dataframe(img_df, use_container_width=True)
            missing_alt = int((img_df["alt_text"] == "").sum()) if "alt_text" in img_df.columns else 0
            if missing_alt:
                st.warning(f"⚠️ {missing_alt} images missing alt text")
            st.download_button("📥 Download Images CSV",
                               img_df.to_csv(index=False).encode("utf-8"),
                               "images_report.csv", "text/csv")
        else:
            st.info("No images found.")

    # -------------------------
    # Titles
    # -------------------------
    with tab_titles:
        st.subheader("📝 Page Titles Analysis")
        if "title" in df.columns:
            title_df = df[["url", "title", "title_length"]].copy()
            title_df["status"] = title_df.apply(
                lambda r: "❌ Missing" if r["title_length"] == 0 else
                          "⚠️ Too Long" if r["title_length"] > 60 else
                          "⚠️ Too Short" if r["title_length"] < 30 else "✅ Good",
                axis=1
            )
            st.dataframe(title_df, use_container_width=True)
            st.download_button("📥 Download Titles CSV",
                               title_df.to_csv(index=False).encode("utf-8"),
                               "titles_report.csv", "text/csv")
        else:
            st.warning("Title fields not found.")

    # -------------------------
    # Meta Descriptions
    # -------------------------
    with tab_meta:
        st.subheader("📄 Meta Descriptions Analysis")
        if "meta_description" in df.columns:
            meta_df = df[["url", "meta_description", "meta_desc_length"]].copy()
            meta_df["status"] = meta_df.apply(
                lambda r: "❌ Missing" if r["meta_desc_length"] == 0 else
                          "⚠️ Too Long" if r["meta_desc_length"] > 160 else
                          "⚠️ Too Short" if r["meta_desc_length"] < 120 else "✅ Good",
                axis=1
            )
            st.dataframe(meta_df, use_container_width=True)
            st.download_button("📥 Download Meta CSV",
                               meta_df.to_csv(index=False).encode("utf-8"),
                               "meta_desc_report.csv", "text/csv")
        else:
            st.warning("Meta description fields not found.")

    # -------------------------
    # Headers
    # -------------------------
    with tab_headers:
        st.subheader("🏷️ Header Tags Analysis (H1–H4)")
        needed = {"h1_count", "h2_count", "h3_count", "h4_count"}
        if needed.issubset(set(df.columns)):
            header_df = df[["url", "h1_count", "h2_count", "h3_count", "h4_count", "h1_tags"]].copy()
            header_df["h1_preview"] = header_df["h1_tags"].apply(lambda x: (x.split(";")[0][:100] if x else "Missing"))
            header_df["status"] = header_df.apply(
                lambda r: "❌ No H1" if r["h1_count"] == 0 else
                          "⚠️ Multiple H1" if r["h1_count"] > 1 else "✅ Good H1",
                axis=1
            )
            st.dataframe(header_df.drop(columns=["h1_tags"]), use_container_width=True)
            st.download_button("📥 Download Headers CSV",
                               header_df.to_csv(index=False).encode("utf-8"),
                               "headers_report.csv", "text/csv")
        else:
            st.warning("Header fields not found.")

    # -------------------------
    # Redirects
    # -------------------------
    with tab_redirects:
        st.subheader("🔄 Redirect Chain Analysis")
        if "redirect_count" in df.columns:
            red_df = df[df["redirect_count"] > 0].copy()
            if not red_df.empty:
                display_df = red_df[["original_url", "url", "redirect_count", "status_code"]].copy()
                display_df.columns = ["Original URL", "Final URL", "Redirect Hops", "Final Status"]
                st.dataframe(display_df, use_container_width=True)

                for _, row in red_df.iterrows():
                    chain = row.get("redirect_chain", [])
                    if chain:
                        with st.expander(f"🔗 Chain: {row.get('original_url','')[:80]}"):
                            for hop in chain:
                                st.write(f"**Step {hop.get('step')}**: {hop.get('redirect_type','')} → {hop.get('from_url','')}")

                st.download_button("📥 Download Redirects CSV",
                                   display_df.to_csv(index=False).encode("utf-8"),
                                   "redirects_report.csv", "text/csv")
            else:
                st.success("✅ No redirects found.")
        else:
            st.warning("Redirect fields not found.")

    # -------------------------
    # Status
    # -------------------------
    with tab_status:
        st.subheader("📊 HTTP Status Code Analysis")
        if "status_code" in df.columns:
            status_counts = df["status_code"].value_counts().sort_index()
            st.bar_chart(status_counts)
            status_df = df[["url", "status_code", "indexability", "response_time", "server"]].copy() if {"url","status_code"}.issubset(df.columns) else df
            st.dataframe(status_df, use_container_width=True)
            st.download_button("📥 Download Status CSV",
                               status_df.to_csv(index=False).encode("utf-8"),
                               "status_report.csv", "text/csv")
        else:
            st.warning("Status fields not found.")

    # -------------------------
    # Canonicals
    # -------------------------
    with tab_canon:
        st.subheader("🎯 Canonical URL Analysis")
        if "canonical_url" in df.columns:
            canonical_df = df[["url", "canonical_url", "meta_robots"]].copy()
            canonical_df["canonical_status"] = canonical_df.apply(
                lambda r: "❌ Missing" if not r["canonical_url"] else
                          "✅ Self-Referencing" if r["canonical_url"].rstrip("/") == r["url"].rstrip("/") else
                          "🔄 Points Elsewhere",
                axis=1
            )
            st.dataframe(canonical_df, use_container_width=True)
            st.download_button("📥 Download Canonicals CSV",
                               canonical_df.to_csv(index=False).encode("utf-8"),
                               "canonicals_report.csv", "text/csv")
        else:
            st.warning("Canonical fields not found.")

    # -------------------------
    # Social
    # -------------------------
    with tab_social:
        st.subheader("📱 Open Graph & Twitter Card Tags")
        social_cols = ["url", "og_title", "og_description", "og_image", "twitter_title", "twitter_description", "twitter_image"]
        if set(social_cols).issubset(df.columns):
            social_df = df[social_cols].copy()
            social_df["og_complete"] = social_df.apply(
                lambda r: "✅ Complete" if all([r["og_title"], r["og_description"], r["og_image"]]) else "⚠️ Incomplete",
                axis=1
            )
            social_df["twitter_complete"] = social_df.apply(
                lambda r: "✅ Complete" if all([r["twitter_title"], r["twitter_description"]]) else "⚠️ Incomplete",
                axis=1
            )
            st.dataframe(social_df, use_container_width=True)
            st.download_button("📥 Download Social CSV",
                               social_df.to_csv(index=False).encode("utf-8"),
                               "social_tags_report.csv", "text/csv")
        else:
            st.warning("Social tag fields not found.")

    # -------------------------
    # Performance
    # -------------------------
    with tab_perf:
        st.subheader("🚀 Performance & Technical Summary")
        perf_cols = ["url", "response_time", "content_length", "word_count", "css_files", "js_files", "schema_count"]
        if set(perf_cols).issubset(df.columns):
            perf_df = df[perf_cols].copy()
            perf_df["performance_score"] = perf_df.apply(
                lambda r: "🟢 Excellent" if r["response_time"] < 1.0 else
                          "🟡 Good" if r["response_time"] < 3.0 else "🔴 Needs Improvement",
                axis=1
            )
            st.dataframe(perf_df, use_container_width=True)

            p1, p2, p3 = st.columns(3)
            p1.metric("⚡ Avg Response Time", f"{df['response_time'].mean():.2f}s")
            p2.metric("📝 Avg Word Count", f"{int(df['word_count'].mean())}")
            p3.metric("🏷️ Pages with Schema", int((df["schema_count"] > 0).sum()))

            st.download_button("📥 Download Performance CSV",
                               perf_df.to_csv(index=False).encode("utf-8"),
                               "performance_report.csv", "text/csv")
        else:
            st.warning("Performance fields not found.")

    # -------------------------
    # Graph
    # -------------------------
    with tab_graph:
        st.subheader("🕸️ Site Architecture Visualization (Internal Links)")
        if not HAS_PYVIS:
            st.error("pyvis is not installed. Add `pyvis` to requirements.txt to enable graph.")
        else:
            if "internal_links" not in df.columns:
                st.warning("Internal links not found.")
            else:
                # Limit for performance
                max_nodes = st.slider("Max nodes in graph (performance)", 10, 250, 80)
                subset = df.head(max_nodes).copy()

                G = nx.DiGraph()
                urls_set = set(subset["url"].tolist())

                for _, row in subset.iterrows():
                    src = row["url"]
                    G.add_node(src, title=row.get("title", ""), color="#4CAF50", size=18)

                    for link in row.get("internal_links", []):
                        dst = link.get("url", "")
                        if dst in urls_set:
                            G.add_edge(src, dst, color="#aaaaaa")

                net = Network(height="650px", width="100%", bgcolor="#111111", font_color="white", directed=True)
                net.from_nx(G)
                net.repulsion(node_distance=110, spring_length=200)

                try:
                    path = "ultrafrog_graph.html"
                    net.save_graph(path)
                    with open(path, "r", encoding="utf-8") as f:
                        components.html(f.read(), height=700)
                except Exception as e:
                    st.error(f"Graph generation error: {e}")

    # -------------------------
    # Orphans
    # -------------------------
    with tab_orphan:
        st.subheader("👻 Orphan Pages (Sitemap URLs not reached by crawl)")
        if not sitemap_set:
            st.info("Provide a Sitemap URL in sidebar (Spider/List mode) to enable orphan detection.")
        else:
            if orphans:
                orphan_df = pd.DataFrame(sorted(orphans), columns=["Orphan URL"])
                st.dataframe(orphan_df, use_container_width=True)
                st.download_button("📥 Download Orphans CSV",
                                   orphan_df.to_csv(index=False).encode("utf-8"),
                                   "orphan_pages.csv", "text/csv")
            else:
                st.success("✅ No orphan pages found (or sitemap had no extra URLs).")

    # -------------------------
    # Custom extraction
    # -------------------------
    with tab_custom:
        st.subheader("⛏️ Custom Extracted Data")
        if "custom_extraction" in df.columns:
            custom_df = df[["url", "custom_extraction"]].copy()
            st.dataframe(custom_df, use_container_width=True)
            st.download_button("📥 Download Custom Extraction CSV",
                               custom_df.to_csv(index=False).encode("utf-8"),
                               "custom_extraction.csv", "text/csv")
        else:
            st.info("Run crawl with a selector to populate this tab.")

    # -------------------------
    # Raw data
    # -------------------------
    with tab_raw:
        st.subheader("📄 Raw Crawl Data")
        st.dataframe(df, use_container_width=True)

    # -------------------------
    # Quick Downloads
    # -------------------------
    st.header("📥 Quick Downloads")
    q1, q2, q3, q4 = st.columns(4)

    with q1:
        st.download_button("📊 Complete Report CSV",
                           df.to_csv(index=False).encode("utf-8"),
                           f"ultra_frog_complete_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                           "text/csv")

    with q2:
        issues_df = df[
            (df.get("status_code", 200) != 200) |
            (df.get("title_length", 0) == 0) |
            (df.get("meta_desc_length", 0) == 0) |
            (df.get("h1_count", 1) == 0) |
            (df.get("redirect_count", 0) > 0)
        ].copy()
        if not issues_df.empty:
            st.download_button("⚠️ Issues Report CSV",
                               issues_df.to_csv(index=False).encode("utf-8"),
                               f"ultra_frog_issues_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                               "text/csv")
        else:
            st.caption("No issues file (none found).")

    with q3:
        redirects_df = df[df.get("redirect_count", 0) > 0][["original_url", "url", "status_code", "redirect_count"]].copy() \
            if "redirect_count" in df.columns else pd.DataFrame()
        if not redirects_df.empty:
            st.download_button("🔄 Redirects Only CSV",
                               redirects_df.to_csv(index=False).encode("utf-8"),
                               f"ultra_frog_redirects_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                               "text/csv")
        else:
            st.caption("No redirects file (none found).")

    with q4:
        # Images report
        images_data = []
        if "images" in df.columns:
            for _, row in df.iterrows():
                for img in row.get("images", []):
                    images_data.append({
                        "source_url": row.get("url", ""),
                        "image_url": img.get("src", ""),
                        "alt_text": img.get("alt", ""),
                        "has_alt": "Yes" if img.get("alt", "") else "No"
                    })
        if images_data:
            images_df = pd.DataFrame(images_data)
            st.download_button("🖼️ Images Report CSV",
                               images_df.to_csv(index=False).encode("utf-8"),
                               f"ultra_frog_images_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                               "text/csv")
        else:
            st.caption("No images file (none found).")

    # -------------------------
    # Quick Insights
    # -------------------------
    st.header("🎯 Quick SEO Insights")
    i1, i2 = st.columns(2)
    with i1:
        st.write("**❌ Issues Found:**")
        missing_titles = int((df.get("title_length", 0) == 0).sum()) if "title_length" in df.columns else 0
        missing_meta = int((df.get("meta_desc_length", 0) == 0).sum()) if "meta_desc_length" in df.columns else 0
        missing_h1 = int((df.get("h1_count", 0) == 0).sum()) if "h1_count" in df.columns else 0
        images_no_alt = int(df.get("images_without_alt", pd.Series([0])).sum()) if "images_without_alt" in df.columns else 0

        if missing_titles: st.write(f"• {missing_titles} pages missing titles")
        if missing_meta: st.write(f"• {missing_meta} pages missing meta descriptions")
        if missing_h1: st.write(f"• {missing_h1} pages missing H1 tags")
        if images_no_alt: st.write(f"• {images_no_alt} images missing alt text")
        if not any([missing_titles, missing_meta, missing_h1, images_no_alt]):
            st.write("🎉 No major issues found!")

    with i2:
        st.write("**✅ Performance Summary:**")
        status_200 = int((df.get("status_code", 0) == 200).sum()) if "status_code" in df.columns else 0
        with_schema = int((df.get("schema_count", 0) > 0).sum()) if "schema_count" in df.columns else 0
        fast_pages = int((df.get("response_time", 999) < 2.0).sum()) if "response_time" in df.columns else 0
        avg_words = df.get("word_count", pd.Series([0])).mean() if "word_count" in df.columns else 0

        st.write(f"• {status_200} pages return 200 OK")
        st.write(f"• {with_schema} pages have schema markup")
        st.write(f"• {fast_pages} pages load under 2 seconds")
        st.write(f"• Average page size: {avg_words:.0f} words")

else:
    st.info("👈 Configure crawl settings in the sidebar and click **Start Crawl**.")
    st.header("🐸 Ultra Frog Features (3.1)")
    a, b, c = st.columns(3)
    with a:
        st.markdown("""
        **🎯 Crawl Modes**
        - 🕷️ Spider crawling with scope
        - 📝 List mode (paste/upload)
        - 🗺️ Sitemap crawling
        - ⛔ Stop crawl
        """)
    with b:
        st.markdown("""
        **📊 SEO Analysis**
        - Titles & meta descriptions
        - Canonicals & robots
        - Headers H1–H4
        - Status codes & redirects
        - Images + alt audit
        - Schema + social tags
        """)
    with c:
        st.markdown("""
        **🔗 Interlinking**
        - Anchor text
        - Placement (Header/Body/Footer/Sidebar)
        - CSS path detection
        - Graph visualization (pyvis)
        - Orphan pages via sitemap
        - Custom extraction via selector
        """)

# Footer
st.markdown("---")
st.markdown("""
<div style="text-align: center; padding: 1rem; background: linear-gradient(90deg, #4CAF50, #2E7D32); border-radius: 10px;">
    <h3 style="color: white; margin: 0;">🐸 Ultra Frog SEO Crawler v3.1</h3>
    <p style="color: white; margin: 0;">SEO + Interlinking + Reporting • Ready for GitHub deployment</p>
</div>
""", unsafe_allow_html=True)
