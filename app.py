def extract_page_data(self, url):
    try:
        response = self.session.get(url, timeout=10, allow_redirects=True)
        soup = BeautifulSoup(response.content, 'html.parser')

        # ===== BASIC SEO =====
        title = soup.find('title')
        title_text = title.get_text().strip() if title else ""

        meta_desc = soup.find('meta', attrs={'name': 'description'})
        meta_desc_text = meta_desc.get('content', '') if meta_desc else ""

        canonical = soup.find('link', attrs={'rel': 'canonical'})
        canonical_url = canonical.get('href', '') if canonical else ""

        meta_robots = soup.find('meta', attrs={'name': 'robots'})
        robots_content = meta_robots.get('content', '') if meta_robots else ""

        # ===== SOCIAL TAGS =====
        og_title = soup.find('meta', attrs={'property': 'og:title'})
        og_desc = soup.find('meta', attrs={'property': 'og:description'})
        og_image = soup.find('meta', attrs={'property': 'og:image'})

        twitter_title = soup.find('meta', attrs={'name': 'twitter:title'})
        twitter_desc = soup.find('meta', attrs={'name': 'twitter:description'})
        twitter_image = soup.find('meta', attrs={'name': 'twitter:image'})

        # ===== HEADERS H1-H4 =====
        h1_tags = [h.get_text(strip=True) for h in soup.find_all('h1')]
        h2_tags = [h.get_text(strip=True) for h in soup.find_all('h2')]
        h3_tags = [h.get_text(strip=True) for h in soup.find_all('h3')]
        h4_tags = [h.get_text(strip=True) for h in soup.find_all('h4')]

        # ===== LINKS (KEEP YOUR PLACEMENT + ADD EXTERNAL) =====
        internal_links = []
        external_links = []
        base_domain = urlparse(response.url).netloc

        for link in soup.find_all('a', href=True):
            href = urljoin(response.url, link['href'])
            link_text = link.get_text().strip()[:100]

            css_path = self.get_css_path(link)
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

        # ===== IMAGES =====
        images = []
        for img in soup.find_all('img'):
            img_src = urljoin(response.url, img.get('src', ''))
            images.append({
                'src': img_src,
                'alt': img.get('alt', ''),
                'title': img.get('title', ''),
                'width': img.get('width', ''),
                'height': img.get('height', '')
            })

        # ===== SCHEMA TYPES =====
        schema_types = []
        scripts = soup.find_all('script', type='application/ld+json')
        for script in scripts:
            try:
                if script.string:
                    schema_data = json.loads(script.string)
                    if isinstance(schema_data, dict) and '@type' in schema_data:
                        schema_types.append(str(schema_data['@type']))
                    elif isinstance(schema_data, list):
                        for item in schema_data:
                            if isinstance(item, dict) and '@type' in item:
                                schema_types.append(str(item['@type']))
            except:
                pass

        # ===== PERFORMANCE INDICATORS (LIGHT) =====
        css_files = len(soup.find_all('link', attrs={'rel': 'stylesheet'}))
        js_files = len(soup.find_all('script', src=True))
        word_count = len(soup.get_text(" ").split())

        # ===== REDIRECT CHAIN =====
        redirect_chain = []
        if response.history:
            for i, resp in enumerate(response.history):
                redirect_chain.append({
                    'step': i + 1,
                    'from_url': resp.url,
                    'to_url': resp.headers.get('location', ''),
                    'status_code': resp.status_code
                })

        # ===== CUSTOM EXTRACTION =====
        custom_data = ""
        if self.custom_selector:
            custom_elements = soup.select(self.custom_selector)
            custom_data = "; ".join([el.get_text(strip=True) for el in custom_elements])

        # ===== INDEXABILITY =====
        indexability = "Indexable"
        if response.status_code != 200 or ('noindex' in robots_content.lower()):
            indexability = "Non-Indexable"

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

            'internal_links': internal_links,
            'internal_links_count': len(internal_links),
            'external_links': external_links,
            'external_links_count': len(external_links),

            'images': images,
            'image_count': len(images),
            'images_without_alt': len([i for i in images if not i.get('alt')]),

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
            'indexability': indexability,
            'crawl_timestamp': datetime.now().isoformat()
        }

    except Exception as e:
        return {
            'url': url,
            'original_url': url,
            'status_code': 0,
            'error': str(e),
            'title': '', 'title_length': 0,
            'meta_description': '', 'meta_desc_length': 0,
            'canonical_url': '', 'meta_robots': '',
            'h1_tags': '', 'h1_count': 0,
            'h2_tags': '', 'h2_count': 0,
            'h3_tags': '', 'h3_count': 0,
            'h4_tags': '', 'h4_count': 0,
            'word_count': 0,
            'response_time': 0,
            'content_length': 0,
            'internal_links': [], 'internal_links_count': 0,
            'external_links': [], 'external_links_count': 0,
            'images': [], 'image_count': 0, 'images_without_alt': 0,
            'schema_types': '', 'schema_count': 0,
            'redirect_chain': [], 'redirect_count': 0,
            'css_files': 0, 'js_files': 0,
            'og_title': '', 'og_description': '', 'og_image': '',
            'twitter_title': '', 'twitter_description': '', 'twitter_image': '',
            'content_type': '', 'last_modified': '', 'server': '',
            'custom_extraction': '',
            'indexability': 'Error',
            'crawl_timestamp': datetime.now().isoformat()
        }
