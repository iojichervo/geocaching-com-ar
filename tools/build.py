#!/usr/bin/env python3
"""Rebuild the static site from the Wayback Machine captures of geocaching.com.ar.

Usage: python3 tools/build.py            (from the repo root)

1. Crawls the raw archived HTML (`web/2022id_/...`) starting from the pages in SEEDS,
   following internal links to regular pages/posts (CRAWL_LIMIT).
2. Downloads every referenced asset (css/js/images/fonts) from the archive into assets/,
   recursing into CSS url()/@import.
3. Rewrites all URLs to relative local paths and writes the pages as <slug>/index.html.

Downloads are cached in .cache/, so re-running is cheap.
"""
import hashlib
import html
import os
import re
import sys
import time
import urllib.parse
import urllib.request
import urllib.error
from concurrent.futures import ThreadPoolExecutor
from posixpath import normpath, relpath, dirname, join as pjoin
from urllib.parse import urlsplit, urljoin

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CACHE = os.path.join(ROOT, ".cache")
SITE_HOSTS = {"geocaching.com.ar", "www.geocaching.com.ar"}
STAMP = "2022"  # Wayback picks the capture closest to this
SEEDS = [
    "", "argentinaworld", "nosotros", "guia-geocaching", "informe-anual-ga",
    "estadisticas-de-ga", "utilidades", "el-cache-del-ano", "cache-virtual", "earthcache",
    "benchmark", "registro-de-benchmarks", "la-ruta-40", "caches-rn40", "contacto",
]
CRAWL_LIMIT = 60
# the Sep 2022 capture of the home page is a hosting placeholder; use the Nov 2021 one
PAGE_STAMPS = {"": "20211127032549"}
ASSET_EXT = {"css", "js", "png", "jpg", "jpeg", "gif", "svg", "webp", "woff", "woff2", "ttf",
             "eot", "otf", "ico", "pdf", "mp4", "mp3", "zip"}
# third-party scripts that only make sense on a live server
DROP_SCRIPT_SRC = re.compile(
    r"hostinger\.com|respond\.min|html5shiv|fontawesome|google-analytics|googletagmanager|"
    r"recaptcha|argenmap|wp-emoji|xmlrpc", re.I)
DROP_INLINE_SCRIPT = re.compile(
    r"_wpemojiSettings|et_core_page_resource_fallback|google-analytics|gtag\(|recaptcha", re.I)


def _get(url):
    """GET with retries. Returns (bytes|None, definitive) - definitive=False on throttling/network errors."""
    for attempt in range(5):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (site-recreation)"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read(), True
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None, True
            time.sleep(3 * (attempt + 1))
        except Exception:
            time.sleep(3 * (attempt + 1))
    return None, False


def fetch(url, mode="id_", stamp=None):
    """Download `url` from the archive (cached). Falls back to any 200 capture via CDX."""
    os.makedirs(CACHE, exist_ok=True)
    key = os.path.join(CACHE, hashlib.sha1((mode + (stamp or "") + url).encode()).hexdigest())
    if os.path.exists(key):
        data = open(key, "rb").read()
        return data or None
    data, definitive = _get(f"https://web.archive.org/web/{stamp or STAMP}{mode}/{url}")
    if not data:
        cdx, _ = _get("https://web.archive.org/cdx/search/cdx?output=txt&fl=timestamp&filter=statuscode:200"
                      "&limit=-1&url=" + urllib.parse.quote(url, safe=""))
        stamps = cdx.decode().split() if cdx else []
        if stamps:
            data, definitive = _get(f"https://web.archive.org/web/{stamps[0]}{mode}/{url}")
        elif cdx is not None:
            definitive = True
    if data or definitive:
        open(key, "wb").write(data or b"")
    return data


def norm_site_path(u):
    """http://www.geocaching.com.ar/index.php/foo/?x -> 'foo' (None if not a plain page)."""
    p = urlsplit(u)
    if p.netloc.lower() not in SITE_HOSTS:
        return None
    path = re.sub(r"^/index\.php", "", p.path).strip("/")
    if p.query and not path:
        return None
    return path


def is_page_path(path):
    if path is None:
        return False
    if path == "":
        return True
    if re.search(r"\.[a-z0-9]{2,5}$", path, re.I):
        return False
    return not re.match(r"(wp-|feed|category|tag|author|comments|xmlrpc|\?)", path)


def ext_of(path):
    m = re.search(r"\.([a-z0-9]+)$", path, re.I)
    return m.group(1).lower() if m else ""


def asset_local_path(u):
    """Map an asset URL to its path under the repo (no query string)."""
    p = urlsplit(u)
    path = p.path
    if p.netloc.lower() in SITE_HOSTS:
        return "assets/" + path.lstrip("/")
    if "fonts.googleapis.com" in p.netloc:
        return "assets/fonts/" + hashlib.sha1(u.encode()).hexdigest()[:10] + ".css"
    return "assets/ext/" + p.netloc + path


def is_asset_url(u):
    p = urlsplit(u)
    if "fonts.googleapis.com" in p.netloc and p.path.endswith("/css"):
        return True
    return ext_of(p.path) in ASSET_EXT


URL_RE = re.compile(r"""https?:(?:\\?/){2}[^\s"'<>()\\]+(?:\\/[^\s"'<>()\\]+)*""")


def clean_url(u):
    u = html.unescape(u.replace("\\/", "/"))
    return u.rstrip(".,;")


assets = {}  # url -> local path (None if download failed)


def get_asset(u):
    """Make sure asset `u` is downloaded; returns its local path or None."""
    if u in assets:
        return assets[u]
    local = asset_local_path(u)
    assets[u] = local  # optimistic (avoids recursion loops)
    data = fetch(u, "id_")
    if not data:
        assets[u] = None
        print("  MISSING", u)
        return None
    dest = os.path.join(ROOT, local)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    if local.endswith(".css"):
        data = process_css(data.decode("utf-8", "replace"), u, local).encode("utf-8")
    open(dest, "wb").write(data)
    return local


CSS_URL_RE = re.compile(r"""url\(\s*(['"]?)([^'")]+)\1\s*\)|@import\s+(['"])([^'"]+)\3""")


def process_css(text, css_url, css_local):
    def sub(m):
        ref = m.group(2) or m.group(4)
        if ref.startswith(("data:", "#")):
            return m.group(0)
        absu = urljoin(css_url, html.unescape(ref))
        if not is_asset_url(absu):
            return m.group(0)
        loc = get_asset(absu)
        if not loc:
            return m.group(0)
        rel = relpath(loc, dirname(css_local))
        if m.group(2) is not None:
            return f"url({rel})"
        return f'@import "{rel}"'
    return CSS_URL_RE.sub(sub, text)


def rel_to(page_depth, target):
    return ("../" * page_depth) + target


def page_href(slug, depth):
    if slug == "":
        return "../" * depth if depth else "./"
    return rel_to(depth, slug + "/")


def rewrite_html(text, slug, known_pages):
    depth = len(slug.split("/")) if slug else 0

    # drop junk first
    def keep_script(m):
        attrs, body = m.group(1), m.group(2)
        src = re.search(r"""src=["']([^"']+)""", attrs)
        if src:
            return "" if DROP_SCRIPT_SRC.search(src.group(1)) else m.group(0)
        return "" if DROP_INLINE_SCRIPT.search(body) else m.group(0)
    text = re.sub(r"<script\b([^>]*)>(.*?)</script>", keep_script, text, flags=re.S)
    text = re.sub(r"<link[^>]+rel=['\"](?:pingback|EditURI|wlwmanifest|alternate|https://api\.w\.org/|shortlink|canonical|dns-prefetch)['\"][^>]*>", "", text)
    text = re.sub(r"<link[^>]+(?:xmlrpc|wlwmanifest|wp-json)[^>]*>", "", text)
    text = re.sub(r"<meta name=['\"]generator['\"][^>]*>", "", text)
    text = re.sub(r"<noscript>.*?</noscript>", "", text, flags=re.S)
    text = re.sub(r"<style[^>]*id=['\"]wp-emoji[^>]*>.*?</style>", "", text, flags=re.S)

    def sub(m):
        raw = m.group(0)
        u = clean_url(raw)
        if is_asset_url(u):
            loc = get_asset(u)
            return rel_to(depth, loc) if loc else raw
        path = norm_site_path(u)
        if path is not None and is_page_path(path):
            frag = ("#" + urlsplit(u).fragment) if urlsplit(u).fragment else ""
            if path in known_pages:
                return page_href(path, depth) + frag
            return "https://web.archive.org/web/" + STAMP + "/" + u
        return raw
    # inline JSON escapes slashes; only rewrite asset/page URLs, leave the rest
    text = URL_RE.sub(sub, text)

    # static-site tweaks
    text = re.sub(r"(<div id=\"footer-info\">)(.*?)(</div>)",
                  r"\1\2 &middot; Recreaci&oacute;n est&aacute;tica basada en las copias de web.archive.org\3",
                  text, count=1, flags=re.S)
    return text


def crawl():
    pages = {}
    queue = list(SEEDS)
    seen = set(queue)
    while queue and len(pages) < CRAWL_LIMIT:
        batch, queue = queue[:8], queue[8:]
        with ThreadPoolExecutor(3) as ex:
            res = list(ex.map(lambda s: (s, fetch(f"http://geocaching.com.ar/{s}/" if s else "http://geocaching.com.ar/", stamp=PAGE_STAMPS.get(s))), batch))
        for slug, data in res:
            if not data:
                print("  page not archived:", slug)
                continue
            text = data.decode("utf-8", "replace")
            pages[slug] = text
            body = text[text.find("<body"):]
            for u in URL_RE.findall(body):
                path = norm_site_path(clean_url(u))
                if is_page_path(path) and path not in seen and "/page/" not in path:
                    seen.add(path)
                    queue.append(path)
    return pages


def main():
    pages = crawl()
    print(f"{len(pages)} pages: {sorted(pages)}")
    known = set(pages)
    for slug, text in pages.items():
        out = rewrite_html(text, slug, known)
        dest = os.path.join(ROOT, slug, "index.html") if slug else os.path.join(ROOT, "index.html")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        open(dest, "w", encoding="utf-8").write(out)
    print(f"{sum(1 for v in assets.values() if v)} assets ok, {sum(1 for v in assets.values() if not v)} missing")


if __name__ == "__main__":
    sys.exit(main())
