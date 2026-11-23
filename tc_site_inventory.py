#!/usr/bin/env python3
"""
Tata Capital site inventory.

Crawls tatacapital.com (sitemap + links), and for every page records:
  - final URL, status, redirect chain, and whether it leaves the main site
  - title, meta, H1, H2s, breadcrumb, word count, full page text
  - forms and fields, calculators (sliders), videos, iframes (and whose), FAQs, tables
  - every link on the page (header/footer vs body), PDFs and other documents
  - full-page screenshots at 1440 (desktop) and 360 (mobile)

Outputs (in ./tc_inventory by default):
  Tata Capital Site Inventory.html   contact sheet, grouped by section, opens offline
  inventory.csv                      one row per page
  links.csv                          every link: from page, to URL, link text, where on page
  documents.csv                      PDFs and other files linked from the site
  offsite.csv                        hosts the site sends people to (subdomains, LOS, partners)
  screens/desktop/*.jpg, screens/mobile/*.jpg
  text/*.txt                         visible text of each page
  pages.jsonl                        raw record per page (lets a stopped run resume)

Setup (once, on a Mac):
  python3 -m venv tcenv && source tcenv/bin/activate
  pip install playwright
  python -m playwright install chromium

Run:
  python tc_site_inventory.py --max-pages 20      # quick test first
  python tc_site_inventory.py                     # full run: www plus every *.tatacapital.com subdomain
  python tc_site_inventory.py --main-only         # www only

It only opens pages (GET). It never clicks, submits forms or accepts cookies.
"""
import argparse, asyncio, csv, hashlib, html, json, os, re, sys, time
from collections import defaultdict
from urllib.parse import urlparse, urlunparse, urljoin
from xml.etree import ElementTree as ET

try:
    from playwright.async_api import async_playwright
except ImportError:
    sys.exit("Playwright is missing. Run: pip install playwright && python -m playwright install chromium")

DOC_EXT = re.compile(r"\.(pdf|docx?|xlsx?|pptx?|zip|csv|jpg|jpeg|png|gif|svg|webp|mp4|mp3)$", re.I)
SKIP_SCHEMES = ("mailto:", "tel:", "javascript:", "whatsapp:", "sms:", "data:")
UA_DESKTOP = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
UA_MOBILE = ("Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 "
             "(KHTML, like Gecko) Chrome/131.0.0.0 Mobile Safari/537.36")

EXTRACT_JS = r"""
() => {
  const q = s => [...document.querySelectorAll(s)];
  const txt = e => (e && (e.innerText || e.textContent) || '').replace(/\s+/g, ' ').trim();
  const meta = n => (document.querySelector(`meta[name="${n}"]`) || {}).content || '';
  const body = txt(document.body);
  const host = u => { try { return new URL(u, location.href).host } catch (e) { return '' } };
  const ld = q('script[type="application/ld+json"]').map(s => {
    try { const j = JSON.parse(s.textContent); return [].concat(j['@graph'] || j).map(x => [].concat(x['@type'] || [])).flat().join('|') }
    catch (e) { return 'invalid-json' }
  }).filter(Boolean).join('|');
  const bc = document.querySelector('nav[aria-label*="readcrumb"], [class*="breadcrumb" i], [itemtype*="BreadcrumbList"]');
  const ctas = [...new Set(q('button, a[class*="btn" i], a[class*="button" i], a[class*="cta" i], [role="button"]')
                 .map(txt).filter(t => t && t.length <= 40))].slice(0, 40);
  return {
    title: document.title || '',
    description: meta('description'),
    robots: meta('robots'),
    canonical: (document.querySelector('link[rel="canonical"]') || {}).href || '',
    lang: document.documentElement.lang || '',
    hreflang: q('link[rel="alternate"][hreflang]').map(l => l.hreflang).join('|'),
    h1: q('h1').map(txt).filter(Boolean).join(' | '),
    h2: q('h2').map(txt).filter(Boolean).slice(0, 40).join(' | '),
    h3_count: q('h3').length,
    breadcrumb: txt(bc),
    words: body ? body.split(' ').length : 0,
    forms: q('form').length,
    fields: q('input:not([type="hidden"]):not([type="submit"]), select, textarea')
              .map(i => i.getAttribute('name') || i.id || i.getAttribute('placeholder') || i.type).filter(Boolean).slice(0, 40).join('|'),
    sliders: q('input[type="range"], [role="slider"], [class*="slider" i] input').length,
    videos: q('video').length + q('iframe[src*="youtube"], iframe[src*="vimeo"], iframe[data-src*="youtube"]').length,
    iframe_hosts: [...new Set(q('iframe').map(f => host(f.src || f.dataset.src || '')).filter(Boolean))].join('|'),
    images: q('img').length,
    images_no_alt: q('img:not([alt]), img[alt=""]').length,
    tables: q('table').length,
    accordions: q('details, [class*="faq" i], [class*="accordion" i]').length,
    ctas: ctas.join(' | '),
    jsonld: ld,
    percents: [...new Set(body.match(/\d{1,2}(\.\d{1,2})?\s?%/g) || [])].slice(0, 25).join(' '),
    rupees: [...new Set(body.match(/₹\s?[\d,.]+\s?(lakh|crore|Lakh|Crore|L|Cr)?/g) || [])].slice(0, 25).join(' '),
    text: body,
    links: q('a[href]').map(a => ({
      href: a.href, text: txt(a).slice(0, 100),
      region: a.closest('header') ? 'header' : a.closest('footer') ? 'footer' : a.closest('nav') ? 'nav' : 'body'
    })),
  };
}
"""

AUTO_SCROLL_JS = r"""
async () => {
  const step = Math.max(400, window.innerHeight * 0.8);
  for (let y = 0, i = 0; y < document.body.scrollHeight && i < 60; y += step, i++) {
    window.scrollTo(0, y); await new Promise(r => setTimeout(r, 120));
  }
  window.scrollTo(0, 0); await new Promise(r => setTimeout(r, 300));
}
"""


def norm(url, keep_query=False):
    """Normalise a URL for de-duplication: no fragment, lower host, no trailing slash, no query by default."""
    p = urlparse(url.strip())
    if p.scheme not in ("http", "https"):
        return None
    path = re.sub(r"/{2,}", "/", p.path or "/")
    if len(path) > 1 and path.endswith("/"):
        path = path[:-1]
    query = p.query if keep_query else ""
    return urlunparse((p.scheme, p.netloc.lower(), path, "", query, ""))


def slug(url):
    p = urlparse(url)
    s = (p.netloc.split(".")[0] + "_" + p.path.strip("/").replace("/", "_")).strip("_") or "home"
    s = re.sub(r"[^A-Za-z0-9_\-]+", "-", s)[:90]
    return f"{s}__{hashlib.md5(url.encode()).hexdigest()[:6]}"


def section_of(url, main_host):
    p = urlparse(url)
    seg = re.sub(r"\.html?$", "", p.path.strip("/").split("/")[0]) or "(home)"
    if p.netloc != main_host:
        return f"{p.netloc} / {seg}"
    return seg


class Crawler:
    def __init__(self, a):
        self.a = a
        self.start = norm(a.start)
        self.main_host = urlparse(self.start).netloc
        self.base = f"{urlparse(self.start).scheme}://{self.main_host}"
        self.root_domain = ".".join(self.main_host.split(".")[-2:])
        self.out = a.out
        for d in ("screens/desktop", "screens/mobile", "text"):
            os.makedirs(os.path.join(self.out, d), exist_ok=True)
        self.jsonl = os.path.join(self.out, "pages.jsonl")
        self.seen, self.done = set(), {}
        self.queue = asyncio.Queue()
        self.docs = defaultdict(set)      # doc url -> set(from pages)
        self.offsite = defaultdict(set)   # host -> set(from pages)
        self.count = 0
        self.lock = asyncio.Lock()
        self.sitemapped = set()
        self.leftover = 0
        self.timed_out = False
        self.sitemap_set = set()
        self.t0 = time.time()

    def in_scope(self, url):
        h = urlparse(url).netloc
        if h == self.main_host:
            return True
        return (not self.a.main_only) and (h == self.root_domain or h.endswith("." + self.root_domain))

    def enqueue(self, url):
        if not url or url in self.seen:
            return
        if len(self.seen) >= self.a.max_pages:
            return
        if self.a.exclude and re.search(self.a.exclude, url):
            return
        self.seen.add(url)
        self.queue.put_nowait(url)

    # ---------- discovery ----------
    async def sitemap_urls(self, request, base=None):
        base = base or self.base
        found, todo, visited = set(), [], set()
        try:
            r = await request.get(f"{base}/robots.txt", timeout=30000)
            if r.ok:
                for line in (await r.text()).splitlines():
                    if line.lower().startswith("sitemap:"):
                        todo.append(line.split(":", 1)[1].strip())
        except Exception as e:
            print("  robots.txt not read:", e)
        todo += [f"{base}/sitemap.xml", f"{base}/sitemap_index.xml"]
        while todo:
            sm = todo.pop(0)
            if sm in visited or len(visited) > 200:
                continue
            visited.add(sm)
            try:
                r = await request.get(sm, timeout=60000)
                if not r.ok:
                    continue
                root = ET.fromstring(await r.body())
            except Exception:
                continue
            for el in root.iter():
                if el.tag.endswith("loc") and el.text:
                    u = el.text.strip()
                    if root.tag.endswith("sitemapindex"):
                        todo.append(u)
                    else:
                        found.add(u)
            print(f"  sitemap {sm}: {len(found)} URLs so far")
        return found

    async def add_sitemap(self, request, base):
        sm = await self.sitemap_urls(request, base)
        for u in sorted(sm):
            n = norm(u)
            if not n:
                continue
            if DOC_EXT.search(urlparse(n).path):
                self.docs[n].add("(sitemap)")
            elif self.in_scope(n):
                self.sitemap_set.add(n)
                self.enqueue(n)
        if sm:
            with open(os.path.join(self.out, "sitemap_urls.txt"), "w") as f:
                f.write("\n".join(sorted(self.sitemap_set)))

    # ---------- per page ----------
    async def capture(self, ctx, url, shot_path, extract):
        page = await ctx.new_page()
        rec = {}
        try:
            resp = await page.goto(url, wait_until="domcontentloaded", timeout=self.a.timeout * 1000)
            try:
                await page.wait_for_load_state("networkidle", timeout=12000)
            except Exception:
                pass
            if resp is not None:
                chain, r = [], resp.request.redirected_from
                while r:
                    chain.append(r.url)
                    r = r.redirected_from
                rec["status"] = resp.status
                rec["redirect_chain"] = " > ".join(reversed(chain))
            else:
                rec["status"] = None
                rec["redirect_chain"] = ""
            await page.wait_for_timeout(self.a.settle)
            rec["final_url"] = page.url
            await page.evaluate(AUTO_SCROLL_JS)
            await page.wait_for_timeout(400)
            await page.screenshot(path=shot_path, full_page=True, type="jpeg", quality=self.a.quality)
            rec["page_height"] = await page.evaluate("document.documentElement.scrollHeight")
            if extract:
                rec.update(await page.evaluate(EXTRACT_JS))
        except Exception as e:
            rec["error"] = str(e).splitlines()[0][:300]
        finally:
            await page.close()
        return rec

    async def worker(self, dctx, mctx):
        while True:
            url = await self.queue.get()
            try:
                if url in self.done:
                    continue
                if self.a.batch_pages and self.count >= self.a.batch_pages:
                    self.leftover += 1
                    continue
                s = slug(url)
                dpath = os.path.join(self.out, "screens/desktop", s + ".jpg")
                mpath = os.path.join(self.out, "screens/mobile", s + ".jpg")
                rec = await self.capture(dctx, url, dpath, extract=True)
                if not self.a.no_mobile and "error" not in rec:
                    m = await self.capture(mctx, url, mpath, extract=False)
                    rec["mobile_height"] = m.get("page_height")
                    rec["mobile_error"] = m.get("error", "")
                rec["url"], rec["slug"] = url, s
                final = rec.get("final_url") or url
                rec["final_host"] = urlparse(final).netloc
                rec["left_main_site"] = rec["final_host"] != self.main_host
                rec["redirected"] = norm(final) != url
                rec["section"] = section_of(url, self.main_host)
                text = rec.pop("text", "")
                if text:
                    with open(os.path.join(self.out, "text", s + ".txt"), "w", encoding="utf-8") as f:
                        f.write(f"{url}\n{rec.get('title','')}\n\n{text}")
                internal = []
                for l in rec.get("links", []):
                    h = l["href"]
                    if h.startswith(SKIP_SCHEMES):
                        continue
                    n = norm(h)
                    if not n:
                        continue
                    if DOC_EXT.search(urlparse(n).path):
                        continue
                    if self.in_scope(n):
                        internal.append(n)
                rec["internal_links"] = sorted(set(internal))
                # follow links only from pages that stayed on the main site
                rec["left_scope"] = not self.in_scope(norm(final) or url)
                if not rec["left_scope"]:
                    if not self.a.no_sitemap:
                        for h in sorted({urlparse(n).netloc for n in rec["internal_links"]} | {rec["final_host"]}):
                            if h not in self.sitemapped:
                                self.sitemapped.add(h)
                                await self.add_sitemap(dctx.request, f"{urlparse(self.start).scheme}://{h}")
                    for n in rec["internal_links"]:
                        self.enqueue(n)
                async with self.lock:
                    self.done[url] = rec
                    with open(self.jsonl, "a", encoding="utf-8") as f:
                        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
                    self.count += 1
                    el = time.time() - self.t0
                    flag = "ERR " if rec.get("error") else ("-> " + rec["final_host"] + " " if rec["final_host"] != urlparse(url).netloc else "")
                    print(f"[{len(self.done):>4} done | {self.queue.qsize():>4} queued | {el/60:5.1f} min] "
                          f"{rec.get('status')} {flag}{url}")
                if self.a.delay:
                    await asyncio.sleep(self.a.delay)
            finally:
                self.queue.task_done()

    # ---------- run ----------
    def load_done(self, retry_errors=False):
        errs = defaultdict(int)
        if os.path.exists(self.jsonl):
            with open(self.jsonl, encoding="utf-8") as f:
                for line in f:
                    try:
                        r = json.loads(line)
                    except Exception:
                        continue
                    if r.get("error"):
                        errs[r["url"]] += 1
                    self.done[r["url"]] = r
        if retry_errors:   # a failed page gets one more try on the next run
            for u, n in errs.items():
                if n < 2 and self.done.get(u, {}).get("error"):
                    del self.done[u]

    async def run(self):
        # resume
        if self.a.fresh and os.path.exists(self.jsonl):
            os.remove(self.jsonl)
        self.load_done(retry_errors=True)
        if self.done:
            print(f"Resuming: {len(self.done)} pages already captured.")

        async with async_playwright() as p:
            launch = dict(headless=not self.a.headed)
            if self.a.chrome:
                launch["channel"] = "chrome"
            browser = await p.chromium.launch(**launch)
            dctx = await browser.new_context(viewport={"width": 1440, "height": 900}, user_agent=UA_DESKTOP,
                                             locale="en-IN", timezone_id="Asia/Kolkata")
            mctx = await browser.new_context(viewport={"width": 360, "height": 800}, user_agent=UA_MOBILE,
                                             device_scale_factor=1.5, is_mobile=True, has_touch=True,
                                             locale="en-IN", timezone_id="Asia/Kolkata")

            print("Finding pages from robots.txt and sitemaps...")
            self.enqueue(self.start)
            if not self.a.no_sitemap:
                self.sitemapped.add(self.main_host)
                await self.add_sitemap(dctx.request, self.base)
            if self.a.recapture and os.path.exists(self.a.recapture):
                for u in open(self.a.recapture).read().split():
                    n = norm(u)
                    if n:
                        self.done.pop(n, None)
                        self.seen.discard(n)
                        self.enqueue(n)
            for r in list(self.done.values()):        # re-queue links found before a stop
                self.seen.add(r["url"])
                if not r.get("left_scope", r.get("left_main_site")):
                    for n in r.get("internal_links", []):
                        self.enqueue(n)
            sm = self.sitemap_set
            print(f"Starting with {self.queue.qsize()} queued ({len(sm)} from sitemaps). Max pages {self.a.max_pages}.")

            workers = [asyncio.create_task(self.worker(dctx, mctx)) for _ in range(self.a.workers)]
            try:
                limit = self.a.time_limit * 60 if self.a.time_limit else None
                await asyncio.wait_for(self.queue.join(), timeout=limit)
            except asyncio.TimeoutError:
                self.timed_out = True
                print("Time limit reached. Saving; the next run resumes.")
            except (KeyboardInterrupt, asyncio.CancelledError):
                print("Stopped. Writing what we have; run again to resume.")
            for w in workers:
                w.cancel()
            await browser.close()
        self.write_outputs()

    # ---------- outputs ----------
    def write_outputs(self):
        recs = sorted(self.done.values(), key=lambda r: (r.get("section", ""), r["url"]))
        smf = os.path.join(self.out, "sitemap_urls.txt")
        sm = self.sitemap_set
        if not sm:
            sm = set(open(smf).read().split()) if os.path.exists(smf) else set()
        for r in recs:
            for l in r.get("links", []):
                h = l["href"]
                if h.startswith(SKIP_SCHEMES):
                    continue
                n = norm(h)
                if not n:
                    continue
                if DOC_EXT.search(urlparse(n).path):
                    self.docs[norm(h, keep_query=True)].add(r["url"])
                elif not self.in_scope(n):
                    self.offsite[urlparse(n).netloc].add(r["url"])
        cols = ["section", "url", "status", "redirected", "left_main_site", "left_scope", "final_url", "final_host", "redirect_chain",
                "in_sitemap", "title", "h1", "h2", "h3_count", "breadcrumb", "description", "canonical", "robots",
                "lang", "hreflang", "words", "forms", "fields", "sliders", "videos", "iframe_hosts", "tables",
                "accordions", "images", "images_no_alt", "ctas", "percents", "rupees", "jsonld", "page_height",
                "mobile_height", "inlinks", "outlinks_internal", "error", "mobile_error", "slug"]
        inlinks = defaultdict(int)
        for r in recs:
            for n in r.get("internal_links", []):
                inlinks[n] += 1
        with open(os.path.join(self.out, "inventory.csv"), "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
            w.writeheader()
            for r in recs:
                row = dict(r)
                row["in_sitemap"] = r["url"] in sm
                row["inlinks"] = inlinks.get(r["url"], 0)
                row["outlinks_internal"] = len(r.get("internal_links", []))
                w.writerow(row)
        with open(os.path.join(self.out, "links.csv"), "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["from_url", "to_url", "to_host", "link_text", "region"])
            for r in recs:
                for l in r.get("links", []):
                    if l["href"].startswith(SKIP_SCHEMES):
                        w.writerow([r["url"], l["href"][:200], l["href"].split(":")[0], l["text"], l["region"]])
                    else:
                        w.writerow([r["url"], l["href"], urlparse(l["href"]).netloc, l["text"], l["region"]])
        with open(os.path.join(self.out, "documents.csv"), "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["document_url", "type", "linked_from_count", "example_page"])
            for d, src in sorted(self.docs.items()):
                w.writerow([d, os.path.splitext(urlparse(d).path)[1].lower(), len(src), sorted(src)[0]])
        with open(os.path.join(self.out, "offsite.csv"), "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["host", "kind", "linked_from_pages", "example_page"])
            for h, src in sorted(self.offsite.items(), key=lambda x: -len(x[1])):
                kind = "Tata Capital subdomain" if h.endswith(self.root_domain) else "other"
                w.writerow([h, kind, len(src), sorted(src)[0]])
        self.write_html(recs, inlinks)
        pending = self.leftover + (self.queue.qsize() if hasattr(self, "queue") else 0)
        with open(os.path.join(self.out, "status.json"), "w") as f:
            json.dump({"pages_total": len(recs), "pages_this_run": self.count, "pending": pending,
                       "timed_out": self.timed_out, "finished": pending == 0 and not self.timed_out}, f)
        el = (time.time() - self.t0) / 60
        print(f"\nDone: {len(recs)} pages, {len(self.docs)} documents, {len(self.offsite)} off-site hosts, {el:.1f} min.")
        print(f"Open: {os.path.join(self.out, 'Tata Capital Site Inventory.html')}")

    def write_html(self, recs, inlinks):
        groups = defaultdict(list)
        for r in recs:
            groups[r.get("section", "?")].append(r)
        e = lambda s: html.escape(str(s if s is not None else ""))
        n_redir = sum(1 for r in recs if r.get("redirected"))
        n_off = sum(1 for r in recs if r.get("left_main_site"))
        n_err = sum(1 for r in recs if r.get("error") or (r.get("status") or 0) >= 400)
        nav = "".join(f'<a href="#s-{i}">{e(k)} <b>{len(v)}</b></a>' for i, (k, v) in enumerate(sorted(groups.items())))
        body = []
        num = 0
        for i, (sec, rows) in enumerate(sorted(groups.items())):
            cards = []
            for r in rows:
                num += 1
                st = r.get("status")
                tags = []
                if r.get("error"): tags.append('<i class="bad">Error</i>')
                elif st and st >= 400: tags.append(f'<i class="bad">{st}</i>')
                if r.get("left_main_site"): tags.append(f'<i class="off">Goes to {e(r.get("final_host"))}</i>')
                elif r.get("redirected"): tags.append('<i class="warn">Redirects</i>')
                if r.get("forms"): tags.append(f'<i>Form ×{r["forms"]}</i>')
                if r.get("sliders"): tags.append('<i>Calculator</i>')
                if r.get("videos"): tags.append(f'<i>Video ×{r["videos"]}</i>')
                if r.get("accordions"): tags.append('<i>FAQ/accordion</i>')
                if not r.get("h1"): tags.append('<i class="warn">No H1</i>')
                d = f'screens/desktop/{r["slug"]}.jpg'
                m = f'screens/mobile/{r["slug"]}.jpg'
                cards.append(f'''<div class="card" data-q="{e((r["url"]+" "+str(r.get("title",""))).lower())}">
<div class="shots"><a href="{e(d)}" target="_blank"><img loading="lazy" src="{e(d)}" alt="Desktop"></a>
<a href="{e(m)}" target="_blank" class="mob"><img loading="lazy" src="{e(m)}" alt="Mobile"></a></div>
<div class="meta"><span class="num">P{num}</span><a class="u" href="{e(r["url"])}" target="_blank">{e(urlparse(r["url"]).path or "/")}</a>
<div class="t">{e(r.get("title"))}</div>
<div class="h"><b>H1</b> {e(r.get("h1") or "none")}</div>
<div class="tags">{"".join(tags)}</div>
<div class="s">{e(r.get("words",0))} words · {e(inlinks.get(r["url"],0))} pages link here · status {e(st)}</div>
{f'<div class="s">Ends at {e(r.get("final_url"))}</div>' if r.get("redirected") else ""}
</div></div>''')
            body.append(f'<section id="s-{i}"><h2>{e(sec)} <span>{len(rows)} pages</span></h2><div class="grid">{"".join(cards)}</div></section>')
        doc = f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Tata Capital Site Inventory</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
:root{{--blue:#1961AC;--ink:#14213d;--mut:#5b6b82;--pale:#eef4fb;--line:#d9e3ef}}
*{{box-sizing:border-box}}body{{margin:0;font:14px/1.45 system-ui,-apple-system,Segoe UI,sans-serif;color:var(--ink);background:#f6f9fc}}
header{{position:sticky;top:0;z-index:5;background:#fff;border-bottom:1px solid var(--line);padding:14px 24px}}
h1{{margin:0 0 6px;font-size:20px}}.sum{{color:var(--mut)}}.sum b{{color:var(--ink)}}
.bar{{display:flex;gap:12px;align-items:center;margin-top:10px;flex-wrap:wrap}}
input,select{{font:inherit;padding:7px 10px;border:1px solid var(--line);border-radius:8px}}
.wrap{{display:flex}}nav{{width:240px;flex:none;position:sticky;top:118px;height:calc(100vh - 118px);overflow:auto;padding:12px;border-right:1px solid var(--line);background:#fff}}
nav a{{display:flex;justify-content:space-between;padding:5px 8px;border-radius:6px;color:var(--ink);text-decoration:none;font-size:13px}}nav a:hover{{background:var(--pale)}}
nav b{{color:var(--mut);font-weight:500}}main{{flex:1;padding:16px 24px;min-width:0}}
section h2{{font-size:16px;margin:22px 0 10px;padding:8px 12px;background:var(--pale);border-radius:8px}}section h2 span{{color:var(--mut);font-weight:400;font-size:13px}}
.grid{{display:grid;grid-template-columns:repeat(auto-fill,minmax(var(--w,380px),1fr));gap:14px}}
.card{{background:#fff;border:1px solid var(--line);border-radius:12px;overflow:hidden;position:relative}}
.num{{display:inline-block;margin-right:6px;background:var(--ink);color:#fff;font-size:11px;font-weight:600;padding:1px 7px;border-radius:10px;vertical-align:1px}}
.shots{{display:flex;gap:6px;background:#e9eff6;height:var(--h,260px);overflow:hidden;padding:6px}}
.shots a{{flex:3;overflow:hidden;border-radius:6px;background:#fff}}.shots a.mob{{flex:1}}
.shots img{{width:100%;display:block}}
.meta{{padding:10px 12px}}.u{{color:var(--blue);word-break:break-all;font-weight:600;text-decoration:none}}
.t{{margin:3px 0;font-weight:500}}.h,.s{{color:var(--mut);font-size:12.5px}}
.tags{{margin:6px 0;display:flex;flex-wrap:wrap;gap:4px}}.tags i{{font-style:normal;font-size:11.5px;padding:2px 8px;border-radius:10px;background:var(--pale)}}
.tags i.bad{{background:#fde2e2;color:#9b1c1c}}.tags i.warn{{background:#fff3cd;color:#7a5a00}}.tags i.off{{background:#e6e1fb;color:#4b2fa0}}
</style></head><body>
<header><h1>Tata Capital Site Inventory</h1>
<div class="sum"><b>{len(recs)}</b> pages · <b>{n_redir}</b> redirect · <b>{n_off}</b> end on another host · <b>{n_err}</b> errors · <b>{len(self.docs)}</b> documents · captured {time.strftime("%b %d, %Y")}</div>
<div class="bar"><input id="q" placeholder="Filter by URL or title" size="34">
<label>Card size <select id="z"><option value="300,200">Small</option><option value="380,260" selected>Medium</option><option value="560,420">Large</option></select></label></div></header>
<div class="wrap"><nav>{nav}</nav><main>{"".join(body)}</main></div>
<script>
const q=document.getElementById('q');q.oninput=()=>{{const v=q.value.toLowerCase();document.querySelectorAll('.card').forEach(c=>c.style.display=c.dataset.q.includes(v)?'':'none')}};
document.getElementById('z').onchange=e=>{{const[w,h]=e.target.value.split(',');document.documentElement.style.setProperty('--w',w+'px');document.documentElement.style.setProperty('--h',h+'px')}};
</script></body></html>'''
        with open(os.path.join(self.out, "Tata Capital Site Inventory.html"), "w", encoding="utf-8") as f:
            f.write(doc)


def main():
    ap = argparse.ArgumentParser(description="Inventory and screenshot tatacapital.com")
    ap.add_argument("--start", default="https://www.tatacapital.com/")
    ap.add_argument("--out", default="tc_inventory")
    ap.add_argument("--max-pages", type=int, default=6000)
    ap.add_argument("--workers", type=int, default=3, help="pages open at once (keep it low and polite)")
    ap.add_argument("--delay", type=float, default=0.5, help="seconds each worker waits between pages")
    ap.add_argument("--timeout", type=int, default=45, help="seconds before a page load gives up")
    ap.add_argument("--settle", type=int, default=1200, help="ms to wait after load for late content")
    ap.add_argument("--quality", type=int, default=60, help="JPEG quality")
    ap.add_argument("--main-only", action="store_true", help="crawl www only; list subdomains without crawling them")
    ap.add_argument("--exclude", default=r"/(search|logout)\b|\?", help="regex of URLs to skip")
    ap.add_argument("--no-mobile", action="store_true", help="skip the 360 screenshots (about twice as fast)")
    ap.add_argument("--no-sitemap", action="store_true")
    ap.add_argument("--headed", action="store_true", help="show the browser window (helps if the site blocks headless)")
    ap.add_argument("--chrome", action="store_true", help="use your installed Google Chrome instead of Playwright's Chromium")
    ap.add_argument("--batch-pages", type=int, default=0, help="stop after this many new pages (0 = no limit)")
    ap.add_argument("--time-limit", type=int, default=0, help="stop after this many minutes (0 = no limit)")
    ap.add_argument("--recapture", default="", help="file of URLs to capture again even if already done")
    ap.add_argument("--report-only", action="store_true", help="rebuild the HTML and CSVs from the last run, no crawling")
    ap.add_argument("--fresh", action="store_true", help="ignore the earlier run and start again")
    a = ap.parse_args()
    c = Crawler(a)
    if a.report_only:
        c.load_done()
        c.write_outputs()
        return
    try:
        asyncio.run(c.run())
    except KeyboardInterrupt:
        print("\nStopped. Writing reports from what was captured; run the same command again to resume.")
        c.done.clear()
        c.load_done()
        c.write_outputs()


if __name__ == "__main__":
    main()
