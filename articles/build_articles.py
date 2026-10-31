#!/usr/bin/env python3
"""Build the articles section of the RTLDesignSherpa Pages site.

Reads `articles/*.md` (front matter + markdown), writes into the staged site
root:

    <site>/articles/index.html          article index, newest first
    <site>/articles/<slug>/index.html   one page per article
    <site>/articles/feed.xml            RSS 2.0 feed (Medium/DEV.to import)
    <site>/articles/assets/*            figures, copied verbatim
    <site>/articles/medium/*            Medium-specific import pages, copied verbatim

Usage:
    python3 articles/build_articles.py <site_root>     # build
    python3 articles/build_articles.py --check <tmp>   # build + validate

Front matter (required unless draft: true):

    ---
    title: A Monitor Fabric That Never Stalls the Bus
    date: 2026-10-20
    summary: One or two sentences; becomes the RSS description.
    tags: monitors, soc          # optional, comma-separated
    draft: true                  # optional: skip this article
    ---

Slug: the filename stem, with a leading YYYY-MM-DD- date prefix stripped.
Image sources under `assets/` are rewritten to absolute site URLs so the RSS
feed is portable to Medium's importer (which fetches images from the feed).
The site base URL defaults to the repo's Pages URL and can be overridden with
SITE_BASE_URL (forks).
"""

import argparse
import datetime
import email.utils
import html
import os
import re
import shutil
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ARTICLES_DIR = Path(__file__).resolve().parent
REPO_ROOT = ARTICLES_DIR.parent

SITE_BASE_URL = os.environ.get(
    'SITE_BASE_URL', 'https://sean-galloway.github.io/RTLDesignSherpa')
SITE_TITLE = 'RTL Design Sherpa — Articles'
FEED_DESCRIPTION = ('Articles from the RTL Design Sherpa project: '
                    'learning hardware design through practice.')

FRONT_MATTER_RE = re.compile(r'\A---\n(.*?)\n---\n', re.S)
DATE_PREFIX_RE = re.compile(r'^(\d{4}-\d{2}-\d{2})-(.*)$')
IMAGE_RE = re.compile(r'(!\[[^\]]*\]\()assets/([^)\s]+)(\))')

STYLE = """
body { font-family: Georgia, serif; max-width: 44rem; margin: 2rem auto;
       padding: 0 1rem; color: #1a1a1a; line-height: 1.55; }
header.site { border-bottom: 2px solid #0b5cad; margin-bottom: 2rem;
              padding-bottom: 0.5rem; }
header.site a { color: #0b5cad; text-decoration: none; }
h1 { font-size: 1.6rem; } h2 { font-size: 1.25rem; margin-top: 2rem; }
img { max-width: 100%; }
.meta { color: #666; font-size: 0.9rem; }
pre { background: #f4f4f4; padding: 0.8rem; overflow-x: auto;
      font-size: 0.85rem; }
code { background: #f4f4f4; padding: 0 0.2em; }
pre code { background: none; padding: 0; }
table { border-collapse: collapse; } td, th { border: 1px solid #ccc;
        padding: 0.3rem 0.6rem; }
ul.articles { list-style: none; padding: 0; }
ul.articles li { margin-bottom: 1.5rem; }
footer { margin-top: 3rem; border-top: 1px solid #ccc; color: #666;
         font-size: 0.85rem; padding-top: 0.5rem; }
"""


def parse_front_matter(text):
    """Return (meta dict, body). Meta values are plain strings."""
    m = FRONT_MATTER_RE.match(text)
    if not m:
        return {}, text
    meta = {}
    for line in m.group(1).splitlines():
        if ':' not in line:
            continue
        key, _, value = line.partition(':')
        meta[key.strip()] = value.strip()
    return meta, text[m.end():]


def article_url(slug):
    return f'{SITE_BASE_URL}/articles/{slug}/'


def collect_articles():
    """Parse every article file. Returns (articles, errors)."""
    articles = []
    errors = []
    for md in sorted(ARTICLES_DIR.glob('*.md')):
        if md.name in ('README.md',):
            continue
        text = md.read_text(encoding='utf-8')
        meta, body = parse_front_matter(text)
        if meta.get('draft', '').lower() == 'true':
            continue

        stem = md.stem
        m = DATE_PREFIX_RE.match(stem)
        slug = m.group(2) if m else stem

        for field in ('title', 'date', 'summary'):
            if not meta.get(field):
                errors.append(f'{md.name}: missing front-matter "{field}"')
        date = meta.get('date', '')
        try:
            pub = datetime.date.fromisoformat(date)
        except ValueError:
            if date:
                errors.append(f'{md.name}: bad date "{date}" (want YYYY-MM-DD)')
            pub = None

        # Every referenced image must exist.
        for im in IMAGE_RE.finditer(body):
            if not (ARTICLES_DIR / 'assets' / im.group(2)).is_file():
                errors.append(f'{md.name}: missing image assets/{im.group(2)}')

        if not errors or all(md.name not in e for e in errors):
            articles.append({
                'slug': slug, 'meta': meta, 'body': body, 'pub': pub,
                'source': md.name,
            })

    slugs = [a['slug'] for a in articles]
    for s in set(slugs):
        if slugs.count(s) > 1:
            errors.append(f'duplicate slug "{s}"')

    articles.sort(key=lambda a: a['pub'] or datetime.date.min, reverse=True)
    return articles, errors


def render_html(body):
    """Markdown to HTML; assets/ image links become absolute site URLs."""
    try:
        import markdown
    except ImportError:
        sys.exit('pip install markdown  (the only dependency)')
    body = IMAGE_RE.sub(
        lambda m: f'{m.group(1)}{SITE_BASE_URL}/articles/assets/{m.group(2)}{m.group(3)}',
        body)
    return markdown.markdown(body, extensions=['fenced_code', 'tables'])


def page(title, content):
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(title)} — RTL Design Sherpa</title>
<link rel="alternate" type="application/rss+xml" title="{html.escape(SITE_TITLE)}"
      href="{SITE_BASE_URL}/articles/feed.xml">
<style>{STYLE}</style>
</head>
<body>
<header class="site"><a href="{SITE_BASE_URL}/articles/">{html.escape(SITE_TITLE)}</a></header>
{content}
<footer>From the <a href="https://github.com/sean-galloway/RTLDesignSherpa">RTLDesignSherpa</a>
project · <a href="{SITE_BASE_URL}/articles/feed.xml">RSS</a></footer>
</body>
</html>
"""


def build_index(out_dir, articles):
    items = []
    for a in articles:
        date = a['pub'].isoformat() if a['pub'] else ''
        items.append(
            f'<li><a href="{article_url(a["slug"])}">{html.escape(a["meta"]["title"])}</a>'
            f'<br><span class="meta">{date}</span>'
            f'<br>{html.escape(a["meta"]["summary"])}</li>')
    content = ('<h1>Articles</h1>\n<ul class="articles">\n' +
               '\n'.join(items) + '\n</ul>')
    (out_dir / 'index.html').write_text(page('Articles', content), encoding='utf-8')


def build_articles(out_dir, articles):
    for a in articles:
        meta = a['meta']
        tags = meta.get('tags', '')
        head = (f'<h1>{html.escape(meta["title"])}</h1>\n'
                f'<p class="meta">{a["pub"].isoformat() if a["pub"] else ""}'
                + (f' · {html.escape(tags)}' if tags else '') + '</p>')
        dest = out_dir / a['slug']
        dest.mkdir(parents=True, exist_ok=True)
        (dest / 'index.html').write_text(
            page(meta['title'], head + render_html(a['body'])), encoding='utf-8')


def build_feed(out_dir, articles):
    """RSS 2.0 with content:encoded; all URLs absolute (Medium import-safe)."""
    items = []
    for a in articles:
        meta = a['meta']
        url = article_url(a['slug'])
        pub = ''
        if a['pub']:
            dt = datetime.datetime(a['pub'].year, a['pub'].month, a['pub'].day,
                                   tzinfo=datetime.timezone.utc)
            pub = email.utils.format_datetime(dt)
        items.append(f"""  <item>
    <title>{html.escape(meta['title'])}</title>
    <link>{url}</link>
    <guid isPermaLink="true">{url}</guid>
    <pubDate>{pub}</pubDate>
    <description>{html.escape(meta['summary'])}</description>
    <content:encoded><![CDATA[{render_html(a['body'])}]]></content:encoded>
  </item>""")

    feed = f"""<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0" xmlns:content="http://purl.org/rss/1.0/modules/content/">
<channel>
  <title>{html.escape(SITE_TITLE)}</title>
  <link>{SITE_BASE_URL}/articles/</link>
  <description>{html.escape(FEED_DESCRIPTION)}</description>
{chr(10).join(items)}
</channel>
</rss>
"""
    (out_dir / 'feed.xml').write_text(feed, encoding='utf-8')


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('site_root', help='staged site root (articles/ goes under it)')
    ap.add_argument('--check', action='store_true',
                    help='validate strictly: any problem exits non-zero')
    args = ap.parse_args()

    articles, errors = collect_articles()
    for e in errors:
        print(f'ERROR: {e}', file=sys.stderr)
    if errors and args.check:
        sys.exit(1)
    if not articles:
        print('no articles found (all drafts?)', file=sys.stderr)
        if args.check:
            sys.exit(1)

    out_dir = Path(args.site_root) / 'articles'
    out_dir.mkdir(parents=True, exist_ok=True)
    assets_src = ARTICLES_DIR / 'assets'
    if assets_src.is_dir():
        shutil.copytree(assets_src, out_dir / 'assets', dirs_exist_ok=True)
    medium_src = ARTICLES_DIR / 'medium'
    if medium_src.is_dir():
        shutil.copytree(medium_src, out_dir / 'medium', dirs_exist_ok=True)

    build_index(out_dir, articles)
    build_articles(out_dir, articles)
    build_feed(out_dir, articles)

    # The feed must parse, and every article page must exist.
    ET.parse(out_dir / 'feed.xml')
    for a in articles:
        if not (out_dir / a['slug'] / 'index.html').is_file():
            sys.exit(f'missing output page for {a["slug"]}')

    print(f'articles: {len(articles)} page(s) + index + feed.xml -> {out_dir}')
    if errors:
        print(f'(non-fatal, {len(errors)} problem(s) above; --check would fail)',
              file=sys.stderr)


if __name__ == '__main__':
    main()
