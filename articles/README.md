<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Articles

Long-form RDS writing, published to GitHub Pages by the `pages` workflow and
cross-posted to Medium / DEV.to from there. Source of truth is here in git;
the Pages site is the canonical public copy; Medium imports point back at it
with a canonical link, so search engines credit the Pages original.

## Writing one

One markdown file per article, named `YYYY-MM-DD-<slug>.md`:

```markdown
---
title: A Monitor Fabric That Never Stalls the Bus It Watches
date: 2026-10-20
summary: One or two sentences; becomes the RSS description and the index blurb.
tags: monitors, soc
---

Body markdown. Figures live in `assets/` and are referenced relative:

![caption](assets/my_figure.png)
```

Rules:

- `title`, `date`, `summary` are required. `tags` optional. `draft: true`
  keeps a file out of the build.
- Figures go in `assets/` and **must** be referenced as `assets/<file>` —
  the builder rewrites those to absolute URLs so Medium's importer can fetch
  them from the RSS feed. Any other image path shape will not travel.
- The URL slug is the filename stem minus the date prefix:
  `2026-10-20-foo.md` publishes at `…/articles/foo/`.
- House style applies: no emoji (they break the PDF pipeline discipline and
  read unprofessionally), diagrams follow
  `vault/handbook/authoring/block-diagrams.md`.

## Preview locally

```bash
pip install markdown   # the only dependency
python3 articles/build_articles.py /tmp/site
# open /tmp/site/articles/index.html
```

Strict validation (what CI runs):

```bash
python3 articles/build_articles.py --check /tmp/site-check
```

## Publishing flow

1. Merge to `main`. The `pages` workflow rebuilds the site: articles land at
   `https://sean-galloway.github.io/RTLDesignSherpa/articles/` with
   `feed.xml` beside them.
2. **Medium**: profile menu → Stories → **Import a story** → paste the
   article's Pages URL. Medium fetches the page, imports images, sets the
   canonical link back to Pages, and backdates to the front-matter date.
   (Medium retired its write API in 2023; import-by-URL is the sanctioned
   path.)
3. **DEV.to** (optional, zero-touch): Settings → Extensions → "Publishing
   from RSS" → point it at
   `https://sean-galloway.github.io/RTLDesignSherpa/articles/feed.xml`.
   New articles appear as drafts automatically, canonicals set.

## Files

- `build_articles.py` — the builder/validator (run by CI on every push that
  touches `articles/`; the deploy re-runs it into the staged site).
- `assets/` — figures referenced by the articles.
