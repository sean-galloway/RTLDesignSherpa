---
title: Doc pipeline
summary: How Markdown becomes a deliverable - md_to_docx --style, caption-encoded lists, RTL PDF books.
---

# Doc pipeline

Canonical how-to: `bin/DOC_GENERATION.md`. This note carries the decisions and
traps; the mechanics live there.

## --style picks the engine

`md_to_docx --style <template>` forces the LibreOffice DOCX -> PDF path.
Without `--style` it falls back to pandoc + lualatex, which is **broken in this
environment** (an lmroman10 font-metric failure). Every generation script must
pass `--style`. The STREAM/RAPIDS/pumice generator scripts are deliberately
skeleton-identical so this cannot drift between them.

## Lists of figures/tables/waveforms come from captions

LoF, LoT and LoW are built from caption encoding in the Markdown, not from a
command-line flag. A missing list means a miscaptioned figure, not a missing
option - look at the source, not the invocation.

## Two document species, different rules

- **HAS/MAS spec reports** - the formal architecture/microarchitecture specs.
  House style, no emojis, generated per component.
- **Operator guides** (e.g. the CDC demo guide) - per-project, task-oriented,
  written for someone at the board.

Do not merge their templates; they have different audiences and different
front matter.

## RTL library books

`docs/markdown/generate_rtl_pdfs.sh` builds the 12 `docs/RTL_*.pdf` books with
`--strip-doc-header`. When RTL moves between directories the book definitions
must move with it, or a book silently ships short.

## Diagrams: the PDF eats PNG, not SVG

Every `.mmd` needs a rendered `.png` beside it. An SVG-only diagram silently
does not appear in the PDF -- no error, no placeholder, just a missing figure.

The reason is which route the book takes. SVG survives pandoc+LaTeX, via the
`svg` package and inkscape (and `--shell-escape`). These books are built with
`md_to_docx.py --style`, which produces DOCX and hands it to LibreOffice for
the PDF, and SVG does not embed reliably through that. So the format guidance
depends on the route, and the route in use is the DOCX one.

*Case (2026-09-01): `docs/markdown/assets/*/DIAGRAM_PLAN.md` prescribed SVG
"to ensure PDF compatibility" -- exactly backwards for this pipeline. Following
it produced **153 diagrams with no PNG**, 139 of them SVG-only, across
rtl-amba, rtl-common and the rapids MAS/HAS books. Both plans now carry a
correction at the top.*

Keep the `.svg` if it exists -- it is fine for the web view and costs nothing.
The PNG is the one that has to be there.

    echo '{"args": ["--no-sandbox", "--disable-setuid-sandbox"]}' > /tmp/pup.json
    mmdc -i diagram.mmd -o diagram.png -b white -p /tmp/pup.json -s 2

The puppeteer config is not optional on this box: without it mmdc dies with
"No usable sandbox" (Chromium + AppArmor). `bin/md_to_docx.py` writes the same
config for its own inline rendering -- copy its flags rather than inventing
new ones.

**Check before shipping a book**, because nothing else will:

    find . -name '*.mmd' | while read m; do [ -f "${m%.mmd}.png" ] || echo "$m"; done

## No emojis anywhere in this path

They break LaTeX. See [[humanization-voice]] - a generative rewrite is the most
common way they get reintroduced.

Related: [[kimi-review-rounds]] reviews this Markdown before it is generated.

## The book index is GENERATED -- regenerate it, never hand-edit it

Every `docs/markdown/**/_book_*_index.md` is emitted by `gen_index` inside
`generate_rtl_pdfs.sh`, from `ls <book-dir>/*.md` with each page's H1 as the
link text. Each file says so in a banner on line 3. Two commits hand-edited
one anyway, directly under that banner, and a single build erased both edits.

Two consequences worth knowing before you touch one:

- **A page missing from a book means the index is STALE, not that a link is
  missing.** `axi5_atomic_filter.md` -- a real module with a full page -- was
  absent from the AXI5 PDF and from every review bundle ever built, because
  nobody had re-run the generator since the page was added. The bundler walks
  the same index the PDF does, so a stale index makes a page invisible to
  BOTH the book and the review process at once. Diagnosing that as "the link
  is missing" and hand-adding it fixes the symptom; the cause is that the
  generator had not been run.
- **Anything the generator cannot derive does not survive a build.** The axi4
  index carried two hand-added cross-component links into the converters MAS.
  `gen_index` globs one directory, so it drops them silently on the next
  build. Put cross-book pointers on a PAGE that lives in the book -- the
  `axi4_dwidth_converter.md` stub already carries both -- not in the index.

Before assuming regeneration is safe, model it: list what the generator would
emit against what the index currently links, and diff both directions. Losing
a page is a real regression; losing curated link TEXT is cosmetic and the
generator wins anyway.
