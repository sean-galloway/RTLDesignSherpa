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

## Markdown references PNG, never SVG

Every image in a `![...]()` must be a `.png`. Mermaid and wavedrom both render
to PNG; an `.svg` may exist as an intermediate, but referencing it from Markdown
is not allowed. Convert first:

```bash
wavedrom-cli -i assets/wavedrom/name.json -s /tmp/name.svg
rsvg-convert -w 1600 -o assets/wavedrom/name.png /tmp/name.svg
```

**Cap the width.** Uncapped wavedrom output reaches 9920x4692 and costs
megabytes per figure -- three such assets alone took the STREAM MAS from 5.5 MB
to 11.3 MB of embedded media. 1600px is page width at print DPI.

**Use `rsvg-convert`, not `inkscape`.** The snap-confined inkscape on this
machine resolves a relative path against `$HOME`, cannot see a repo under
`/mnt/data`, and **exits 0 having written nothing** -- so `check=True` does not
catch it and a missing file is embedded silently.

*Why this note exists: `bin/DOC_GENERATION.md` said the opposite until
2026-09-21 -- it prescribed `wavedrom/ NN_*.json + NN_*.svg` and "chapters
reference wavedrom as `.svg`". Authors followed it, and rapids_beats_has
accumulated 24 image references to SVGs that were never rendered. All PNGs also
belong in an `assets/` folder ([[doc-placement]]).*

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

## A book is built from PAGES, so one page per module

`gen_index` globs `<book-dir>/*.md`. A page covering two modules is therefore
one entry, and a reader searching the book for the second module finds
nothing. Match the family you are in: apb4 gives each stub its own page, so
wb4 combining both into `wb4_stubs.md` was wrong and was split before the
book was built (2026-09-10).

## Verify a built book by its TEXT, not its exit code

The generator exits 0 while LibreOffice prints `failed to launch javaldx` and
other noise, so "it ran" is not "it contains what you think". Extract and
grep:

```bash
pdftotext docs/pdfs/RTL_AMBA_WB4.pdf - | grep -c wb4_slave_cdc_cg
```

*Case (2026-09-10): both the wb4 book (46pp, generated for the first time
though its entry had always been in the script) and the monitor book (424pp)
were checked this way -- every wb4 module named in the first, and the new
Wishbone monitor pages down to individual event codes in the second. The
monitor book needed no script change, because its generator globs
`rtl-amba/monitor/*.md` and `rtl-amba/includes/monitor_*.md` and so picks up
new pages on its own.*

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

## Two book conventions: fenced blocks vs committed PNGs

Both render. Do not "fix" one into the other, and do not mix them in one book.

- **PNG-ref books** (`stream_mas`, `stream_char_guide`, `rapids_char_guide`):
  the chapter carries `![Alt](../assets/<kind>/name.png)` plus a `**Source:**`
  link, and the asset dir holds the `.mmd`/`.json` source next to the `.png`.
  Regenerate with the committed `regenerate_all_*.sh` in that asset dir.
- **Fence books** (`rapids_beats_has`): the chapter carries a live
  ```` ```mermaid ```` / ```` ```wavedrom ```` block and `md_to_docx.py`
  renders it at build time. There is no asset to commit and no regen script.

Measured 2026-09-21: `rapids_beats_has` had picked up 19 image refs and 35
`**Source:**` links pointing at an asset layer that was never built -- 31 of
those targets never existed in git history -- while a live fence sat
immediately below each one carrying the real diagram. The three assets that
did exist had drifted from the fences above them (text similarity 0.11-0.41),
so they were stale, not sources. The fix was deleting the vestigial refs, not
rendering 70 PNGs to satisfy them. **Check which convention a book uses before
concluding a diagram is missing** -- a dead image ref above a live fence is
duplication, not a gap.

## Palette-encode committed diagram PNGs

`convert x.png -colors 64 PNG8:x.png` after rendering. Diagrams are flat line
art, so 64 colours is visually indistinguishable -- the only pixels that move
are antialias edges -- while the file drops by about two thirds. Measured on
`stream_mas`: 34 PNGs, 11.6 MB -> 3.6 MB, every dimension unchanged. Baked
into the canonical `regenerate_all_*.sh`.

Do NOT shrink the pixel dimensions to save bytes. Wavedrom and mermaid emit at
CSS pixel scale and the PDF path assumes 96 px/in, so a diagram rendered at 1x
is already soft once fitted to a page; the committed set is 2x the renderer's
natural width for that reason. Palette encoding buys the same saving with no
resolution cost at all.

## A heading directly above a fence becomes that figure's caption

`md_to_docx.py` compiles the mermaid and wavedrom block patterns with an
OPTIONAL leading heading group:

```python
r'(#{2,4}\s+(?:Figure\s+\d+[:\s]+)?[^\n]+\n+)?```mermaid\s*\n(.*?)\n```'
```

So `## Sink Path Data Flow` followed by blank lines and then a fence is
consumed: the text renders as the diagram's caption and the section stops
existing as a heading. Anything non-blank in between -- even an HTML comment --
prevents the match and keeps the heading.

This is the repo-wide norm, not a defect: measured 2026-09-21 there are 116
such adjacencies in `stream_mas` and 113 in `rapids_beats_mas`. Do not "fix"
one book with guard lines; that makes it the odd one out, and the title text
is preserved either way.

It does mean that **deleting a line between a heading and a fence silently
demotes that heading**. Clearing the dead image/`**Source:**` lines out of
`rapids_beats_has` created 30 new heading/fence adjacencies, which dropped 25
distinct titles out of the section set (several, like "Timing Diagram",
repeat) and took the book from 203 to 199 pages. No text was lost -- each
title still renders once, as the caption. Expect a page-count drop after that
kind of cleanup, and verify it by diffing the heading set rather than assuming
content vanished. Note the measurement trap: `pdftotext` output puts TOC lines
and body headings in the same shape, so a naive `^[0-9]+\.[0-9]+ Title` grep
counts both and will not answer this question cleanly.
