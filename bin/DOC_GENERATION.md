# Doc Generation — the RTL Design Sherpa PDF pipeline

How to author and render a styled, chapterized DOCX/PDF (specs, reports, and
per-project guides) with `bin/md_to_docx.py`. This is the *mechanics* reference;
`projects/NexysA7/stream_characterization/docs/DOC_STYLE.md` is the *policy*
(what must be styled vs. left as plain Markdown).

Read this before standing up a new document unit so you don't re-derive the
non-obvious parts (the caption encoding, the LibreOffice `--style` path, the
`mmdc --no-sandbox` trap).

---

## TL;DR — stand up a new doc in 6 steps

1. `mkdir` a document unit `<doc>/` with `assets/{images,mermaid,wavedrom}` and
   `chNN_*/` chapter dirs (layout below).
2. Copy a `styles.yaml` from a reference guide; edit only the `title_page` block.
   Copy `docs/logos/Logo_400px.png` to `assets/images/logo.png`.
3. Write `<doc>_index.md` listing the chapters in order (this is the build input).
4. Write chapters as `chNN_*/NN_*.md`. **Caption every table and diagram**
   (see "Lists" — this is what populates LoF/LoT/LoW).
5. Copy a `generate_<doc>_pdf.sh`; point it at your index/style/assets.
6. `./generate_<doc>_pdf.sh` → `<Name>_v<rev>.docx` + `.pdf`.

Reference implementations to clone:
- **Guide** (per-project, operator/dev): `projects/NexysA7/cdc_counter_display/docs/cdc_demo_guide/` + `docs/generate_guide_pdf.sh`
- **Spec** (HAS/MAS): `projects/components/dmas/stream/docs/stream_mas/` + `generate_mas_pdf.sh`
- **Report** (single-file): `projects/NexysA7/stream_characterization/docs/generate_pdf.sh`

---

## Anatomy of a document unit

A "document unit" owns everything for one PDF. It is self-contained:

```
docs/
├── generate_<doc>_pdf.sh          thin wrapper around bin/md_to_docx.py
└── <doc>/                         e.g. cdc_demo_guide/ , stream_mas/
    ├── <doc>_index.md             chapter hierarchy — the BUILD INPUT
    ├── <doc>_styles.yaml          branding (see "Branding")
    ├── title.md                   title page (LaTeX titlepage block)
    ├── chNN_<name>/NN_<section>.md   chapters (ordered by the index)
    └── assets/
        ├── images/logo.png        per-doc logo
        ├── mermaid/  NN_*.mmd + NN_*.png   source + rendered block/flow diagrams
        └── wavedrom/ NN_*.json + NN_*.svg  source + rendered timing diagrams
```

The generate script and the styles `title_page` are the ONLY per-doc-specific
pieces; the branding block and the chapter conventions are identical across docs.

---

## The build input: `<doc>_index.md`

`md_to_docx.py --expand-index` reads the index and **inlines the linked chapter
`.md` files in the order they appear**. `--skip-index-content` drops the index's
own prose (so the index can carry quick-reference tables without them landing in
the body). The index therefore defines the document structure:

```markdown
# <Doc Title>
**Version:** 0.90

## Document Organization

### Chapter 1: Overview
- [What It Is](ch01_overview/01_overview.md)

### Chapter 2: How It Works
- [Architecture](ch02_how_it_works/01_architecture.md)
```

Chapter files start with a top-level `#` heading; sections use `##`, `###`.
`--pagebreak` starts each concatenated chapter on a new page.

---

## Lists (LoF / LoT / LoW) — THE thing people get wrong

Getting a populated list needs **two** independent things, and each has its own
failure mode:

1. **The list must be enabled** — and *how* depends on which PDF route you are on
   (see [Enabling the lists](#enabling-the-lists-style-yaml-vs-cli-flags) below).
   Get this wrong and the section does not appear at all.
2. **Entries must be caption-encoded in the Markdown**, which the DOCX
   post-processor (`add_lists_to_docx` in `md_to_docx.py`) scans for. Plain
   `![alt](img)` images and bare tables produce an **empty list** — the section
   renders with no entries under it.

The required encoding:

| List | Author it as | Mechanism |
|------|--------------|-----------|
| **Figures** | a heading `### Figure C.N: Title` on its own line, then the image | scanner matches Heading-styled `Figure N: …` |
| **Tables** | a Pandoc caption line `: Caption` (blank line, then `: text`) after the table | becomes the `Table Caption` style the scanner keys on |
| **Waveforms** | a heading `#### Waveform C.N: Title`, then the wavedrom image | scanner matches Heading-styled `Waveform N: …` |

: Caption encoding for the three lists

Examples:

```markdown
### Figure 2.1: Harness Spine

![Harness spine](../assets/mermaid/01_spine.png)

**Source:** [01_spine.mmd](../assets/mermaid/01_spine.mmd)
```

```markdown
| Signal | Dir | Width |
|--------|-----|-------|
| clk    | in  | 1     |

: Clock and reset
```

Notes:
- Figure/Waveform captions are **real headings** — they take a section number and
  render in-body. Use `###` if you want them in the main TOC (TOC depth is 3),
  `####` to keep them out of the TOC. (STREAM uses `###` for figures, `####` for
  waveforms.)
- Only enable a list you can populate: a doc with no timing diagrams should NOT
  enable `low` — an empty "List of Waveforms" is noise.

### Enabling the lists: style YAML vs CLI flags

**These are two different mechanisms for two different PDF routes. They are NOT
interchangeable, and the CLI flags are silently inert on the route this
methodology actually uses.**

| PDF route | Selected by | What enables the lists |
|-----------|-------------|------------------------|
| DOCX -> LibreOffice (**the standard route**) | passing `--style` | the style YAML `lists:` block (`lot` / `lof` / `low` booleans) |
| pandoc -> LaTeX | omitting `--style` | the `--lot` / `--lof` / `--low` CLI flags |

: How each PDF route enables LoF/LoT/LoW

In `md_to_docx.py` the DOCX path reads
`lists_config = config.get('lists', {})` (`md_to_docx.py:1161`, `:1567`) — it
reads the **style only** and never merges `args`. The CLI flags are consumed
elsewhere, emitting raw LaTeX `\listoftables` / `\listoffigures` /
`\listofwaveforms` (`md_to_docx.py:1617-1625`), which never executes on the
LibreOffice path.

**Consequence:** if you pass `--style` (every doc in this methodology does), then
`--lot/--lof/--low` on the command line do nothing. Set the booleans in the style
YAML. Leaving the flags on the command line is harmless but misleading — several
existing generate scripts still pass them, and their lists are in fact coming
from their style YAML.

**Sharing one style across several docs.** If a single style template serves
multiple books (as `docs/markdown/rtl_pdf_styles.yaml` does for the RTL library),
do not flip the booleans globally — a book whose sources lack caption encoding
would render empty lists. Make them per-book placeholders and substitute at build
time:

```yaml
lists:
  lot: __LOT__
  lof: __LOF__
  low: __LOW__
```

```bash
sed -e "s|__LOT__|${lot}|" -e "s|__LOF__|${lof}|" -e "s|__LOW__|${low}|" \
    "${STYLE_TMPL}" > "${tmpstyle}"
```

See `docs/markdown/generate_rtl_pdfs.sh` (`build_book`) for a working example.

---

## Diagrams

`md_to_docx.py` can render inline ```` ```mermaid ```` / ```` ```wavedrom ````
blocks at build time, but the current process **pre-renders and commits** the
images (source + rendered live together in the same asset dir), then references
them — stable, versioned, faster builds, no build-time renderer needed.

**Convention (as in `stream_mas`):**
- Diagram files: `assets/mermaid/NN_descriptive_name.{mmd,png,svg}` and
  `assets/wavedrom/name.{json,svg}`. (Naming is `NN_name`, not the older
  `_L<line>` scheme; the `assets/mermaid/README.md` describing `_L###` is stale.)
- Chapters reference **mermaid as `.png`**, **wavedrom as `.svg`**, each followed
  by a source link:

```markdown
### Figure 2.13.1: APB to Descriptor Block Diagram

![APB to Descriptor Block Diagram](../assets/mermaid/02_apbtodescr_block.png)

**Source:** [02_apbtodescr_block.mmd](../assets/mermaid/02_apbtodescr_block.mmd)
```

**Regenerate via the committed batch scripts** (one per asset dir), which already
handle the headless traps — do not hand-run `mmdc` ad hoc:

```bash
assets/mermaid/regenerate_all_diagrams.sh     # mmdc + puppeteer --no-sandbox -> .svg
assets/wavedrom/regenerate_all_waveforms.sh   # wavedrom-cli -i x.json -s x.svg
```

**Headless `mmdc` trap** (baked into `regenerate_all_diagrams.sh`): the Chromium
sandbox fails on Ubuntu 23.10+ ("No usable sandbox!"). The script writes a
puppeteer config `{"args":["--no-sandbox","--disable-setuid-sandbox"]}` and
passes it with `--puppeteerConfigFile`. Copy that script into a new doc's
`assets/mermaid/` and it just works.

Supported asset subdirs (the generate script lists all, populated or not):
`images`, `mermaid`, `wavedrom`, `draw.io`, `puml`.

---

## Chapter & front-matter conventions (as in `stream_mas`)

- **Heading levels:** chapter title `#` (H1), sections `##`, sub-sections `###`.
  Figure captions are `###` (H3, appear in the TOC); waveform captions are `####`
  (H4, below TOC depth).
- **Port lists / interfaces:** one `###` sub-section per signal group, each a
  table with a `: Caption` (so every interface lands in the LoT).
- **Code:** fenced blocks, language-tagged where useful (```` ```systemverilog ````).
- **Callouts:** inline bold `**Note:**` / `**Important:**` — no admonition blocks.
- **Front matter** (`ch00_front_matter/00_document_info.md`): a short intro, a
  **References** table (with `: Related Documents` caption), a **Terminology**
  glossary (`**Term**` on its own line, definition below), and a **Revision
  History** table.

## Legacy cruft to ignore (do not copy)

In older units you may find:
- `cmd` — a hand-path build script (`/mnt/.../rtldesignsherpa/bin/...` hardcoded,
  no `--lof/--lot`). Superseded by `generate_<doc>_pdf.sh`.
- `assets/mermaid/README.md` — documents an old `stream_spec/` path and `_L###`
  naming. The live convention is `NN_name.{mmd,png,svg}` + the regenerate scripts.

Anchor on `generate_<doc>_pdf.sh` + `regenerate_all_*.sh`, not those.

## Branding (`<doc>_styles.yaml`)

One YAML carries the whole brand. **Keep the non-title blocks identical across
docs** so the series reads as one; only `title_page` varies per doc. Blocks:
`company`, `colors` (primary `#228B22` green / secondary `#404040`),
`fonts`, `headings` (per-level size/color/spacing), `body`, `tables`, `captions`,
`header_footer` (footer tokens `{title} {version} {confidential} {page}`),
`margins`, `lists` (`lot/lof/low` booleans), and `title_page`
(`logo`, `title`, `subtitle`, `date`, colors/sizes).

---

## The generate script

A thin, near-identical wrapper. The only per-doc lines are `DOC`, the index, and
the style file. Canonical invocation (from the reference guide):

```bash
python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${DOC}/${DOC}_index.md" "${OUTPUT_DOCX}" \
  --style "${DOC}/${DOC}_styles.yaml" \
  --title-page "${DOC}/title.md" \
  --expand-index --skip-index-content \
  --toc --number-sections \
  --pdf --pagebreak --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" --mathfont "Noto Serif" \
  --assets-dir "${DOC}/assets" \
  --assets-dir "${DOC}/assets/images" \
  --assets-dir "${DOC}/assets/mermaid" \
  --assets-dir "${DOC}/assets/wavedrom" \
  --quiet
```

Resolve `REPO_ROOT` with `git rev-parse --show-toplevel` (move-proof). One
`--assets-dir` per asset subdir.

**LoF/LoT/LoW are not on this command line by design.** Because `--style` is
passed, the lists come from the style YAML `lists:` block, not from
`--lot/--lof/--low` — see
[Enabling the lists](#enabling-the-lists-style-yaml-vs-cli-flags). Enable only
the lists the doc can populate. (Older generate scripts still pass `--lof --lot`
here; those flags are inert on this route and can be dropped.)

---

## Toolchain and gotchas

Requires: `pandoc`, a LaTeX engine (`lualatex`/`xelatex`), `libreoffice`
(`soffice`), `mmdc` (@mermaid-js/mermaid-cli), `wavedrom-cli`, and the Noto font
family (`Noto Serif`, `Noto Sans`, `Noto Sans Mono`).

- **`--style` routes the PDF through LibreOffice**, not LaTeX. When `--style` is
  given, `md_to_docx.py` styles the DOCX and converts DOCX→PDF via `soffice`
  (`writer_pdf_Export`). Consequences: the `--pdf-engine`/`--mainfont` flags are
  **inert on that path** (LibreOffice substitutes the `fonts:` from the style
  YAML), **`--lot/--lof/--low` are inert on that path** (the style YAML `lists:`
  block enables them instead), and list entries come from the **DOCX caption
  scanner** above, not LaTeX `\listof*`. Without `--style`, the PDF is built by pandoc + the LaTeX engine
  (needs Unicode-friendly fonts; the default `lmroman10` has broken metrics in
  some environments — pass Noto).
- **`--skip-index-content`** means quick-reference tables in the index do NOT
  appear in the body. Put content you want rendered in a chapter, not the index.
- **Emoji / Unicode** in section text can break the LaTeX path; keep technical
  docs plain (see the root CLAUDE.md "no emojis in technical specifications").
- **Move-proofing:** never hardcode `../../../..`; use
  `git -C "$SCRIPT_DIR" rev-parse --show-toplevel`.

---

## Verifying a build

```bash
pdfinfo <Name>.pdf | grep Pages                       # page count
pdftotext <Name>.pdf - | grep -inE "list of (tables|figures|waveforms)"  # sections present?
pdftotext <Name>.pdf - | grep -A 10 "List of Waveforms"                  # entries under them?
unzip -l <Name>.docx | grep media                     # images embedded?
```

Check the two failure modes separately — they look similar in a PDF viewer but
have different causes:

| Symptom | Cause | Fix |
|---------|-------|-----|
| List section **missing entirely** | the list is not enabled | set the boolean in the **style YAML** `lists:` block (the CLI flag does nothing when `--style` is passed) |
| List section present but **empty** | captions missing or not Heading-styled | revisit [Lists](#lists-lof-lot-low-the-thing-people-get-wrong) — `### Figure C.N:`, `#### Waveform C.N:`, `: Caption` |

: Diagnosing an absent vs an empty list

If an image is missing, its `--assets-dir` is not on the resource path or the
pre-render step didn't run.
