# HAS/MAS spec document standards

Formatting requirements for the chaptered specification books
(`projects/components/*/docs/*_has`, `*_mas`) and their DOCX/PDF builds.
These came out of the v1.1 Bridge/Converters review (2026-08-11) and are
binding for new chapters and for edits to existing ones.

## Page layout

- **Numbered section headings always start on a new page.** "2.4
  Arbitration" opens a fresh page, every time. Mechanism: `md_to_docx.py`
  honors `page_break_before` per heading level; every book's styles YAML
  sets it on `h1` and `h2`. New books copy that.
- **Exception: the first subsection stays with its chapter heading.**
  A chapter heading whose first subsection also broke ended up alone
  above an empty page ("3 Overview", then "3.1" on the next). A heading
  that directly follows a shallower heading with no content between
  them does not break. The chapter still opens a fresh page; siblings
  (3.2, 3.3) still each start one. Handled automatically -- authors do
  nothing.
- **Verify page breaks in the PDF, not the DOCX.** LibreOffice's
  TOC-update pass rewrites paragraph formatting, so `python-docx` reads
  `page_break_before` as `None` on headings that do still break. The
  DOCX cannot be used to check this.
- **Title pages carry the build date and revision, stamped at build
  time.** The checked-in styles YAML holds placeholders only; each
  `generate_*_pdf.sh` writes a `.build.yaml` copy with today's date and
  `Specification ${REV}`, and cleans it up on exit. Never hand-edit a
  date or version into the YAML.

## Diagrams

- **Diagrams are Mermaid.** Block diagrams, dataflow, pipelines,
  state flows: ```` ```mermaid ```` fences, which the pipeline renders
  to PNG. No ASCII diagram art (box-drawing or arrow art) in any spec.
- **Directory trees and containment listings stay ASCII.** Box-drawing
  trees (`├──`/`└──`) are the preferred form for trees and pure
  listings — do not convert them to Mermaid or flatten them.
- **All waveforms are WaveDrom.** Timing/waveform figures use
  ```` ```wavedrom ```` fences (inline JSON, rendered by the pipeline)
  or a checked-in WaveDrom JSON asset with its rendered image — never
  ASCII waveform art, never hand-drawn timing sketches. Mermaid has no
  waveform type; WaveDrom is the only sanctioned tool for signals over
  time.

## Image sizing

- **Every image is fitted to the page automatically.** `md_to_docx.py`
  reads each rendered or referenced image, computes the largest size
  that fits inside the printable box preserving aspect ratio, and emits
  an explicit `{width=...}` attribute. Authors do not hand-size images
  and should not add width attributes of their own.
- The box is the page minus the margins in force (`--narrow-margins`
  is accounted for), minus an allowance so a full-height figure does
  not orphan its caption onto the next page.
- **Small images are never upscaled** — a compact diagram keeps its
  natural size rather than being stretched to the margins.
- This is why a very tall diagram appears small: it was scaled to fit
  the page height, not the width. If that makes it unreadable, the fix
  is to split the diagram, not to force a size.
- **The same trap runs the other way, and Graphviz walks into it by
  default.** A very WIDE figure is scaled to fit the page WIDTH, so its
  height collapses: an 11:1 strip lands about half an inch tall and no
  amount of zoom in the PDF viewer helps, because the pixels were thrown
  away at fit time. `rankdir=LR` with two or three `subgraph cluster_*`
  blocks reaches 5:1 or worse almost immediately -- the Nexys A7 system
  books first rendered at 11:1 and 6.8:1.
  **Aim for between about 0.7:1 and 2.5:1**, and check it rather than
  assuming: `identify -format '%wx%h'` on the rendered PNG. Two fixes,
  in order of preference:
    1. `rankdir=TB` instead of `LR`. A left-to-right chain of five stages
       is a strip; the same five stacked is page-shaped.
    2. For clusters that dot still places side by side, add edges between
       them with `style=invis` to force a vertical order. Invisible edges
       change layout only, so the diagram's meaning is untouched.
  Splitting is still right when the figure is genuinely two figures, but
  a wide diagram is usually one figure laid out badly, and re-laying it
  out costs a one-word change.

## Captions and lists

- Table captions use the pandoc form `: Table N.M: ...` on the line after
  the table; figures and waveforms are `### Figure N.M: Title` /
  `### Waveform N.M: Title` HEADINGS (chapter.number; `md_to_docx.py`'s
  detector accepts any dotted number, so a bare `Figure 3:` also lands).
  These populate the LoT/LoF/LoW in the built document; a caption written
  any other way is silently absent from its list, and one dropped in an edit
  silently breaks book generation. This was the whole point of the retired
  `projects/components/DOCUMENTATION_STANDARDS.md` (tooling TASK-004,
  2026-09-28); the flags and styles-YAML mechanics it also carried live in
  `bin/DOC_GENERATION.md`.
- No emoji anywhere in spec sources (breaks the LaTeX path).

## Voice

Prose follows the Kimi humanization guides:
`docs/kimi_humanization_style_guide.md` (voice) layered with
`docs/kimi_humanization_style_guide_has_mas.md` (container discipline —
what a voice pass must never touch, including the diagram/tree/waveform
rules above). Humanize BEFORE building versioned artifacts, not after.

## Build

One `--rev` per released artifact set; the same revision may be
rebuilt while unreleased. Build scripts:
`projects/components/fabric-gen-ip/bridge/docs/generate_{has,mas}_pdf.sh`,
`projects/components/utility-ip/converters/docs/generate_mas_pdf.sh` — all take
`--rev <version>`.
