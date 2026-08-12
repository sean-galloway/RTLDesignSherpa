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

## Captions and lists

- Table captions use the pandoc form `: Table N.M: ...` after the
  table; figure/waveform headings use `Figure N:` / `Waveform N:` —
  these populate the LoT/LoF/LoW in the built document. A caption
  dropped in an edit silently breaks book generation.
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
`projects/components/bridge/docs/generate_{has,mas}_pdf.sh`,
`projects/components/converters/docs/generate_mas_pdf.sh` — all take
`--rev <version>`.
