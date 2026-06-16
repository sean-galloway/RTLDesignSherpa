# Documentation style convention

**Rule:** All documents must follow the RTL Design Sherpa house style
**unless** the document is a *throwaway* or a *tracking* file.

## House style (deliverables)

Any doc that ships or is reviewed as a deliverable is rendered through
the house PDF pipeline: `bin/md_to_docx.py` driven by a style YAML
cloned from `projects/components/stream/docs/stream_mas/stream_styles.yaml`.

That gives the standard look:
- Sherpa logo title page
- Forest-green (`#228B22`) / dark-gray (`#404040`) heading scheme
- Three-part footer: `{title}  |  Open Source - Apache 2.0 License  |  Page N of M`
- Table of contents, numbered sections, List of Tables (LoF/LoW only when relevant)
- Noto font family, PDF rendered from the styled DOCX via LibreOffice

### Reference generators

- `projects/NexysA7/stream_characterization/docs/generate_pdf.sh` — the STREAM characterization report
- `projects/components/stream/docs/generate_{has,mas}_pdf.sh` — STREAM HAS / MAS specs
- `projects/NexysA7/stream_characterization/reports/generate_reports_pdf.sh` — perf + compression reports

Clone the closest one and point it at the new Markdown source + a style YAML.

## Exempt (plain Markdown, no styling)

- **Throwaway docs** — scratch, transient run notes, one-off analysis.
- **Tracking files** — trackers, `TASKS.md`, plan/status docs meant for
  internal use (e.g. `dma_observer_integration_tracker.md`).

When it is unclear whether a doc is a deliverable or just tracking,
treat it as a deliverable (or ask).
