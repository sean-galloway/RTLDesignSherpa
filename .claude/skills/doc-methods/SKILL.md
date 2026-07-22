---
name: doc-methods
description: The Sherpa documentation pipeline - md_to_docx with --style, LoF/LoT/LoW caption encoding, book indexes, RTL PDF generation, HAS/MAS vs operator guides. Use before generating or restructuring any deliverable doc.
---

# Sherpa doc pipeline

Canonical how-to: bin/DOC_GENERATION.md. Read it before generating anything.

Non-negotiables:
- Deliverable docs render through the house pipeline; throwaway/tracker files
  stay plain markdown.
- md_to_docx.py MUST get --style (forces LibreOffice DOCX->PDF; without it,
  pandoc+lualatex path is broken on this host).
- LoF/LoT/LoW entries are encoded in CAPTIONS, not flags. Losing caption
  encoding silently empties those lists.
- NO EMOJIS in anything the LaTeX/PDF path consumes.
- Book indexes follow links recursively; a page rename breaks book assembly.
- RTL library books: docs/markdown/generate_rtl_pdfs.sh (LC_ALL=C for stable
  section order). Component specs: per-project generate_pdf.sh, all
  skeleton-identical - do not let them drift.
- HAS/MAS spec books are different documents from operator GUIDEs; do not mix.
