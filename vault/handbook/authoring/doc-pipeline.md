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

## No emojis anywhere in this path

They break LaTeX. See [[humanization-voice]] - a generative rewrite is the most
common way they get reintroduced.

Related: [[kimi-review-rounds]] reviews this Markdown before it is generated.
