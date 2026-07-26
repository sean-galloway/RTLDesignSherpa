---
name: module-docs
description: Authoring a per-module reference page under docs/markdown (rtl-common/rtl-math/rtl-amba) - the local .md style (header table, Overview, Architecture, Top-level Interface, Data model, Timing, Related, Test) and the SV header block that mirrors it. Use whenever you add or change an RTL block and need its docs/markdown page, and keep the book index in sync.
---

# module-docs

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/authoring/module-doc-template.md - the section
structure every per-module page follows, plus the SV header block that mirrors it.

The rules that get violated most:
- **One source per fact.** A port list / parameter table stated in both the `.sv`
  and the `.md` rots. State it once; when you change ports, update BOTH in the
  same commit (the `.sv` header and the `.md` interface block).
- **Follow an existing sibling.** New `docs/markdown/rtl-amba/monitor/*.md` pages
  copy the header table and section order of a peer (e.g. `monbus_compressor.md`),
  not a blank template.
- **Keep the book index in sync.** A new page MUST be linked from its
  `_book_<area>_index.md` (e.g. `docs/markdown/rtl-amba/_book_monitor_index.md`),
  or the generated PDF book never includes it.
- **No emojis in pipeline docs** - they break the LaTeX/PDF path. See [[doc-pipeline]].
- Placement rules (which .md lives where) are a separate concern - see the
  `doc-placement` skill / [[doc-placement]].

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE ([[module-doc-template]]), not to this skill.
