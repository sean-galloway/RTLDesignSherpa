---
name: doc-placement
description: What kind of documentation lives where in this repo - handbook (method) vs docs/markdown (reader-facing) vs vault/Tasks (work) vs beside-code (CLAUDE.md, PRD). The rule that a beside-code README is a link, never a standalone guide, and that style guides / how-tos never live in the RTL tree. Use before creating, moving, or "tidying" any .md file, and when reviewing an area's meta-docs.
---

# doc-placement

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/authoring/doc-placement.md - the four homes,
the five rules, and the case each came from.

The three that get violated most:
- **Methodology never lives in the RTL tree.** A style guide, how-to, or
  standalone guide beside code belongs in vault/handbook/ (method) or
  docs/markdown/ (reader-facing). A style guide in rtl/ is always wrong.
- **A beside-code README is a LINK, not a second copy.** If a dir needs a
  quick-start, it lives in docs/markdown/ and the README points at it.
- **One source per fact.** A count/spec/port list stated in two files rots -
  one gets updated, the other does not. Derive it or state it once and link.

Leave alone: files the tooling READS (bin/review/REVIEWER_BRIEF.md, the raw
docs/review/kimi/** critiques) are artifacts, not docs. A subsystem CLAUDE.md
and an area PRD.md legitimately stay beside code.

When you find a violation: git mv (history follows), repoint referrers
(including ~50 generated `# Documentation:` code headers), leave a link, link-check.

The handbook root is vault/handbook/INDEX.md. When you learn a durable lesson in
this domain, ADD IT TO THE HANDBOOK NOTE (doc-placement.md), not to this skill.
