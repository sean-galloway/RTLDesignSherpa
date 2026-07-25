---
title: RTL Design Sherpa Handbook
summary: The repo's working memory - design rules, DV practice, FPGA process. Start here.
---

# Handbook

Atomic notes, one topic each. ``[[name]]`` (literal syntax) links resolve within this vault
(Obsidian-compatible). Indexes are navigation only - content lives in notes.

Authority order: /GLOBAL_REQUIREMENTS.md (enforced) > these notes (practice
and rationale) > code comments. On conflict, the requirement wins.

## Areas

- [design/](design/INDEX.md) - RTL design rules and the lessons behind them
- [dv/](dv/INDEX.md) - verification practice: BFMs, registers, seeds,
  coverage, formal, sandboxes
- [fpga/](fpga/INDEX.md) - board process: builds, timing triage, harness,
  board handling
- [authoring/](authoring/INDEX.md) - documentation practice: review rounds,
  voice, generation pipeline

## Skills

- [[skills]] - the reverse index: every `.claude/skills/` signpost and the
  handbook note it points at. Skills are signposts only; method lives in the note.

## House rules for the handbook itself

- One topic per note; link, never duplicate (duplication is how docs rot).
- Every note has title/summary frontmatter so indexes can be regenerated.
- A lesson earned by a real failure names the failure - the case study is
  the part a future reader trusts.
- No emojis (some notes get quoted into pipeline docs).
