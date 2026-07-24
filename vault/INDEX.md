---
title: RTL Design Sherpa vault
summary: The repo's knowledge vault - handbook (method), Tasks (work), repo-wide-projects (area context).
---

# RTL Design Sherpa vault

Everything the repo knows that is not code. Open this directory as an Obsidian
vault; `[[wikilinks]]` resolve across all three areas because they share one
root.

| Area | Holds | Answers |
|---|---|---|
| **[handbook](handbook/INDEX.md)** | method and practice, as atomic wikilinked notes | "how do we do X here?" |
| **[Tasks](Tasks/INDEX.md)** | work items with an open/active/closed/dropped lifecycle | "what is in flight?" |
| **[repo-wide-projects](repo-wide-projects/INDEX.md)** | one note per RTL subsystem and project, mirroring the repo tree | "why is *this block* like this?" |

## Which one does a thing go in?

The distinction is worth holding, because putting a note in the wrong place is
how it stops being found:

- A rule that applies **everywhere** — reset conventions, how to run a
  regression, the filelist MUST — is a **handbook** note.
- A thing **to do**, with a beginning and an end, is a **task**.
- Durable context about **one area** — why pumice's arbiter guards a bank for
  two cycles, what bit someone on the RAPIDS beats rework — is a
  **repo-wide-projects** note.

## The rule that outranks all of this

[/GLOBAL_REQUIREMENTS.md](../GLOBAL_REQUIREMENTS.md) is the enforcement
authority and wins on any conflict. The vault records practice and rationale;
it does not override requirements.

## What does not live here

Methodology does **not** live next to the code — no `README.md` beside a tool
restating how to use it, no `TASKS.md` or `TODO.md` next to a module. A second
copy is how documentation rots: the copy nobody edits is the one the next
session reads. Point at the vault note instead.

Skills in `.claude/skills/` are **signposts only** — a skill names its canonical
handbook note and stops.
