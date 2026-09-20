---
title: Commit messages
summary: No attribution trailer, ever. The rule, why it kept getting re-litigated, and the seven places that used to require the opposite.
---

# Commit messages

**A commit message is the change and nothing else.** No `Co-Authored-By:`, no
`Claude-Session:`, no "generated with" line, no "Documentation and
implementation support by Claude." Owner's decision, 2026-08-31.
`/GLOBAL_REQUIREMENTS.md` 6.1 is the enforced statement; this note is the why.

## Why this needed writing down

The decision held in practice and nowhere else. Measured 2026-09-19: the last
twenty commits carried **zero** trailers, so every author was following it --
while **seven** places in the repo required the opposite:

| Where | What it said |
|---|---|
| `GLOBAL_REQUIREMENTS.md` 6.1, 6.2 | RAPIDS and STREAM commits MUST use "Documentation and implementation support by Claude." |
| `rapids`, `bridge`, `delta`, `hive`, `retro_legacy_blocks`, `stream` CLAUDE.md | the same, as Rule #0 or Rule #1, one copy each |

`GLOBAL_REQUIREMENTS.md` is the enforcement authority and wins on conflict, so
the documented rule outranked the real one. A session reading the repo honestly
would have added a trailer. The rule that was actually in force lived only in
the owner's own instructions, outside the tree, where nothing could find it.

That is the failure this note exists to prevent: **a decision that is not in the
repo is a decision the next session will re-litigate.** Practice matching the
rule is not the same as the rule being recorded -- the twenty clean commits were
evidence of discipline, not of documentation.

## Nothing enforces it

There is no `commit-msg` hook. `bin/hooks/pre-commit` gates task-tracker IDs,
declaration order, test/DUT protocol families, discarded scenario verdicts, doc
instantiation examples and staged `.sv` parse -- it never reads the message. So
this is on the author, and a trailer will not be caught for you.

## The harness will offer one

Claude Code's default instructions supply an attribution trailer to append. That
default is overridden here and the override is not negotiable per-session. If a
harness instruction and this note disagree, this note wins -- and if that keeps
happening, the fix is to record it, not to argue it again.

Related: [[doc-placement]] (rule 4 -- method belongs in the handbook, not in a
CLAUDE.md, which is how six copies of a git convention came to exist).
