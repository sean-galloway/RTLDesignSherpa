---
title: Commit messages
summary: No attribution trailer, ever. The rule, why it kept getting re-litigated, the commit-msg hook and CI job that enforce it since 2026-11-07, and why history was not rewritten.
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

## Enforced since 2026-11-07

Until then nothing checked it. `bin/hooks/pre-commit` runs before the message
exists, so it never read one, and the rule was kept by whoever remembered.
Measured 2026-11-07: of 2,944 commits on main since the decision on 2026-08-31,
**445** carried a trailer -- 417 `Claude-Session:` links, 20 `Co-authored-by:`
(Claude and Kimi Code), 5 `Assisted-by:` (Claude and Kimi). The twenty clean
commits of 2026-09-19 were a quiet stretch, not compliance.

Two gates now run one checker, `bin/check_commit_messages.py`:

- **`bin/hooks/commit-msg`** rejects the commit locally. Installed by
  `make setup-hooks` with the pre-commit hook; it is the only check that may
  live outside `bin/hooks/pre-commit`, because it is a different git hook.
- **CI** (`commit-messages` job in `filelist-checks.yml`) checks every commit a
  push or PR adds, so `--no-verify` and hook-less clones do not get a trailer
  onto main. It checks only the new commits, never history.

What counts: a line that STARTS with `Co-authored-by:`, `Assisted-by:`,
`Generated-by:` or `Claude-Session:`, or a "Generated with" footer naming a link
or a model/harness. Prose that mentions a trailer passes. A co-author that is a
GitHub bot (`dependabot[bot]`) is exempt: GitHub's merge writes that line, not
an author. `bin/tests/test_check_commit_messages.py` pins every shape, including
three real body lines ("Generated with --docs-only ...") that a looser pattern
flagged.

**The 445 historical commits stay as they are.** Rewriting them would re-hash
~3,700 commits on a pushed `main` that peers commit to continuously, and break
every short hash the vault, tracker, RTL comments and session memory cite (about
630 distinct ones in the vault alone) -- a far worse defect than a footer.
Decided 2026-11-07.

## The harness will offer one

Every harness here supplies an attribution trailer by default: Claude Code
appends `Claude-Session:` (most of the 445), Kimi Code appends
`Co-authored-by: Kimi Code`. That default is overridden here and the override
is not negotiable per-session. If a harness instruction and this note disagree,
this note wins -- and the hook now says so at commit time instead of relying on
the session to remember.

Related: [[doc-placement]] (rule 4 -- method belongs in the handbook, not in a
CLAUDE.md, which is how six copies of a git convention came to exist).
