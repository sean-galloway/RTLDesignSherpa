---
name: tasks
description: Where project tasks/TODOs live and how to track them - the /vault/Tasks/<area>/ directory with open/active/closed/dropped lifecycle pages. Use whenever you would record a TODO, start/finish a task, or are tempted to create a TASKS.md or TODO.md next to code.
---

# tasks

READ FIRST: /vault/Tasks/INDEX.md (the master index IS the authority for this convention).

All task tracking lives in `/vault/Tasks/<area>/`. Each area has `INDEX.md` plus four
lifecycle pages: `open.md` (not started), `active.md` (in progress),
`closed.md` (done), `dropped.md` (ended without completing).

The rule agents break: **never create a `TASKS.md` / `TODO.md` / `*_TODO.md`
next to code.** That scatter is what /vault/Tasks/ replaces. A note-to-self goes in
`/vault/Tasks/<area>/open.md`, not in a new file beside the module.

Move a task by CUTTING its block between pages (never copy - one state only),
and keep its `**Status:**` line dated. `closed` = done; `dropped` = decided not
to do it - keep them apart so history stays honest.

Migration is in progress (tracked as TOOL-001 in vault/Tasks/tooling/active.md):
`amba` is migrated; other areas' rows in /vault/Tasks/INDEX.md are marked `pending`
and still point at their old file until moved.

## Migrating an area (do every area identically)

1. **Fence-aware split** the source file into task blocks. Only treat a line
   starting with `##`/`###` as a header when NOT inside a ``` code fence — task
   bodies embed markdown/code examples whose lines start with `##`, and a naive
   split silently drops the tail of those tasks.
2. **Classify by REAL repo state, not the stale `**Status:**` marker.** Verify
   each task against the tree (does the file/feature exist, did the work land?).
   The amba pilot's "active" bucket was mostly already done. closed = done,
   dropped = decided-against.
3. Write `INDEX.md` + `open/active/closed/dropped.md` (see vault/Tasks/amba/ for the
   shape). Keep each task block intact; drop only scaffolding (legends, phase
   headers, stale summary tables).
4. **Repoint every inbound reference** to /vault/Tasks/<area>/ and delete the
   original file (owner's chosen policy).
5. **Verify**: task-block count and content match the original; all links
   resolve. The counts looking clean is not proof — the first amba pass looked
   clean and had dropped a task's tail.

Enforcement authority remains /GLOBAL_REQUIREMENTS.md. Design/DV/FPGA practice
lives in the handbook (vault/handbook/INDEX.md), not here - this tracks WORK.
