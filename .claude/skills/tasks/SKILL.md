---
name: tasks
description: Where project tasks/TODOs live and how to track them - the /Tasks/<area>/ directory with open/active/closed/dropped lifecycle pages. Use whenever you would record a TODO, start/finish a task, or are tempted to create a TASKS.md or TODO.md next to code.
---

# tasks

READ FIRST: /Tasks/INDEX.md (the master index IS the authority for this convention).

All task tracking lives in `/Tasks/<area>/`. Each area has `INDEX.md` plus four
lifecycle pages: `open.md` (not started), `active.md` (in progress),
`closed.md` (done), `dropped.md` (ended without completing).

The rule agents break: **never create a `TASKS.md` / `TODO.md` / `*_TODO.md`
next to code.** That scatter is what /Tasks/ replaces. A note-to-self goes in
`/Tasks/<area>/open.md`, not in a new file beside the module.

Move a task by CUTTING its block between pages (never copy - one state only),
and keep its `**Status:**` line dated. `closed` = done; `dropped` = decided not
to do it - keep them apart so history stays honest.

Migration is in progress: `amba` is migrated; other areas' rows in
/Tasks/INDEX.md are marked `pending` and still point at their old file until
moved. If you touch a pending area's tasks, prefer migrating it into
/Tasks/<area>/ over editing the old file in place.

Enforcement authority remains /GLOBAL_REQUIREMENTS.md. Design/DV/FPGA practice
lives in the handbook (docs/handbook/INDEX.md), not here - this tracks WORK.
