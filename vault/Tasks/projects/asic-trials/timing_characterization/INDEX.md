---
title: timing_characterization tasks
summary: Task rollup for the pre-synthesis timing characterization campaign (projects/asic-trials/timing_characterization).
---

# projects/asic-trials/timing_characterization — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

The **core is complete**: 9 FUBs, `char_top.sv`, 45/45 tests, multi-flow SDC,
HAS/MAS books and white papers. What remains is enhancement work only.

Formerly filed under NexysA7; the area moved to `projects/asic-trials/` and its
TASKS.md did not follow, which is why TOOL-001 lost track of it. That checklist
recorded "9 task blocks"; there were four.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-005` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-001` |

Open counts include the reserved `-000` template, which is never a real item.

## Provenance

Migrated 2026-09-25 from `projects/asic-trials/timing_characterization/TASKS.md` under tooling TOOL-001, and
every item was classified against the TREE rather than its own `**Status:**`
line. Each item records its source and original ID.
