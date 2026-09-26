---
title: hive tasks
summary: Task rollup for HIVE, 1 VexRiscv supervisor + 16 SERV cores (projects/components/hive).
---

# projects/components/hive — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

HIVE is in **Early Specification Phase** (`PRD.md` v0.1). Measured 2026-09-25:
zero `.sv` files, zero tests, no SERV or VexRiscv source, and only
`docs/hive_spec/ch01_overview/` plus `ch02_blocks/00_overview.md` written. Every
item's stated Related Files path does not exist yet, which is why all of them
are open rather than in progress.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-026` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-001` |

Open counts include the reserved `-000` template, which is never a real item.

## Provenance

Migrated 2026-09-25 from `projects/components/hive/TASKS.md` under tooling TOOL-001, and
every item was classified against the TREE rather than its own `**Status:**`
line. Each item records its source and original ID.
