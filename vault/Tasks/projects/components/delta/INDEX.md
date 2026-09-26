---
title: delta tasks
summary: Task rollup for Delta, the AXI-Stream crossbar generator (projects/components/delta).
---

# projects/components/delta — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

Delta is an **AXI-Stream crossbar generator** (`PRD.md`): Python-generated RTL,
dual topology -- flat crossbar and tree. RTL under
`projects/components/delta/rtl/`, generators in `bin/`
(`delta_generator.py`, `complete_tree_generator.py`), spec under
`docs/delta_spec/`.

**Scope tension worth knowing before you pick up an item.** The spec still
describes a NoC -- routers, network interfaces, virtual channels, a 4x4 mesh --
while the PRD commits only to flat and tree topologies. The mesh items are kept
OPEN rather than dropped; whether mesh is in scope is the owner's call.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-017` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-001` |

Open counts include the reserved `-000` template, which is never a real item.

## Provenance

Migrated 2026-09-25 from `projects/components/delta/TASKS.md` under tooling TOOL-001, and
every item was classified against the TREE rather than its own `**Status:**`
line. Each item records its source and original ID.
