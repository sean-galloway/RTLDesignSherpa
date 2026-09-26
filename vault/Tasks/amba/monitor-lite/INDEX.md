---
title: amba/monitor-lite tasks
summary: Task rollup for rtl/amba/monitor/axi_monitor_lite.sv (axi_monitor_lite), the AXI monitor at a fifth of the gates.
---

# amba/monitor-lite — task rollup

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between states
is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-003` |
| [bug/](bug/INDEX.md) | a defect with a reproduction | `BUG-001` |
| [issue/](issue/INDEX.md) | an anomaly, risk or open question | `ISSUE-002` |

Open counts include the reserved `-000` template, which is never a real item.

## What lives here (Sean, 2026-09-25)

`rtl/amba/monitor/axi_monitor_lite.sv` is its own sub-area of amba, the way each RLB block
is a sub-area of RLB: the block's own features, defects and questions file
here; work on the monbus, the full monitor family or the wrappers files under
`amba/`. Its collateral is likewise its own: tests in `val/amba/monitor-lite/`
(own Makefile and conftest, an entry in `val/Makefile` AREAS and in the root
gate/func/full targets), TB classes in `bin/TBClasses/amba/monitor_lite/`,
formal in `formal/amba/axi_monitor_lite/`, pages in
`docs/markdown/rtl-amba/monitor/` booked with the monitor subsystem.

IDs are scoped to this sub-area and its lane; cite one from outside as
"amba/monitor-lite TASK-001". TASK-001 began life as the legacy amba lane's
TASK-098, filed and committed there before this sub-area existed; it was
re-filed here the same day and closed there with a pointer.
