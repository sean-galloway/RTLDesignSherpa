---
title: memory-controllers tasks
summary: Cross-controller task lane for the mem-ctrl-ip family (pumice DDR2/LPDDR2, scoria DDR3/LPDDR3, andesite DDR4/LPDDR4; basalt reserved).
---

# memory-controllers — task rollup

**Each lane carries its own Next ID** (task `MC-006`, bug `BUG-003`, issue `ISSUE-002`) — never recycle a number, even when its item closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between
states is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `MC-006` |
| [bug/](bug/INDEX.md) | defects in the shared `common-ip` RTL, more than one controller | `BUG-003` |
| [issue/](issue/INDEX.md) | undiagnosed problems spanning controllers | `ISSUE-002` |

Open on 2026-11-07: ISSUE-001 (the microarchitecture is ASIC-shaped for the
FPGA target; ranked rework list in its report, 14 of 16 rows still open).
Closed 2026-11-07: BUG-001 (`mc_wr_intake` dropped Bs without `wr_done`
backpressure) and BUG-002 (`mc_dfi_cdc` token and data on separate
synchronizers), both fixed 2026-11-06. Lanes created 2026-11-06. Active: MC-004
(skid buffer `DATA_RST` parameter) and MC-005 (reset-free storage arrays), the
first two ISSUE-001 reworks: RTL done and regression-clean 2026-11-06, routed
A/B builds running 2026-11-07; MC-005 phase 3 (bridge generator) open.

Family-wide conventions live here (see
[ADVANCED_MODES_ROADMAP.md](ADVANCED_MODES_ROADMAP.md) for the feature
roadmap): macros are `*_layer` (MC-001), FUB training interfaces keep
`*_ifc`.

## LPDDR is deferred on every technology (owner, 2026-11-02)

No LPDDR board work, and no new LPDDR feature work, on any controller --
pumice / granite (LPDDR2), scoria / gabbro (LPDDR3), andesite / diorite
(LPDDR4) -- until summer 2027, when test boards built following Antmicro's
methods are in hand. That board on the bench is the named condition for
unparking. What exists stays: LPDDR paths keep passing their current tests,
and a defect found in them is still fixed (pumice BUG-024 was closed under
this rule). Deferred under it: pumice TASK-042 (LPDDR2 board enablement).
