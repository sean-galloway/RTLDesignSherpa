---
title: granite-ddr2-lpddr2 tasks
summary: Task rollup for the granite-ddr2-lpddr2 product (projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2).
---

# granite-ddr2-lpddr2 — task rollup

**Next ID: TASK-010** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`, `deferred/`). Moving an
item between states is `git mv`, so an item is in exactly one state by
construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-010` |

## Open shortlist

Nothing open or active. TASK-003 (100 MHz, ahead of LiteDRAM) and TASK-007
(narrow beats, fixed by `mc_axi4_narrow_pack`) closed 2026-11-02; TASK-001,
TASK-002, TASK-006 and TASK-008 are closed. Two deferred: TASK-004 (timing
margin levers), TASK-009 (1:4 board first DQ word). TASK-005 (half-width
aggregator) dropped 2026-11-03: the store combiner does its job. See [task/INDEX.md](task/INDEX.md).
