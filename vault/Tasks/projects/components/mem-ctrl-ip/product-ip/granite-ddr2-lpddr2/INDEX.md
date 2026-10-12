---
title: granite-ddr2-lpddr2 tasks
summary: Task rollup for the granite-ddr2-lpddr2 product (projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2).
---

# granite-ddr2-lpddr2 — task rollup

**Next ID: TASK-002** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`, `deferred/`). Moving an
item between states is `git mv`, so an item is in exactly one state by
construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-002` |

## Open shortlist

None — TASK-001 (granite first build) is **active**: wrappers dissolved into
the common macros and `granite_core` built (no storage layer,
`mc_xddr2_entry_store` seam, reduced refresh options). Remaining: product
CSR baseline + board. Details: [task/active/TASK-001.md](task/active/TASK-001.md).
