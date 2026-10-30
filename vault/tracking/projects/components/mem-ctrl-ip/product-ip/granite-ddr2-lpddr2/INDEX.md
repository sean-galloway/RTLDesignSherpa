---
title: granite-ddr2-lpddr2 tasks
summary: Task rollup for the granite-ddr2-lpddr2 product (projects/components/mem-ctrl-ip/product-ip/granite-ddr2-lpddr2).
---

# granite-ddr2-lpddr2 — task rollup

**Next ID: TASK-008** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`, `deferred/`). Moving an
item between states is `git mv`, so an item is in exactly one state by
construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `TASK-008` |

## Open shortlist

One active item, one open (TASK-007, narrow beats on the 1:4 host), two deferred (2026-10-29). TASK-001 (first build),
TASK-002 (age-FIFO store) and TASK-006 (store combining) are closed; the
board runs every profile clean at 75 MHz and at the DDR2-400 100 MHz point,
with and without the combiner.

- **TASK-003** (active) -- 100 MHz and ahead of LiteDRAM through the same
  harness: items 5 (where the aged class sits in the pick's select, then
  CSR weights) and 6 (DFI 1:4 at 100 MHz, BL8) are what is left.
  [task/active/TASK-003.md](task/active/TASK-003.md).
- **TASK-006** (closed 2026-10-29) -- store combining behind
  `STORE_MERGE_EN`: close_page pair walk doubled, open_page pair +14..25
  percent at 3-4 threads, the board corruption root-caused and fixed
  (a WRITE at the DFI head before its data). [task/closed/TASK-006.md](task/closed/TASK-006.md).
- **TASK-004** (deferred) -- the 100 MHz timing margin levers.
  [task/deferred/TASK-004.md](task/deferred/TASK-004.md).
- **TASK-005** (deferred) -- the half-width AXI aggregator, kept behind
  `HALF_AGG=0`. [task/deferred/TASK-005.md](task/deferred/TASK-005.md).
