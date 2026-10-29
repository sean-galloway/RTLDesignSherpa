<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — tasks

**Next ID: TASK-007** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one
state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 2 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 2 | parked pending a named condition |

## Open

(none)

## Active

- **TASK-006** — store combining behind `STORE_MERGE_EN` (default 0): built,
  tested, on the board the close_page pair walk doubles and matches pumice;
  OPEN DEFECT: counter-id open_page pair walk at 1-2 threads corrupts
  (write merge under an open row), reads-only merging clean. ACTIVE
  2026-10-29. [active/TASK-006.md](active/TASK-006.md).
- **TASK-003** — granite at 100 MHz and ahead of LiteDRAM through the same
  harness: 100 MHz closes (b8665155e, timer loads registered); DDR2-400 board
  point measured 2026-10-29 (streams 772/774 of 800, 1w+1r 761-773 combined,
  3x LiteDRAM at 75); thrash cells remain the gap. [active/TASK-003.md](active/TASK-003.md).

## Closed

- **TASK-001** — granite first build: wrappers dissolved, `granite_core`
  composed from common-ip, CSR baseline, Nexys A7 at 75 MHz. The split-burst
  wedge it carried was fixed under MC-003. CLOSED 2026-10-29.
  [closed/TASK-001.md](closed/TASK-001.md).
- **TASK-002** — bank queues as gaxi_age_fifo_sync (PEEK 2) carrying the pool
  age; landed 3a1479820, cycle-identical, controller worst path 0.34 -> 0.93
  ns. Residual (where the aged class sits in the select, `HAS_AGE` 0) folded
  into TASK-003 item 5. CLOSED 2026-10-29. [closed/TASK-002.md](closed/TASK-002.md).

## Deferred

- **TASK-004** — granite 100 MHz timing margin: the remaining levers (LA=3 pick
  split, plane pblock, registered read-issue strobe; directives, replication and
  the pick trim measured and not levers) -- DEFERRED 2026-10-29, pending a build
  that no longer closes at 100 MHz with the shipped directives, or a product
  point above 100 MHz. [deferred/TASK-004.md](deferred/TASK-004.md).
- **TASK-005** — the simple AXI aggregator in granite's AXI plane (`HALF_AGG`,
  block kept, off) -- DEFERRED 2026-10-29, measured: pairs only same-ID adjacent
  halves, the open_page pair cell is host-rate bound (no gain), unpaired halves
  pay the hold (-30 percent), a write hang on open_page. Wakes for a DRAM-bound
  same-ID master or a per-port placement. [deferred/TASK-005.md](deferred/TASK-005.md).
