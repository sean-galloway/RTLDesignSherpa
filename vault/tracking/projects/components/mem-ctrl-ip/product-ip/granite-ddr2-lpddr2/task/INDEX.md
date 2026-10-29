<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one
state by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 3 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 2 | parked pending a named condition |

## Active

- **TASK-001** — granite first build: steps 1-2 done (wrappers dissolved
  into common macros; `granite_core` built — no storage layer,
  `mc_xddr2_entry_store` seam, reduced refresh options). Remaining: product
  CSR baseline, board + frequency plan. [active/TASK-001.md](active/TASK-001.md).
- **TASK-002** — bank queues as gaxi_age_fifo_sync (PEEK 2) carrying the pool age;
  a head's rd_age_thresh is the record's age_exceed. Owner's choice 2026-10-25. [active/TASK-002.md](active/TASK-002.md).
- **TASK-003** — granite at 100 MHz and ahead of LiteDRAM through the same
  harness: 100 MHz closes (b8665155e, timer loads registered); DDR2-400 board
  point measured 2026-10-29 (streams 772/774 of 800, 1w+1r 761-773 combined,
  3x LiteDRAM at 75); thrash cells remain the gap. [active/TASK-003.md](active/TASK-003.md).

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
