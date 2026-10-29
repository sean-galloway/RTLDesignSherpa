<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# granite-ddr2-lpddr2 — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

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
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Active

- **TASK-001** — granite first build: steps 1-2 done (wrappers dissolved
  into common macros; `granite_core` built — no storage layer,
  `mc_xddr2_entry_store` seam, reduced refresh options). Remaining: product
  CSR baseline, board + frequency plan. [active/TASK-001.md](active/TASK-001.md).
- **TASK-002** — bank queues as gaxi_age_fifo_sync (PEEK 2) carrying the pool age;
  a head's rd_age_thresh is the record's age_exceed. Owner's choice 2026-10-25. [active/TASK-002.md](active/TASK-002.md).
- **TASK-003** — granite at 100 MHz and ahead of LiteDRAM through the same
  harness: 100 MHz build -0.686 ns (132 core endpoints, two cones), board
  1w+1r collapse (54 MB/s vs pumice 552) traced to the select order; row gate
  in the pick. [active/TASK-003.md](active/TASK-003.md).

## Deferred

- **TASK-004** — granite 100 MHz timing margin: the remaining levers (LA=3 pick
  split, plane pblock, registered read-issue strobe; directives, replication and
  the pick trim measured and not levers) -- DEFERRED 2026-10-29, pending a build
  that no longer closes at 100 MHz with the shipped directives, or a product
  point above 100 MHz. [deferred/TASK-004.md](deferred/TASK-004.md).
