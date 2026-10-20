<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/tile — tasks

**Next ID: TASK-007** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 6 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — study IBM NorthPole for tile architecture ideas (networks, memory near compute, program distribution, flow control); owner rules on each idea
- **TASK-002** — milestone M1: fully working tetrad on the FPGA (TILE_SPEC 12 ladder, owner direction 2026-10-19)
- **TASK-003** — milestone M2: tile running in isolation (injectors) on the FPGA
- **TASK-004** — milestone M3: rapids + tile working artificially (injectors/test data)
- **TASK-005** — milestone M4: rapids + tile on real data and benchmarks
- **TASK-006** — cell-to-cell credits/grants extension (TILE_SPEC 10 open item; after M3)

## Active

## Closed
