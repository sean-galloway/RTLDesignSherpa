<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/peregrine-rv32im — tasks

**Next ID: TASK-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **TASK-001** — peregrine RV32IM core: RTL, DV and targeted formal per PRD 0.2 (staged: traps cacheless, M unit, predictor, caches + fabric). Stage 1 (traps, cacheless) done 2026-11-23; stage 2 (M unit, hold-in-EX) done 2026-11-24; stage 3 (predictor) done 2026-11-24; stage 6 (amber hit latency, P13) measured 2026-11-24: 4 cycles; P13 option (b) chosen, amber pipelined hit path filed as cache-ip/amber-mesi-l1 TASK-005.

## Closed

(none)
