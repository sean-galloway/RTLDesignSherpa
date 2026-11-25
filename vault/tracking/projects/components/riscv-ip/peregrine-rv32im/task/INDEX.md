<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/riscv-ip/peregrine-rv32im — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-003** — the peregrine book (*speculation and traps*) and predictor drill mode 3 (PRD §7 item 5); after TASK-002.
- **TASK-004** — hive-serv HIVE-C `CORE_FLAVOR=peregrine` swap, peregrine's system bring-up (PRD §7 item 6, hive-serv PRD §10.3).

## Active

- **TASK-002** — `peregrine_has` and `peregrine_mas` books, as built (PRD §7 item 2).

## Closed

- **TASK-001** — peregrine RV32IM core: RTL, DV and targeted formal per PRD 0.2. Closed 2026-11-25: all seven stages done; amber is the D$, 18.5 ns (54.1 MHz) on xc7a100t-1, riscv-formal 52/52 on both `MUL_DSP` builds, targeted core/top properties, a bounded M-unit reference proof.
