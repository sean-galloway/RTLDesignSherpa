<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/reed-solomon — tasks

**Next ID: TASK-004** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Active

- **TASK-002** — Erasure decoding (PRD D5): erasure locator interface, Forney erasure path in `rs_model.py` then RTL, both solvers, DV matrix, injector erasure mode on the harness. Implementation shape pinned 2026-10-02 (Sean): elaboration-time `ERASURE_SUPPORT` param, default 0, off state bit-identical with its own OFF test. ACTIVE 2026-10-02.

## Open

## Closed

- **TASK-001** — Stand up the Reed-Solomon component -- CLOSED 2026-10-02: codec, both solvers, AXIS + AXI4 wrappers, 195-cell DV area, HAS, and the four-image Nexys A7 loop harness all exist and board-pass; sim harness reproduces the board's bandwidth slopes to the cycle. Successors: TASK-002 (erasures), TASK-003 (first consumer).

## Deferred

- **TASK-003** — First consumer selection (PRD D10) -- DEFERRED 2026-10-02, pending a memory controller project consumer (Sean: consumers are expected from a future memory controller project). Wakes to pin the profile, D8 conventions, the TASK-002 pull-in, and PRD v1.0.
