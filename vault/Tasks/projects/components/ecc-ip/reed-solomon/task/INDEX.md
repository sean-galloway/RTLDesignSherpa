<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/reed-solomon — tasks

**Next ID: TASK-005** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Active

## Open

- **TASK-004** — Author the RS math chapter for novices: from zero (what a
  field is, why GF(2^m), polynomial arithmetic mod p(x)) to the full decoder
  chain, with hand-checkable GF(2^4) worked numbers; novice voice, every
  symbol defined before use; BCH's matching chapter links here for the
  shared foundation.

## Closed

- **TASK-001** — Stand up the Reed-Solomon component -- CLOSED 2026-10-02: codec, both solvers, AXIS + AXI4 wrappers, 195-cell DV area, HAS, and the four-image Nexys A7 loop harness all exist and board-pass; sim harness reproduces the board's bandwidth slopes to the cycle. Successors: TASK-002 (erasures), TASK-003 (first consumer).
- **TASK-002** — Erasure decoding (PRD D5) -- CLOSED 2026-10-03: elaboration-time `ERASURE_SUPPORT` (default 0, off state bit-identical with its own OFF test), erasure locator + Forney erasure path proven model-first against reedsolo, both solvers, per-beat sideband on the AXIS wrapper and job-level `cfg_erasure` on the AXI4 wrapper, injector `INJ_CFG.mark` mode on the harness, full DV matrix. Surfaced and fixed amba BUG-038 (axis4 tuser mis-slice) and the harness SC_W truncation. Consumer pull-in rides with TASK-003.

## Deferred

- **TASK-003** — First consumer selection (PRD D10) -- DEFERRED 2026-10-02, pending a memory controller project consumer (Sean: consumers are expected from a future memory controller project). Wakes to pin the profile, D8 conventions, the TASK-002 pull-in, and PRD v1.0.
