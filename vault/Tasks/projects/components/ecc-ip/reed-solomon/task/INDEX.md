<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/ecc-ip/reed-solomon — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Active

## Open

## Closed

- **TASK-004** — Author the RS math chapter for novices -- CLOSED 2026-10-08:
  landed as HAS ch07 `understanding_the_math` with all five sections
  (fields/polynomials, the code, decoding, the n/k/t/m parameters, and
  every-stage math-to-pseudocode), worked GF(2^4) numbers verified by
  `ch07_math_trace.py` (ALL CHECKS PASSED: RS(255,239) and RS(252,236)
  profiles, correction round-trip, post-correction syndromes zero); BCH's
  sister chapter cross-links here for the shared finite-field foundation.
- **TASK-001** — Stand up the Reed-Solomon component -- CLOSED 2026-10-02: codec, both solvers, AXIS + AXI4 wrappers, 195-cell DV area, HAS, and the four-image Nexys A7 loop harness all exist and board-pass; sim harness reproduces the board's bandwidth slopes to the cycle. Successors: TASK-002 (erasures), TASK-003 (first consumer).
- **TASK-002** — Erasure decoding (PRD D5) -- CLOSED 2026-10-03: elaboration-time `ERASURE_SUPPORT` (default 0, off state bit-identical with its own OFF test), erasure locator + Forney erasure path proven model-first against reedsolo, both solvers, per-beat sideband on the AXIS wrapper and job-level `cfg_erasure` on the AXI4 wrapper, injector `INJ_CFG.mark` mode on the harness, full DV matrix. Surfaced and fixed amba BUG-038 (axis4 tuser mis-slice) and the harness SC_W truncation. Consumer pull-in rides with TASK-003.
- **TASK-005** — RS decoder flags f = 2t erasure blocks uncorrectable -- CLOSED 2026-10-08: never the decoder. The 10-04 failure's symptom pattern (f=8 corrects, f=16 uncorrectable every block, f=17 refuses) is exactly errors-only decoding of an unmarked stream: the run sat in the uncommitted unified-injector migration window, with the host regmap writing INJ_CFG.mark at bit 2 against hardware already at bit 3. f433fcaec committed the consistent flip (mark 2→3 across RDL, regblock, regmap) — that is the fix; no board re-ran the erasure sequence afterward, so the task stayed open on stale evidence. Era-exact A/B on the Genesys 2: the stashed 2026-10-04 bitstream and a fresh current-main image both PASS `init erasure` (f=8/16/17, blocks=16); component DV at the board geometry RS(252,236) S=4 and the dual-solver harness sim also pass. Board geometry added to the decoder-core matrix so the sim keeps the case.

## Deferred

- **TASK-003** — First consumer selection (PRD D10) -- DEFERRED 2026-10-02, pending a memory controller project consumer (Sean: consumers are expected from a future memory controller project). Wakes to pin the profile, D8 conventions, the TASK-002 pull-in, and PRD v1.0.
