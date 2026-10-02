# TASK-002: Erasure decoding (PRD D5)

**Priority:** P3
**Status:** active 2026-10-02 -- implementation started (model-first)
**Owner:** TBD

Filed at the close of reed-solomon TASK-001. PRD D5 is the last undecided
architectural decision with RTL substance: the decoder corrects e errors plus
f erasures whenever 2e + f <= 2t, but today it has no way to be TOLD which
symbols are erased. The consumers that want it are RAID-style (known-bad
columns) and -- per Sean's D10 direction (2026-10-02) -- the future memory
controller project, where a failing device or rank is exactly a known-bad
column.

## Implementation shape (Sean, 2026-10-02)

**Elaboration-time parameter `ERASURE_SUPPORT`, default 0**, same style as
`KES_ALGO` and `SYMBOLS_PER_BEAT` and the same philosophy as D2 (t is
elaboration-time; no runtime CSR, no mode bit).

- `ERASURE_SUPPORT=0`: no erasure-flag sideband on the intake, no Gamma(x)
  build, no KES-seed mux, no Forney extension -- generate blocks elaborate
  all of it away. The off state must be BIT-IDENTICAL to the pre-erasure
  decoder, proven by netlist diff or formal equivalence, not assumed.
- `ERASURE_SUPPORT=1`: S erasure flags ride with each beat at
  `SYMBOLS_PER_BEAT = S`; the erasure locator builds incrementally as
  flagged beats arrive; the selected solver's state is seeded with Gamma;
  Forney evaluates at erasure positions too. The wrappers only expose the
  sideband when the parameter is on, so a RAID/MC integration opts in and
  every other consumer's interface is unchanged.
- DV: the OFF state gets its OWN test (drive erasure stimulus at
  `ERASURE_SUPPORT=0`, prove errors-only behaviour is untouched), and the
  matrix gains an `ERASURE_SUPPORT` axis rather than flipping existing
  cells.

## Scope

- **Interface:** an erasure locator alongside the codeword -- a per-symbol
  erasure flag (or a packed erasure bitmap) on the decoder intake, S flags per
  beat at `SYMBOLS_PER_BEAT = S`, valid with the beat. Source is the
  integration (a RAID stripe map, an MC's known-bad-column CSR).
- **Algorithm:** Forney's erasure method -- build the erasure locator
  polynomial Gamma(x) from the flagged positions, modify the syndromes (or run
  the key equation seeded with Gamma), and extend the Forney evaluation.
  `rs_model.py` gains the erasure path FIRST and is validated against
  reedsolo's erasure decode, the way the error-only path was (900/900).
- **RTL:** `rs_decoder_core` and the blocks it touches (syndrome unit or KES
  seeding, Chien -- erasure magnitudes are evaluated at known positions so the
  search still runs, Forney). Both solvers (riBM and Euclid) must produce
  identical verdicts under erasures, as they do for errors.
- **DV:** new cells across the matrix -- f = 1..2t erasures only, e + f mixes
  at the 2e + f = 2t boundary, and the first failing case past it. Mutation
  checks on the erasure locator build.
- **Harness:** the error injector gains an erasure-flag mode so the Nexys A7
  loop can exercise it on the board; docs (HAS chapters, FUB catalog) in the
  same pass.

## Out of scope

Encoder changes (none needed -- erasures are a decode-side property), and any
run-time reconfiguration of t (still elaboration-time per D2).

## Notes

Every existing block was built errors-only; the model-first order (Python,
then RTL, then DV cells, then harness) is the pattern that worked for the
decoder bring-up and is repeated deliberately. Depends on nothing; pulls
forward only when a consumer names it (see TASK-003).
