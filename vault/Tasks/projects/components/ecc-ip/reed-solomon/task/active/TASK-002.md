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

## As-validated solver integration (2026-10-02, model proven)

The "seeded with Gamma" guess above did NOT survive contact with the fixed
2t-cycle arrays. What validated 100% against reedsolo (six profiles, both
solvers, plus an exhaustive (f, e) boundary sweep) is a front transform +
control change + post-multiply:

- `erasure_locator`: Gamma(x) = prod_j (1 - X_j * x), X_j = alpha^(n-1-j)
  (roots at X_j^-1, Chien's convention). Hardware: one parallel-combine
  cycle per flagged beat.
- Forney syndromes: T = Gamma*S mod x^2t with the LOW f coefficients
  dropped (they are the evaluator tail; consuming them as discrepancies is
  the unsound step, and reedsolo skips exactly the same coefficients).
- riBM: runs the fixed 2t cycles on T zero-padded, with updates KILLED
  (d0 forced 0) for cycles >= 2t-f. Zero-padding without the kill is
  unsound -- the pad is consumed with nonzero discrepancies once the
  locator develops (measured: spurious degrees).
- Euclid: takes the zeroed-LOW window (x^f * T, sound there because it
  consumes the polynomial whole, unlike a forward-iterating BM) and raises
  its stop threshold to t + ceil(f/2); f = 0 reduces to errors-only.
- Degree check against the SHRUNK budget: deg(Lambda_e) <= (2t-f)/2.
  Without it a beyond-bound block (2e + f > 2t) walks degree, root-count
  AND re-check onto a WRONG valid codeword (measured at e=1, f=15).
- Post-multiply: combined locator Gamma * Lambda_e goes to Chien; Forney
  uses the combined evaluator Gamma*Lambda_e*S mod x^2t with exponent 1-b.
- Beyond the bound, reedsolo itself miscorrects (77 wrong / 0 right / 172
  raises in one corpus), so the model is deliberately the stricter decoder
  there: uncorrectable, both solvers agreeing.

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

## RTL phase complete (2026-10-02)

Model (fe5241a6a) -> solvers (623206957) -> erasure unit (ae8df6e0b) ->
core plumbing (f3265108e). What landed:

- `rs_erasure_unit` (new): A-side records flagged X values into a 2t+1-entry
  file in arrival order (f saturates at 2t+1 with f_over); the packed record
  rides the A->B descriptor's low bits. B-side runs TRANS (f cycles, Gamma
  and GS = Gamma*S mod x^2t combined one gf_mul deep), the solver window
  (riBM: T = GS >> f as a crossbar; Euclid: zeroed-low window), and COMB
  (Horner over Lambda_e: Lambda_c = Gamma*Lambda_e, Omega_c = Lambda_e*GS
  mod x^2t). t_zero bypass: erasures alone explain the syndromes, so the
  solver is skipped and the registers already hold the answers.
- Both solvers take `ERASURE_SUPPORT` + `i_erasure_count`: riBM kills
  updates for cycles >= 2t-f, Euclid raises the stop threshold to
  t + ceil(f/2). Off state generates the logic away.
- `rs_decoder_core` stage B splits into two generate branches: the
  errors-only FSM verbatim (off state bit-identical), and a five-state
  TRANS -> SOLVE -> COMB FSM with the f_over uncorrectable-by-inspection
  exit, the t_zero bypass, and the (2t-f)/2 budget check in the bad
  verdict. The erasure stage pays one bubble per block boundary (TRANS
  must run before the next solve). Chien/Forney run at T_SYMBOLS = 2t on
  the combined polynomials, OMEGA_HIGH_HALF = 0 (the combined evaluator is
  the textbook form either way). Chien and Forney themselves needed NO
  changes -- fully generic in T_SYMBOLS.
- Wrappers (axis4, axi4) tie `in_erasure` off for now; the sideband is
  exposed when the DV phase adds the axis.

Verified: `make -C rtl lint-all` clean (19 tops); ERASURE_SUPPORT=1
elaborates with zero diagnostics for BOTH solvers; the off state passes
the gate 82/82 unchanged. The on state is functionally UNPROVEN until the
DV cells land -- that is the next phase, not an assumption to bake in.

Still to do: DV cells (ERASURE_SUPPORT matrix axis, the dedicated
OFF-state test, boundary cells 2e+f = 2t and the first failing case past
it, mutation checks on the Gamma build, erasure-unit model-matched
cells), then the harness injector erasure mode + docs (HAS, FUB catalog),
then the wrapper sideband.

## Notes

Every existing block was built errors-only; the model-first order (Python,
then RTL, then DV cells, then harness) is the pattern that worked for the
decoder bring-up and is repeated deliberately. Depends on nothing; pulls
forward only when a consumer names it (see TASK-003).
