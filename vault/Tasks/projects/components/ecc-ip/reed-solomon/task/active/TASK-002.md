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

## DV phase complete (2026-10-02)

- `test_rs_decoder_core` gains an `ERASURE_SUPPORT` axis: every profile runs
  at 0 and 1. The off state runs the identical erasure stimulus as the
  dedicated flags-are-dead test (the axis IS the off-state test), and keeps
  the strict bit-identical perf contract; the on state uses the erasure
  rate below.
- `rs_erasure_unit` gets a standalone TB (`rs_erasure_unit_tb` +
  `test_rs_erasure_unit`, 12 cells over gate/func, both solvers, S > 1,
  GF(2^4)): the TB plays the core, loops the packed record back, and checks
  every output against `rs_model`'s erasure intermediates -- the record
  (f, f_over, flags forced into the LAST beat to lock the next-value pack),
  t_zero, the solver windows, and the COMB outputs over a model-solver
  Lambda_e.
- THE bug the cells found: the core pops the A->B descriptor on the SAME
  edge `i_trans_start` fires, and the skid buffer's rd_data does not hold
  after the pop -- so through all of TRANS the unit read f = 0 and an
  all-zero X file, built Gamma = 1 / GS = S, and decoded errors-only.
  e + f <= t cells pass IDENTICALLY errors-only (same data, same count),
  so the erasure path had never actually worked; the passing cells passed
  around it. Fixed by latching the record at the start edge (r_fb /
  r_xfile_b); every B-side consumer reads the latch. Root-caused with a
  dynamic probe of the unit outputs against model intermediates after the
  static reads all came back clean.
- Second bug, same family: the record pack sampled the pre-edge registers
  on the block-end edge, dropping the LAST beat's flags. o_ab is now the
  next-value record (this beat's lanes merged over the file), the same
  reason the syndrome path ships w_synd_next.
- Third: `w_b_bad` dropped the `w_er_f_over` term -- unreachable (an f_over
  block exits in BE_IDLE) and able to misfire post-pop on the NEXT block's
  record.
- Rate contract (measured, codified in the TB perf checks and the core
  module header): the erasure stage B runs TRANS (f) + solve (2t) + COMB
  (deg_e + 1) serially, occupying f + 2t + deg_e + 5 cycles per block, so
  the on-state per-block rate is `max(n/S, 3t + 5)` -- below n/S the intake
  is solve-stage-bound, not bus-bound. The formula matched the measured
  slopes EXACTLY on all four matrix profiles; the named consumers
  (RAID stripes, an MC's known-bad column) run n = 255-class blocks where
  stage B never binds.

Verified: gate 94/94 and func 188/188, both after `make clean-all`
(90 core-area cells at gate plus the 4 new unit profiles; the 4 pre-fix
failures were the small-profile throughput cells the rate contract now
encodes).

## Wrapper sideband phase (2026-10-02)

The `ERASURE_SUPPORT` param and the erasure sideband are now exposed on both
codec tops; the off state builds the pre-erasure wrapper.

- `rs_decoder_axis4`: per-beat `in_erasure[S-1:0]` sideband, spliced ABOVE
  the consumer's tuser through the intake skid (`EUW = UW + S` when on) so
  the flags stay beat-aligned under backpressure -- a downstream consumer
  cannot see the skid's internals, so the flags ride the same register the
  data does. At 0 the generate branch wires `s_axis_tuser` straight through.
- `rs_decoder_axi4`: job-level `cfg_erasure[N-1:0]` bitmap, sampled at
  cfg_start into `r_er_map` and sliced per beat by the same beat index that
  builds `keep`. That is the shape the named consumer has: an MC known-bad
  column is a fixed position set for the whole job, identical in every
  block.
- Bug found by inspection before DV fired it: both wrappers hardcoded
  `STATUS_CNT_WIDTH = clog2(T+1)` while the core widens to `clog2(2T+1)`
  under ERASURE_SUPPORT (a corrected count reaches 2t). Both now take the
  same conditional.
- Consumers tied off explicitly until the injector's erasure mode exists:
  `rs_axi4_pipeline` (`.cfg_erasure('0)`) and `rs_loop_harness`
  (`.in_erasure('0)`). The axi4 loop DV toplevel forwards both the param
  and the port.
- DV: both wrappers run the SAME 7 erasure cells on BOTH axes, gate 3 /
  func 5 / full 7, chosen so the axes disagree (mostly between the
  errors-only bound e+f <= t and the erasure bound 2e+f <= 2t). axis4
  drives the per-beat flags from a coroutine that stays aligned under
  backpressure; axi4-loop corrupts M2 through the sdpram backdoor
  (`u_mem2.u_core.r_mem`) between encode and decode, one re-encode per cell
  restoring the clean codewords, and checks both the counters and the
  drained data (uncorrectable blocks pass received symbols through).
  `test_rs_axis4` and `test_rs_axi4_loop` each gained the erasure axis
  (`_e{0,1}` in the cell name), doubling both matrices.
- The axis4 on-state rate check uses the erasure contract
  `max(cw_beats, 3t+5)`; the off state keeps the strict pre-erasure one.
- TB bug the e0 axis caught: the M2 backdoor poked one symbol at a time,
  read-modify-write -- and the read-back does not see the previous line's
  deposit, so on any word two corrupted symbols share, every poke but the
  last was lost. The e1 axis hid it (a clean symbol at a flagged position
  still decodes, and the corrected count tallies the position); the
  errors-only e0 axis showed it as a corrected count one short per block
  and a clean symbol in the drained data. The poke now aggregates all
  deltas into ONE read + ONE write per word.

Verified: `make -C rtl lint-all` clean; one axis4 e1 gate cell
(RS(255,239), 27 checks / 0) and one axi4-loop e1 gate cell (RS(15,9)
EUCLID, 8 checks / 0) green before the regression.

Still to do: the harness injector erasure mode (rewire the
`.in_erasure('0)` tie-off) + docs (HAS chapters, FUB catalog).

## Notes

Every existing block was built errors-only; the model-first order (Python,
then RTL, then DV cells, then harness) is the pattern that worked for the
decoder bring-up and is repeated deliberately. Depends on nothing; pulls
forward only when a consumer names it (see TASK-003).
