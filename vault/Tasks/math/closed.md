<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Closed

_None._


---

## MATH-002 — bf16_adder underflow can report as +infinity/overflow (wrap bit shared by both flags)
**Status:** closed 2026-07-31 -- fix-RTL per Sean ("fix the math if they aren't to spec");
wrap-bit flag separation applied, directed FTZ regression added to
BF16AdderTB (underflow_ftz_test), mutation-checked (reverting the fix turns
3 cases RED).
**Priority:** P1 — possible RTL defect; doc promises FTZ-to-zero
**Owner:** Sean

`docs/markdown/rtl-math/math_bf16_adder.md` promises flush-to-zero:
"Output subnormals - Not generated (result goes to zero)", "FTZ mode",
"ow_underflow: 1 if result underflowed to zero". But in
`rtl/math/math_bf16_adder.sv`:

    wire w_exp_overflow  = w_exp_adjusted[8] || (w_exp_adjusted[7:0] >= 8'hFF);
    wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);

`w_exp_adjusted = {1'b0, r3_exp_l} - {5'b0, w_norm_shift_amt}` -- when the
normalization left shift exceeds exp_l the subtraction wraps negative and
bit 8 sets, asserting BOTH flags. The result-select chain tests the
overflow branch FIRST, so an underflowing result comes out as +infinity
with ow_overflow instead of zero with ow_underflow.

**Sim-settled 2026-07-31: the bug is REAL.** Directed case
(all PIPE_STAGEs=1): `0x0081 - 0x0080` (result ~2^-133, deep subnormal,
should FTZ to zero with ow_underflow) produces **0x7f80 (+inf), ow_overflow
= 1, ow_underflow = 0**; same for `0x0083 - 0x0080`. Sanity 1.0+1.0=2.0
passes. The wrap mechanism is confirmed: bit 8 of w_exp_adjusted is exactly
the negative sign of the exponent subtraction, so

    w_exp_overflow  = !w_exp_adjusted[8] && (w_exp_adjusted[7:0] >= 8'hFF);
    w_exp_underflow =  w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);

separates the flags (bit 8 cannot mean positive overflow here: shift is
bounded by the mantissa width, so a positive exp_l-shift never wraps).

**Remaining decision (Sean):** fix the RTL per the sketch above
(mutation-check with the same directed case), or declare inf-on-underflow
intended and rewrite the doc's FTZ promises. The doc currently reads as the
spec, and +inf on underflow is indefensible arithmetic -- the expected call
is fix-RTL, but it is your module.



---

## MATH-003 — filelist coverage: 134 math modules have no .f; 106 of 119 math tests hand-list sources
**Status:** closed 2026-08-06 -- 134 missing .f generated
(bin/gen_math_filelists.py), 24 hand-maintained lists had incomplete
closures (regenerated), all 119 tests converted
(bin/convert_math_tests_to_filelists.py). gate 119/119, func 134/134 on
clean builds.
**Priority:** P2 — mechanical but large; drives every future test review of the area
**Owner:** TBD

The [[filelists]] rule (every module has a `.f`, tests take the closure, never
hand-list) is broadly unimplemented in rtl/math:

- **134 of 171 modules have no filelist** (38 exist in rtl/math/filelists/).
  Generation is scriptable: each module's `.f` is its instantiation closure
  (the deps_of logic in bin/build_review_bundle.py already computes it), then
  `python3 bin/filelist_registry.py --check` must pass.
- **106 of 119 val/math tests hand-list `verilog_sources = [...]`** (13 use
  get_sources_from_filelist). Convert once the filelists exist, in batches
  with a regression run per batch. The cdc audit found the same class in
  miniature (3 tests) and it was fixed in-line there.
- Related smaller item from the same findings: wrappers that DO use the
  filelist helper then pass `includes=[]` (the cdc batch-5 pattern) — fold
  those into the conversion batches.




---

## MATH-004 — levels are decorative: TEST_LEVEL exported but never gates depth; FULL == FUNC grids
**Status:** closed 2026-08-06 -- systemic core fixed: TBBase.normalize_test_level
(22 read sites swept across the six shared TB families) maps gate/func/full
onto the basic/medium/full suites, so func no longer falls through to the
minimal suite; full_nbit's FULL grid un-duplicated; HanCarlsonAdderTB's
dead 'gate' branch and silent-deepest-else fixed. Per-TB depth tuning
continues in future audits, but the mechanism is now live everywhere.
**Priority:** P1 — HARD REQUIREMENT (Sean 2026-08-03): every test must have working gate/func/full
**Owner:** TBD

Math tests have REG_LEVEL grids on paper (119/119) but the audit finds the
second mechanism hollow: TEST_LEVEL is exported by the wrapper and never read
by the TB path (or gates nothing), and several grids are FULL == FUNC
re-labelled (clause 7, "levels are honest"). cdc's batch-3 fixed this shape
there (matrices restored, vocabulary unified); math needs the same pass per
TB family (fp_testing, bf16_testing, adder_testing, multiplier_testing are
shared by 100+ tests, so fixing the shared TBs covers most of the class).
Define what gate/func/full actually DO per family (fewer patterns at gate,
the full directed set at full) and wire it.



---

## MATH-001 — Decide: bf16 multiplier rounding is not RNE — intended or RTL defect?
**Status:** closed 2026-08-10 -- final suite verification green on clean
builds (bf16_multiplier, fp32_multiplier, bf16_mantissa_mult, 3/3)

Where it is at (Sean's request for a status marker):
- bf16: mantissa_mult exports the guard bit and TRUE sticky (unfolded --
  the fold made ties-at-even round up); multiplier computes
  G & (R | S | LSB). Sweep-verified: 0 mismatches in 5000 random pairs vs
  an exact behavioral RNE reference (tb_rne2.sv harness pattern in /tmp).
- fp32: same fix applied to the ieee754_2008_fp32 pair (family sweep).
- Docs updated on both bf16 pages (rounding note now describes the fix,
  with history).
- REMAINING: final suite verification (bf16/fp32 multiplier + mantissa_mult
  suites on clean builds), then close. fp16/fp8 variants split to MATH-007. 2026-07-29 (surfaced by math qc round_1; previously noted in dropped DOCREV-001)
**Priority:** P1 — an RTL behavior question only the owner can settle
**Owner:** Sean

`math_bf16_mantissa_mult` folds guard into sticky (`ow_sticky_bit = guard | sticky`),
so `math_bf16_multiplier` rounds on `R & (G | S | LSB)` where textbook RNE is
`G & (R | S | LSB)`. Verified truth table (LSB, guard, round, sticky): the two
agree in 10/16 patterns and disagree in 6 — five NON-tie cases (`G=0,R=1,S=1`
and `G=0,R=1,S=0,L=1` round up where RNE rounds down; `G=1,R=0,S=1` rounds down
where RNE rounds up) plus one tie (`G=1,R=0,S=0,L=1`, no round-to-even). 37.5%
of inexact guard patterns round the wrong way.

Decision needed: is the implemented boolean intentional (cheap rounding,
documented as such) or a defect? If defect: change to
`w_round_up = w_guard_bit & (w_round_bit | w_sticky_bit | w_lsb)` — but note
`mantissa_mult` currently outputs only folded (sticky|lsb) terms, so true RNE
needs the guard bit exported separately, which changes the module interface.
The docs now describe the actual behavior accurately (math qc round_1
integration, 2026-07-29); only the RTL question remains.

If intended: close with a one-line rationale and mark the doc note 'documented
behavior, not a bug'. If defect: fix RTL + the consuming modules, add a
rounding-truth-table test to val/math.
