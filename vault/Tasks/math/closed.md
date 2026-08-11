<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Closed


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

---

## MATH-005 — math_mod_3_compress needs its final formal checks
**Status:** closed 2026-08-10 -- harness written per [[formal]]
(formal/common/math_mod_3_compress/): anyconst 16-bit input, rem_out asserted
against the solver's own `d_in % 3`, plus range assert and 7 covers (all three
residues, zero, all-ones/max digit sum, and both fold subtract branches --
digit sums 15 and 6). prove PASS, cover PASS 7/7 reached; mutation-checked
(fold constant 6->5 turns ap_rem_correct RED, restore GREEN).
**Priority:** P2
**Owner:** TBD

`math_mod_3_compress.sv` moved from rtl/common to rtl/math (commit 3ccd1fcd,
with filelist; registry PASS, no stale doc references). Reviews are done;
the formal checks remain. No harness exists yet (nothing under formal/
matches). Write the formal harness per [[formal]] (sv2v/SBY flow,
mutation rule, vacuity traps), fold the run into the formal backlog's
coverage, and close by pointing at passing proofs.

---

## MATH-007 — fp16/fp8 multiplier rounding deviates from RNE (family sweep of MATH-001)

(was drafted as MATH-006; renumbered -- the other agent's formal-suite
re-run task took MATH-006 while this was in flight)
**Status:** closed 2026-08-10 -- **FALSE ALARM on the headline claim,
verified by exhaustive/directed sweep; the sweep then found real work** (see
below and MATH-008).
**Priority:** P1 (as filed)
**Owner:** claude

The MATH-001 pattern extends beyond bf16/fp32, with per-module variation:

- `math_ieee754_2008_fp16_multiplier.sv` / `math_fp8_e4m3_multiplier.sv` /
  `math_fp8_e5m2_multiplier.sv` all compute
  `w_round_up = w_round_bit & (w_sticky_bit | w_lsb)`.
- Their mantissa_mults export only round + TRUE sticky (no fold) and NO
  guard bit, so the decision is `R & (S | LSB)` -- not RNE, and not even the
  bf16 pre-fix form: a result strictly between half and one ulp (G=1, R=1,
  S=0, L=0) rounds DOWN when it should round up.
- Fix shape (same as bf16/fp32): export the guard from each mantissa_mult
  (fp16: guard = product[11]/[10] per norm; fp8 needs the guard computed --
  check each module's bit map), connect in the multiplier, set
  `w_round_up = w_guard_bit & (w_round_bit | w_sticky_bit | w_lsb)`.
- Verify each with the sweep harness (/tmp/csa_check/tb_rne2.sv pattern):
  DUT vs a textbook-RNE behavioral reference over several thousand pairs,
  zero mismatches; then the family suites, then mutation-check (truncate
  the guard term -> RED).
- Docs: the per-module pages' rounding claims need the same sweep after
  (the claims that bf16 round_2/3 corrected likely exist on these pages).


### Disposition (2026-08-10)

**The claimed defect does not exist.** In the fp16/fp8 mantissa_mults,
`ow_round_bit` is the GUARD in G/R/S terms (the FIRST bit below the kept
mantissa -- fp16 norm case: mantissa=[20:11], round_bit=[10]) and
`ow_sticky_bit` ORs everything below it (R|S). So the multipliers'
`round & (sticky | LSB)` composes to exactly `G & (R|S|LSB)` -- textbook RNE.
The task was filed by pattern-matching the formula shape against bf16's
different naming convention, without simulating (rule 5: recompute).

**Sweep evidence** (DUT vs exact-integer-product textbook-RNE reference,
independent of any G/R/S decomposition): e4m3 and e5m2 exhaustive
(all 65,536 input pairs each), fp16/bf16/fp32 300k random + directed tie and
G=1,R=1,S=0,L=0 scans. **0 mismatches in all five formats**, with the claimed
failure pattern hit 347x in fp16 and 1240x in exhaustive e4m3. Ties with
LSB=0 (the round-half-up detector) hit hundreds-to-thousands of times per
format. Harness mutation-checked: reverting bf16 to the pre-MATH-001 formula
fails immediately.

**Real work the sweep and the fix-every-occurrence audit produced:**

- **The generators had never received MATH-001** (or several other tree-side
  hand-fixes). Regen-and-diff found 13 generated files drifted; all
  back-ported into bin/rtl_generators (bf16 + ieee754): MATH-001 RNE for
  bf16/fp32, the CLZ bit-reverse removal in five adder/FMA generators, the
  bf16_fma signed-exponent + result-priority fixes, the e4m3 round-carry
  overflow wrap guard. Full regeneration adopted; the only functional tree
  changes were the wrap guard propagating to `bf16_to_fp8_e4m3` and
  `fp32_to_fp8_e4m3`, where the bug was LIVE: input ~510 silently returned
  +0.0 with no flags (before/after sim: pre-fix 0x00/no-flags, post-fix
  0x7E/overflow=1). Lesson recorded in [[generated-rtl-discipline]].
- **NAMING NOTE comments** added (generator-side) to all fp16/fp8
  mantissa_mult + multiplier files so the guard-vs-round naming cannot be
  "fixed" into a real bug by the next reader.
- **Directed rounding-pressure stimulus** added to the shared FP test values
  (all-ones mantissa at 2^0 and 2^8): the 2^8 row is the e4m3 wrap trap, which
  random stimulus hits with ~1e-4 probability. Mutation-checked: pre-fix
  conversion RTL fails conv_15 (src=0x43FF got 0x0 expected 0x7E); fixed RTL
  passes 216/216 in all three source formats. Full val/math func regression
  135/135 after the change.
- **Doc fix**: `math_bf16_mantissa_mult.md` still showed the pre-MATH-001
  folded-sticky RTL, a note justifying the fold, and a usage example teaching
  the old formula -- rule-6 sibling miss from MATH-001's integration; fixed,
  `check_doc_instantiations.py` 0 across rtl-math.
- **Formal harness contract drift**: both mantissa_mult harnesses still
  asserted the folded sticky (found by the MATH-006 re-run); updated to true
  sticky + explicit guard property, prove+cover PASS, guard property
  mutation-checked.
- **New finding filed as MATH-008**: the underflow-edge flush (pre-round
  exponent 0 rescued by rounding carry) -- ALL FIVE multiplier formats flush
  to zero where IEEE 754 post-round detection gives min-normal.

---

## MATH-009 — goldschmidt_div iter2-pipe: ow_is_inf asserted on ZERO results, missed a==inf (FIXED)
**Status:** closed 2026-08-10 -- found and fixed in-session (the MATH-007 finish-up's
final FULL regression); flag registers un-swapped, 5/5 params pass at FULL on a
clean rebuild.
**Priority:** P1 (silent wrong status flags on a shipping datapath config)
**Owner:** claude

`math_bf16_goldschmidt_div.sv`'s ITERATIONS=2 PIPELINED=1 branch registered its
special-case conditions into each other's registers: `r_special_zero` held
`w_b_is_zero` (an INFINITY result) and `r_special_inf` held the zero-result
condition (a==0, b==inf, prescale underflow). The value mux consumed them in
the swapped sense consistently, so QUOTIENTS were correct -- but the flag path
computed `r_is_inf <= r_special_zero || r_special_inf`, so **ow_is_inf
asserted whenever the result was ZERO, and never for a==inf** (a==inf appeared
in neither register; its quotient was only right because inf propagates
through the multiply chain). ow_div_by_zero was coincidentally correct.

Found because the whole-area FULL regression finally ran (nothing since the
2026-08-06 testqc integration added the flag checks had run FULL): 2 of 5
params failed -- exactly the two iter2_pipe configs -- with quotients matching
and only ow_is_inf wrong on `0/1.0`, `1.0/inf`, `inf/1.0` and every
zero-result random. Bisected against pre-MATH-001 RTL (same failure), so it
predates today's rounding work entirely.

Fix mirrors the iter1 path's semantics: a dedicated `r_b_is_zero` for
div_by_zero and the INF/ZERO conditions in their own registers, value mux
keyed identically to the old (correct) value behavior. The failing test IS the
mutation check: it was RED against the swapped registers and is GREEN after
(5/5 at FULL, fresh 78 s build). Area lint PASS.
