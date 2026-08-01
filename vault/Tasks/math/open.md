<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# math — Open

## MATH-001 — Decide: bf16 multiplier rounding is not RNE — intended or RTL defect?
**Status:** open 2026-07-29 (surfaced by math qc round_1; previously noted in dropped DOCREV-001)
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
## MATH-003 — filelist coverage: 134 math modules have no .f; 106 of 119 math tests hand-list sources
**Status:** open 2026-07-31 (math test-audit round_1, 38 findings in the class)
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

## MATH-004 — levels are decorative: TEST_LEVEL exported but never gates depth; FULL == FUNC grids
**Status:** open 2026-07-31 (math test-audit round_1, 59 findings in the class)
**Priority:** P2 — per-TB design work, not mechanical
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
