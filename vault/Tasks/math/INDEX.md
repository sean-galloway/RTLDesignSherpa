# math — task rollup

**Next ID: MATH-011** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 7 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 8 | 0 | 0 |
| [issue/](issue/INDEX.md) | 2 | 0 | 1 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.


Math library (rtl/math, val/math, docs/markdown/rtl-math) work.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 7 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 8 | 0 | 0 |
| [issue/](issue/INDEX.md) | 2 | 0 | 1 | 0 | 0 |

## Recently closed

- **BUG-008** (2026-10-10) — math_fp8_e4m3_to_fp8_e5m2 NaN'd the top of the e4m3
  range (264..448); narrowing generator templates hardcoded the infinity-style
  source decode. Format-aware decode, regenerated, formal re-proven; found by the
  TASK-007 special-value grid. Record: [bug/closed/BUG-008.md](bug/closed/BUG-008.md).
- **TASK-007** (2026-10-10) — special-value Cartesian product grid propagated to the
  IEEE-754 fp_testing TB family (13 base classes + all 8 ieee754_2008 files);
  surfaced BUG-008 and the clamp comparator contract. Record:
  [task/closed/TASK-007.md](task/closed/TASK-007.md).
- **TASK-005** (2026-10-07) — IEEE 754 gradual underflow
  (`SUBNORMAL_SUPPORT`, default 0 = legacy FTZ) across all six ieee754
  fp16/fp32 arithmetic blocks plus NEW fp32 divider (Goldschmidt, 1/9/10
  cycles) and sqrt (Newton-Raphson reciprocal-sqrt, 1/10/11 cycles); exact
  integer oracles, both param values, 0 failures at gate/func/full. Five
  commits: cf9520e2b, 0dc286dbd, f0b5e3f3f, 065148c0a, 02140c782. Record:
  [task/closed/TASK-005.md](task/closed/TASK-005.md).
- **MATH-008** (2026-08-11) — underflow edge fixed to IEEE per Sean ("Follow
  ieee, I messed up"): all five multipliers now detect underflow AFTER
  rounding, so a rounding carry out of pre-round exponent 0 yields min-normal
  instead of a flush. Generators + regen, TB models rewritten to the exact
  integer datapath, directed pairs added and mutation-checked, sweep asserts
  all 2.9M+ edge cases, five formal configs re-proven, FULL regression green.
- **MATH-006** (2026-08-11) — full math formal suite dispositioned after the
  path repair: 157 PASS + mod_3_compress; 6 known intractables; 2 harness
  drifts fixed; wallace_tree_016 reconfirmed; dadda_tree_016 prove_boundary
  does not converge (3 h serial z3) — low8 passes, joins the heavy bucket.
- **MATH-009** (2026-08-10) — goldschmidt_div iter2-pipe flag registers were
  swapped; fixed, 5/5 FULL on clean rebuild.
- **MATH-007** (2026-08-10) — fp16/fp8 multiplier RNE claim was a FALSE ALARM;
  the audit still back-ported 13 generated files' hand-fixes into the
  generators and fixed a live silent-zero wrap bug in two conversions.
- **MATH-005** (2026-08-10) — mod_3_compress formal harness (prove + 7/7
  covers, mutation-checked).

## Open

_None._
