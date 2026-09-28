# math — task rollup

**Next ID: MATH-011** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 4 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 6 | 0 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 1 | 0 | 0 |

Items live one per file under the lane directories below; this page is the
area overview. See [the convention](../INDEX.md) for the definitions.


Math library (rtl/math, val/math, docs/markdown/rtl-math) work.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 3 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 5 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 1 | 0 | 0 |

## Recently closed

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
