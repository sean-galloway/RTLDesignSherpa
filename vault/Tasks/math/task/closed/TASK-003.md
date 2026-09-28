# TASK-003: Re-run the full math formal suite after the path repair

> Migrated 2026-09-27 from `vault/Tasks/math/closed.md` as **MATH-006** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-11 — every config dispositioned; final entry in
the table below resolved (dadda_tree_016 prove_boundary does NOT converge:
killed at a 3 h serial z3 budget; its prove_low8 passes, so it joins the
heavy bucket honestly — sby dies loudly, no false pass).
**Priority:** P2
**Owner:** claude

All 147 `formal/common/math_*` `.sby` configs pointed at
`../../../rtl/common/math_*.sv`, which moved to `rtl/math/` in the math
split — the entire math formal suite was unrunnable (sby dies at file-copy,
loudly, so no false passes; but every recorded PASS predates the split).
Paths mechanically repaired 2026-08-09.

### 2026-08-10 full re-run (all 171 config dirs, incl. the new mod_3_compress)

| disposition | n | detail |
|---|---|---|
| PASS | 157 | prove+cover reconfirmed against current RTL |
| known BMC-intractable | 6 | softmax_8 x5, bf16_exp2 — ERROR as recorded, not regressions |
| harness contract drift, FIXED | 2 | bf16 + fp32 mantissa_mult harnesses still asserted the pre-MATH-001 folded sticky; updated to true-sticky + guard property, now PASS, mutation-checked |
| never proven (unchanged) | 3 | dadda_4to2_011, dadda_tree_032, wallace_tree_csa_032 — FORMAL_PRIORITY priority-0 rows ("Too large"/"Odd size") |
| reconfirmed serially | 1 | wallace_tree_016: low8 + boundary PASS (~35 min serial) |
| heavy, does not converge | 1 | dadda_tree_016: low8 PASS; prove_boundary killed at 1 h parallel, 1 h serial AND 3 h serial (z3 BMC) |

Operational notes (also in formal/FORMAL_TODO.md): `sby -f dir/cfg.sby`
resolves relative `[files]` paths against the CWD, not the .sby location —
run from inside each config dir. The 016 configs use task names
`prove_low8`/`prove_boundary`, so status-scrapers globbing `*_prove` miss
them.

The five multiplier configs were additionally re-proven 2026-08-11 after the
MATH-008 RTL change (prove+cover PASS all five).

---
