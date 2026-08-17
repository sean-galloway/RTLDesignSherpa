<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# bridge — closed

## BRIDGE-001 — Generator emits NUM_SLAVES as a body localparam used in the port list
**Status:** closed 2026-08-08 (opened 2026-07-28)
**Priority:** P1 — blocked clean commits of any regenerated bridge

**Resolution (2026-08-08):** fixed on `fix/bridge-xbar-num-slaves-param`:

- Generator emits `NUM_SLAVES` in the parameter port list
  (`16841bce`); all bridges regenerated together; pre-commit
  decl-order hook passes with no `--no-verify`.
- The class sweep found and fixed the bigger sibling: all four
  generators emitted `import <bridge>_pkg::*;` at $unit scope with
  package types/localparams in the ANSI header — same
  Verilator-tolerant / strict-frontend-fatal asymmetry, plus $unit
  struct-type collisions for multi-bridge compilation units. Now the
  LRM module-header import form (`6f99c889`).
- Full bridge DV: 25/25 non-monitor tests green from clean builds.
  **Still broken (pre-existing, NOT this task):** all six
  `*_mon_monitor` stress tests fail identically at this branch's
  BASE commit (verified in a worktree at the pre-fix parent) — see
  BRIDGE-003.

## BRIDGE-003 — All six *_mon_monitor stress tests fail (pre-existing)
**Status:** closed 2026-08-16 — 6/6 green; 5963b2dc

Two independent causes, which is why this looked stuck for so long.

**Cause 1 (monitor RTL, fixed by the other agent).** Landed on main as
3ca1b9fb / merge 1451b5a8. Rerunning the six immediately after took the
suite from **0/6 to 3/6**: `1x2_rd`, `1x2_rd_regblock` and `mix_a`
passed, `mix_b/c/d` still failed.

**Cause 2 (testbench, fixed here).** `stress_read_plan` stepped offsets
by the SLAVE word (4 B) while `run_err_bp_phase` computed its expected
value via `tb.slave_mem_read(...)`, which derives `byte_count` from the
MASTER width. With a 64-bit master over the 4 KB seeded window, drawing
the top offset gave an 8-byte read at `0xFFC` — four bytes past the
cap. `MemoryModel` raised `ValueError`, and since that call sits
outside the phase's `try/except` (which only catches `RuntimeError` for
SLVERR), the phase died on an uncaught exception instead of reporting a
mismatch. Hence logs that simply stopped mid-run at the warning.

The plan now reserves room for a full master-width access:
`max_word = (CAP - access) // WORD + 1`. A 32-bit master still gets
1024 choices, so previously-passing tests are untouched.

**Worth remembering:** this was latent, not per-test. `mix_a` has the
same 64-bit master as `mix_b/c/d` and passed only because its random
draw never landed on the last word — a seed change would have moved the
failure around and made it look flaky.

**Re-verified 2026-08-17** from a genuinely clean build (all 13
`*_mon_monitor` in one pass, 55 min): all six are green. The earlier
6/6 had run behind a `make clean-all` that silently aborted, so this is
the result that actually counts.

**Not in scope, still failing:** of the seven other tests sharing this
helper, `1x2_wr_axi5`, `_axi5a` and `_axi5n` fail. Confirmed
pre-existing and unrelated by stashing this change and reproducing the
identical failure at HEAD in 1.1 s, before any traffic runs. Tracked as
[[BRIDGE-004]].

