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
