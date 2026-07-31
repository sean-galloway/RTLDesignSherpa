# common — task rollup

Canonical tracker for `rtl/common/` (~57 reusable building blocks).
Migrated 2026-07-23 from `rtl/common/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 9 | accepted, not started |
| [closed.md](closed.md) | 6 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

The library is a stable, mature baseline: all modules production-ready, 100%
module test coverage, no blocking issues. Activity is maintenance, coverage and
integration support.

## Open shortlist

- **COMMON-010** — every module MUST have a filelist + registry entry. Coverage
  is already good; the gap is that **nothing enforces it**. Shared gate with
  AMBA TASK-026.
- **COMMON-011** — `counter.sv` tick not gated during reset. Low severity, but
  the edge-case test is disabled with `if False:` — a silent test.
- **COMMON-014/015** — two latent RTL corners from qc round_2: `fifo_control`
  defaults contradict its own DEPTH == 2^ADDR_WIDTH constraint, and
  `shifter_beat_pack` truncates an over-wide runtime beat config to 0. Both
  P3 — neither is reachable through the modules' real callers.
- **COMMON-003** — integration examples (P2).
- **COMMON-006/007/008/009** — deferred enhancements (P3). COMMON-009 (BCH) is
  the only place BCH is tracked; the docs-only `components/bch/` placeholder was
  deleted 2026-07-23.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
