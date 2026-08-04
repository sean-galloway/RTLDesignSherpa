# common — task rollup

Canonical tracker for `rtl/common/` (~57 reusable building blocks).
Migrated 2026-07-23 from `rtl/common/TASKS.md`.

| Page | Count | What |
|---|---|---|
| [active.md](active.md) | 0 | in progress right now |
| [open.md](open.md) | 10 | accepted, not started |
| [closed.md](closed.md) | 7 | done (kept for history) |
| [dropped.md](dropped.md) | 0 | ended without completing |

The library is a stable, mature baseline: all modules production-ready, 100%
module test coverage, no blocking issues. Activity is maintenance, coverage and
integration support.

## Open shortlist

- **COMMON-010** — every module MUST have a filelist + registry entry. Coverage
  is already good; the gap is that **nothing enforces it**. Shared gate with
  AMBA TASK-026.
- **COMMON-017** — SETTLED: the arbiter compliance model does not model
  `block_arb`, so it reports a false round-robin violation on the first grant
  after a block. The RTL is correct (`r_last_valid` drops, mask falls back to
  client 0). Fix belongs in the DV framework; one error type is excluded by
  name meanwhile.
- **COMMON-016** — arbiter ACK mode: 105 unexpected ACKs per run, and the
  compliance model was being consumed only to raise its timeout. Now asserted
  on errors; the warnings need diagnosing before they become errors.
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
