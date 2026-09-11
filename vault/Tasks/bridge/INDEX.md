# bridge — task rollup

**Next ID: BRIDGE-018** — never recycle a number, even when its task closed.

Bridge crossbar generator (`projects/components/bridge/`): the CSV/toml-driven
generator, its generated wrappers/xbars/adapters, and their DV.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 2 |
| [closed](closed.md) | 15 |
| [dropped](dropped.md) | 2 |

## Open

- **BRIDGE-014** — AXI5-Lite and APB5 as MASTER protocols; a native-AXI5 fabric.
  Filed when BRIDGE-002 closed; no consumer yet.
- **BRIDGE-017** — legacy backlog carried over from the retired TASKS.md
  (perf characterization, synthesis guide, async CDC, QoS aging, xbar
  pipelining).

> The pre-migration `projects/components/bridge/TASKS.md` was folded in on
> 2026-09-10: ledger at the end of [closed](closed.md), leftovers in
> BRIDGE-017 and [dropped](dropped.md). The file is retired.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
