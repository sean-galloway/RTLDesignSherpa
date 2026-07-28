# bridge — task rollup

Bridge crossbar generator (`projects/components/bridge/`): the CSV/toml-driven
generator, its generated wrappers/xbars/adapters, and their DV.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 1 |
| [closed](closed.md) | 0 |
| [dropped](dropped.md) | 0 |

## Open

- **BRIDGE-001** — the generator emits `NUM_SLAVES` as a body localparam while
  using it in the port list of the generated xbars. Verilator accepts; strict
  front ends reject; the pre-commit declaration-order hook blocks. Fix in the
  generator, then a FULL regeneration (rule #0).

> Note: this area currently holds only BRIDGE-001. The pre-migration
> `projects/components/bridge/TASKS.md` still needs folding in (part of
> TOOL-001); the master `/vault/Tasks/INDEX.md` row points here.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
