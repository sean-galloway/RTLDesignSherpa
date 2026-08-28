# bridge — task rollup

**Next ID: BRIDGE-006** — never recycle a number, even when its task closed.

Bridge crossbar generator (`projects/components/bridge/`): the CSV/toml-driven
generator, its generated wrappers/xbars/adapters, and their DV.

| State | Count |
|---|---|
| [active](active.md) | 0 |
| [open](open.md) | 1 |
| [closed](closed.md) | 4 |
| [dropped](dropped.md) | 0 |

## Open

- **BRIDGE-003** — all six `*_mon_monitor` stress tests fail; verified
  pre-existing at the branch base (not fallout from the BRIDGE-001 fixes).
  Likely tied to the stream-mon AW/W decoupling WIP.
- **BRIDGE-002** — AMBA5 bridge support: AXI5 ports on the AMBA4 fabric first
  (wrappers/BFMs/compliance already in-tree; gaps are AXI5<->AXI4 feature
  conversion and a `*_to_apb5` shim), native-AXI5 sideband and AWATOP
  R-channel routing as follow-ons.

> Note: the pre-migration `projects/components/bridge/TASKS.md` still needs
> folding in (part of TOOL-001); the master `/vault/Tasks/INDEX.md` row
> points here.

Practice and rationale live in the [handbook](../../handbook/INDEX.md);
this directory tracks *work* only. `/GLOBAL_REQUIREMENTS.md` wins on conflict.
