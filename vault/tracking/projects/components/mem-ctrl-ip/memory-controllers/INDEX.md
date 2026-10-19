---
title: memory-controllers tasks
summary: Cross-controller task lane for the mem-ctrl-ip family (pumice DDR2/LPDDR2, scoria DDR3/LPDDR3, andesite DDR4/LPDDR4; basalt reserved).
---

# memory-controllers — task rollup

**Next ID: MC-002** — never recycle a number, even when its task closed.

**Every item is its own file**, `<ID>.md`, filed under the directory for its
state (`open/`, `active/`, `closed/`, `dropped/`). Moving an item between
states is `git mv`, so an item is in exactly one state by construction.

## Lanes

| Lane | For | Next ID |
|---|---|---|
| [task/](task/INDEX.md) | planned work we decided to do | `MC-002` |

Family-wide conventions live here (see
[ADVANCED_MODES_ROADMAP.md](ADVANCED_MODES_ROADMAP.md) for the feature
roadmap): macros are `*_layer` (MC-001), FUB training interfaces keep
`*_ifc`.
