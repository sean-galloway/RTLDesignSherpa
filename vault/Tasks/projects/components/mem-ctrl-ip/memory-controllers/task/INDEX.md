# memory-controllers — task lane

**Next ID: MC-003** — never recycle a number.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **MC-002** — GTKWave debug views for every mem-ctrl fub/macro + top
  wr/rd DFI paths: one validated `.gtkw` per tested common-ip fub/macro in
  its tests area, and per-core top views for the write path to DFI and the
  read path to/from DFI (pumice/scoria/andesite/granite).

## Closed

- **MC-001** — macro names to the `*_layer` convention on every memory
  controller: pumice_axi4_ifc → pumice_axi4_layer, mem_cmd_scheduler →
  scheduler_layer on all three trees; *_dfi_layer already conforms; FUB
  training `*_ifc` blocks stay. Landed on andesite as the four
  `andesite_*_layer` macros (scheduler/training/dfi/axi4) + `andesite_core`
  top under TASK-016 (closed 2026-10-05), completing the convention on all
  three trees.
