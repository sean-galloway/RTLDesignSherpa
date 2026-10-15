# memory-controllers — task lane

**Next ID: MC-003** — never recycle a number.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **MC-003** — granite's intended per-bank in-order scheduler core
  (per-bank head sequencers + cross-bank mux on the existing fire-stage
  JEDEC authority; the FR-FCFS pick core is the research core — pumice's).
  Supersedes the `BANK_IN_ORDER` pick-mask approach, measured on silicon
  2026-10-15 to serialize single-bank traffic at pick-pipe depth (revert
  `7a7f80b00`).

## Closed

- **MC-002** — GTKWave debug views for every mem-ctrl fub/macro + top
  wr/rd DFI paths. Landed 2026-10-12: generator
  (`common-ip/dv/tools/gen_gtkw.py`, fst->vcd, house format, every emitted
  path validated 0-missing against a real dump) + curated specs
  (`gtkw_curated_{fubs,macros,tops}.py`). 24 views: 14 fub (22-50 signals),
  2 macro (dfi_plane, axi4_plane), 9 top (granite_core, granite_top_geared,
  pumice_core x {wr_engine_path, rd_engine_path, planes_axi_to_dfi}).
  16 test files gained WAVES/--trace support (7 pumice fubs, 3 pumice macro,
  3 tops incl. granite's two). Skips, documented: test_pumice_config_array +
  test_pumice_telemetry_invariants (multi-DUT, no wave support),
  pumice_scheduler_plane macro (filelist absent), scoria/andesite macros (out
  of scope). Commits 8f30b80b6, a3d52c706, 270fb791f, ae1c0c9a1.

## Closed

- **MC-001** — macro names to the `*_layer` convention on every memory
  controller: pumice_axi4_ifc → pumice_axi4_layer, mem_cmd_scheduler →
  scheduler_layer on all three trees; *_dfi_layer already conforms; FUB
  training `*_ifc` blocks stay. Landed on andesite as the four
  `andesite_*_layer` macros (scheduler/training/dfi/axi4) + `andesite_core`
  top under TASK-016 (closed 2026-10-05), completing the convention on all
  three trees.
