# memory-controllers — task lane

**Next ID: MC-011** — never recycle a number.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 2 | in progress right now |
| [closed/](closed/) | 7 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open

(none)

## Active

- **MC-004** -- two-register `gaxi_skid_buffer`, no data reset, no shift
  (ISSUE-001 row 1; ~3k LUT chip-wide). Started 2026-11-06.
- **MC-005** -- storage arrays out of `ALWAYS_FF_RST` into reset-free
  `always_ff` with the live state kept in the reset block (ISSUE-001 row 2b;
  35 / 30 arrays dissolved to flops today). Started 2026-11-06.

## Deferred

- **MC-009** -- pumice arbiter: steps (a) and (c) done (the STAGE-1b
  selection out of the classify cone; build-time pick modes). Step (b), hit /
  sibling flags in the CAM, parked until the research configuration has to
  close 75 MHz on the board. Deferred 2026-11-08.

## Closed

- **MC-006** -- pumice FPGA SKU build knobs (merge, snarf, narrow pack off;
  mapper one-hot; CAM default 8). Closed 2026-11-08: the SKU closes sys75 at
  +0.230 / 38,970 LUT and runs `windows` on the board at 75 MHz 4 / 4.
- **MC-007** -- timer / plane mechanical rows: `S_MAX` serial scan, timeout
  request registered, timer CSR loads hoisted. Closed 2026-11-08; row 7 (SRL
  delay lines) deferred on measurement.
- **MC-008** -- ring shadow readiness at fetch, `r_src` reset-free; the ring
  proof's undriven merge ports fixed. Closed 2026-11-08; row 10 closed on the
  SKU (age logic has no reader), row 5 deferred (area only).
- **MC-010** -- granite bank queues as `mc_bank_queue` (shift-register head,
  LUTRAM tail) when HAS_AGE = 0, proved equivalent to the age FIFO. Closed
  2026-11-08; row 15 (pick rotor) deferred on measurement.
- **MC-003** — granite's per-bank in-order scheduler core: shipped as
  `mc_bank_pick` over the age-FIFO store (granite TASK-002), BANK_PICK the
  granite default; pumice closes at 75 MHz and granite at 100 MHz with the
  DDR2-400 board point measured (granite TASK-003). CLOSED 2026-10-29.
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

- **MC-001** — macro names to the `*_layer` convention on every memory
  controller: pumice_axi4_ifc → pumice_axi4_layer, mem_cmd_scheduler →
  scheduler_layer on all three trees; *_dfi_layer already conforms; FUB
  training `*_ifc` blocks stay. Landed on andesite as the four
  `andesite_*_layer` macros (scheduler/training/dfi/axi4) + `andesite_core`
  top under TASK-016 (closed 2026-10-05), completing the convention on all
  three trees.
