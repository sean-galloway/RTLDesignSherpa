# memory-controllers — task lane

**Next ID: MC-017** — never recycle a number.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 3 | in progress right now |
| [closed/](closed/) | 10 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open

- **MC-016** -- a cross-bank row-hit-first pick for granite's `mixed` window:
  the model prices strict per-bank FIFOs 11 % under a pooled row-hit-first
  queue on `mixed` (320 vs 360) and equal everywhere else; granite's two-head
  store sits between -- model it first, then decide. Filed 2026-11-12 from
  MC-013 item 4.
- **MC-015** -- the write stream pays one command slot per AXI burst at the
  intake, both controllers: with MC-014's lane on, granite reads reach 773 /
  775 on `col_major_interleaved` / `row_thrash` and writes stay at 686 / 687
  (7 WRs a cycle apart, then a gap of 2, per burst; identical with the lane
  off). Not the scheduler: upstream, per AXI burst. Filed 2026-11-12.

## Active

- **MC-014** -- a row lane on granite's bank-pick core (dual issue): the
  2026-11-12 sim traced the sku100 bank-parallel miss cells to one command
  slot per MC cycle (97 % occupancy, ACT every 9 cycles); pumice's lane on the
  same DFI path recovers +13 % reads. Priced +92..+145 MB/s. Filed and started
  2026-11-12: `mc_bank_pick` DUAL_ISSUE lane, plane / granite_core / top /
  CSR plumbing built; sim reads 773 / 775 / 722 (within 1 % of the ideal on
  the pure families). Board half in progress: the first sys100 build with the
  lane missed by 1.7 ns (the lane pick behind the main select, the lane fire
  on the command-valid cone); both cut 2026-11-12, rebuild and board runs.

- **MC-011** -- the 0.2 ns clock-uncertainty budget is in both board XDCs;
  sweep 1: pumice sys75 closes by 0.100 under budget on the worst of three
  placements, granite sys75 by 0.817, granite sys100 does not close (-0.335
  worst, the bank-pick select loop). Open work: the two cones. Active 2026-11-08.
- **MC-004** -- two-register `gaxi_skid_buffer`, no data reset, no shift
  (ISSUE-001 row 1; ~3k LUT chip-wide). Started 2026-11-06.

## Deferred

- **MC-009** -- pumice arbiter: steps (a) and (c) done (the STAGE-1b
  selection out of the classify cone; build-time pick modes). Step (b), hit /
  sibling flags in the CAM, parked until the research configuration has to
  close 75 MHz on the board. Deferred 2026-11-08.

## Closed

- **MC-013** -- model-driven policy exploration on the Ramulator 2 DDR2 model,
  five items: the command slot (-> MC-014, built), write drain (granite is at
  the deep end already), refresh placement (0.6 % recoverable, the rest is
  tRFC), per-bank vs pooled queues (`BankFIFO-RR` in the overlay; `mixed`
  -11 % -> MC-016), a cocotb AXI trace exporter (the rebuilt streams
  confirmed, `mixed` switched to captured). Closed 2026-11-12.

- **MC-012** -- Ramulator 2 pinned and built from `references/ramulator2/fetch.sh`;
  DDR2 / DDR2_BL8 device classes checked against JESD79-2F (found BUG-003);
  the board's char streams replayed through the ideal controller beside the
  measured sku100 cells: granite at the refresh ceiling on row hits, the
  `col_major` gap is the 2 CK timer granularity exactly, the bank-parallel
  miss families sit 12-21 % under the ideal (single command slot per MC
  cycle the candidate). Closed 2026-11-11.

- **MC-005** -- storage arrays out of `ALWAYS_FF_RST` into reset-free
  `always_ff` (ISSUE-001 row 2b): phases 1-2 (common-ip + harness, -2,042 /
  -2,198 routed LUT with MC-004) 2026-11-06/07, phase 3 (the bridge generator,
  bridge TASK-024) 2026-11-10 -- Synth 8-4767 bridge arrays 17 -> 0 on both
  controllers. Closed 2026-11-10.

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
