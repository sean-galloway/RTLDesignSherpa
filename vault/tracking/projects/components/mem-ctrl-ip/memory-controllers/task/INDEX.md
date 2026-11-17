# memory-controllers — task lane

**Next ID: MC-021** — never recycle a number.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 17 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 1 | parked pending a named condition |

## Open

- **MC-019** -- the row lane carries ACT only: the SKU model prices a PRE on
  the lane at 0.0 on all 29 MC-018 patterns (PRE-only = lane off, ACT-only =
  the SKU); drop the PRE class from the lane for logic out of the 100 MHz
  cone, gated by `TEST_DUAL` both ways, formal and the no-knob sys100 build.
  Filed 2026-11-17 from MC-018.
- **MC-020** -- a row command into the idle main slot or the column's own
  bank: the one-slot rule still costs `col_major` +14.6 / +9.5 / +5.3 percent
  (bl4 / 8 / 16) and the two-bank interleave +4 .. +6 in the model, nothing
  elsewhere; MC-014 cut the alone-firing lane for the 100 MHz cone, so the
  task is a form that does not re-enter it, priced in the model first.
  Filed 2026-11-17 from MC-018.

## Active



## Deferred

- **MC-009** -- pumice arbiter: steps (a) and (c) done (the STAGE-1b
  selection out of the classify cone; build-time pick modes). Step (b), hit /
  sibling flags in the CAM, parked until the research configuration has to
  close 75 MHz on the board. Deferred 2026-11-08.

## Closed

- **MC-018** -- the granite FPGA SKU as a Ramulator configuration:
  `granite_sku100` (the overlay's `GraniteSKU` controller -- bank-FIFO store
  with the per-burst `BANK_CAP_MIXED`, the pick core's select and MC-017
  direction register, the row lane on the odd CK, close-on-drain, one slot
  per MC cycle -- on the host's MC-cycle timings with the PHY-window tRTW as
  `nRTW`). Every open-page cell of the SKU preset inside the stated tolerance
  (row-hit +0.4 .. +1.2 %, `col_major` within 0.6, `random` +3 .. +4, `mixed`
  +9 on the union); `bank_interleave`, `close_page` and the `mixed` turn
  structure filed as ISSUE-002 / 003 / 004. The 644-cell pattern x variant
  sweep filed MC-019 and MC-020 and recorded the rest (pool 24 / 32, pool 8,
  refresh burst, peek, caps, hold, batch, the JEDEC tRTW). Closed 2026-11-17.

- **MC-011** -- timing is predictable or it is not closed: the 0.2 ns
  clock-uncertainty budget in both board XDCs, config CSRs as false paths, and
  a three-directive placement sweep as the gate. Worst-of-three under the
  budget: pumice sys75 +0.028, granite sys75 +1.338, granite sys100 +0.002
  (2026-11-09); every sys100 rebuild since (MC-014 / 015 / 017) closed under
  it. Plan step 2 (pumice fire-stage lookahead) was margin beyond the gate and
  is not re-filed. Closed 2026-11-16.
- **MC-004** -- two-register `gaxi_skid_buffer`, no data reset, no shift
  (ISSUE-001 row 1): `DATA_RST` parameter (default 0 = the new form), skid
  suite FULL 61/61, formal prove + cover, routed same-tree A/B pumice -2,198 /
  granite -2,042 LUT with MC-005. Landed 2026-11-07 (429ccc5cf); closed
  2026-11-16.
- **MC-017** -- the `mixed` window's direction register: every cap flip
  handed the register to the waiting direction for five cycles and no
  columns (136 of 143 read turns; a write column, hinted ungated after the
  owner's PRE / ACT on the shared bank, took it back with a fresh 255). The
  cap sweep (16-255) was not the lever. Four register-only terms in
  `mc_bank_pick` (hint direction gate, drain flip under the idle hold and
  not while a row request / row winner is live, the lane counts only
  gate-allowed columns) make every turn carry its batch: `mixed` 272 / 272
  on the board at both presets (was 318 / 649 and 473 / 286), worst read
  wait 52 000 -> 520 cycles, single-direction cells unchanged, +0.012 ns
  under budget. Union -5..-14 % lane on, +1..+6 % lane off on this window.
  Formal x5, granite / pumice / common-ip / char fw suites pass. Closed
  2026-11-15.
- **MC-016** -- "model the two-head store first": the second head is not a
  scheduling peek (read only in the pop shadow; its hit is the stored
  same-row bit), and a real one would buy nothing at AxLEN 8 -- a
  `peek_depth` on the overlay's `BankFIFO-RR` is bit-identical to the strict
  FIFO at depths 2 / 4 / 8 on `mixed` at pool 8 / 16 / 32 (the entries behind
  a head are its own burst). Granite's `mixed` gap is the direction rule, not
  the queue shape (-> MC-017). No RTL. Closed 2026-11-15.
- **MC-015** -- "one command slot per AXI write burst" was the FIFO store's
  8-entry write pool: eight slots at a nine-cycle turnaround = 8/9 of a command
  per cycle (686 of 781). A per-hop valid/ready probe (`PERF_W_HOPS`) named it
  in one run. Pool 16 in sim: granite 686 -> 766-769 writes on
  `col_major_interleaved` / `row_thrash`, pumice 682 -> 768 (same pool);
  board sys100 `GRANITE_NUM_ENTRIES=16` +0.034 ns / 0 EP, +913 LUT, writes
  688 -> 768-770 level with reads, `mixed` swaps shape between presets
  (-> MC-016). SKU default stays 8, the owner's call. Closed 2026-11-13.
- **MC-014** -- a row lane on granite's bank-pick core (dual issue):
  `mc_bank_pick` DUAL_ISSUE, the plane's `a2_*`, granite_core / top / CSR
  plumbing, `GRANITE_DUAL_ISSUE=1` board builds. Sim reads 686 -> 774 / 687
  -> 773 / 656 -> 721 on col_major_interleaved / row_thrash / random (within
  1 % of the model's best policy); five sys100 builds to +0.059 ns under the
  budget (four register-only cuts, one hold-mask liveness fix the board
  confirmed); board cells with the lane on in
  `char_results/board_mc014_granite_row_lane_sku100_2026-11-12.md`. Writes
  unchanged (MC-015). Closed 2026-11-12.
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
