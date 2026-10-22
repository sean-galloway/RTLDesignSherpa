# mem-ctrl recovery — Phase 3 report (2026-10-22)

Plan: `docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md` §3 Phase 3
(timing: 100 MHz the target, 75 MHz the floor; every claim names the clock,
the WNS, the failing-endpoint count and the total-endpoint count). Tree:
shared `main`, HEAD at start c8ea5d926 (Phase 2). Owner's answers for this
phase: on a miss, clear the component's `debug/` folder and put the binned
timings xlsx there with separate rd / wr diagrams of the failing paths drawn
in red; pumice only, both cores, both clocks.

## 1. Where the Phase 2 text stood (the reason for this phase)

| build | clock | WNS (ns) | failing / total endpoints | of which in the controller |
|---|---|---|---|---|
| build-perf `PUMICE_SYS_75=1`, BANK_PICK (Phase 2 text) | `w_sys_i` 75 MHz | -3.175 | 122 / 77 059 | 17 (record slot -> pop-shadow slot compare -> record mux -> stale-winner mask -> arbiter -> winner register, 12.3 ns of route); the other 105 are the harness read engines |
| build-perf `PUMICE_SYS_100=1`, BANK_PICK (Phase 2 text) | `w_sys_i` 100 MHz | -6.672 | 11 899 / 77 058 | 5 492; 8 482 harness (hist_rd / hist_wr / gen engines) |
| build-perf `PUMICE_SYS_75=1`, FRFCFS (`PUMICE_SCHED_CORE=0`, control) | `w_sys_i` 75 MHz | +0.028 | 0 / 76 901 | - |
| build-perf `PUMICE_SYS_100=1`, FRFCFS (control) | `w_sys_i` 100 MHz | -2.555 | 6 296 / 77 003 | the harness dominates (hist_rd 1 002, hist_wr 866, gen write engines 404 + 312 ...) |

Two facts fall out of the control builds. The ddr2_char harness itself does
not close 100 MHz with either core, so a 100 MHz claim for the controller
can only come from an out-of-context implementation of `pumice_core`; and
the Phase 2 pick core, deeply pipelined as it is, failed 75 MHz on ONE
combinational arc that bypassed the pipeline: the fire cone (record mux,
hit compare, live timers) fed the winner register's load enable (hold on a
closed timer) and, through the stale-winner mask, the arbiter.

## 2. What changed (all in the scheduler / storage planes; no DFI-plane change)

| change | why | where |
|---|---|---|
| Record carries `hit`, classified at the storage edge against the scheduler plane's REGISTERED row image (`bank_row_active_i`, `bank_open_row_i` on `mc_bank_head_records`); one cycle stale by construction; the fire stage ANDs it with live row-active | the 16:1 record mux -> 14-bit row compare was on the arbiter path | `mc_common_pkg.sv`, `mc_bank_head_records.sv`, `mc_storage_plane.sv`, `pumice_core.sv`, `granite_core.sv` (scoria / andesite tie the new inputs off) |
| Pop shadow is one bit per pair, no slot compare | the slot compare was a record read on the arbiter path | `mc_bank_pick.sv` |
| The pick register loads every cycle; a winner waiting on a timer holds through a register-to-register mux (a registered "waiting" bit selects last cycle's effective winner over the fresh pick), bounded by the bank's lookahead bit; the search starts past the effective winner, and the effective winner's own pair is masked out of the pick for one cycle when its request cannot be its next command (a row command, or a column with nothing behind it). The mask is registered from next cycle's effective winner, which this cycle already knows: three sources (held winner, speculation, fresh pick as the arbiter's one-hot) registered separately and resolved by the registered hold / speculation bits, so it is one AND at the arbiter's root; computed live it sat at the root of the arbiter cone (14 levels, -1.7 ns at synthesis) | the Phase 2 hold put the fire cone on the winner register's load enable; the first Phase 3 form (no hold, search past the fresh pick every cycle) walked on under tCCD and fired whichever pair the rotor had reached (bank 0's second read before banks 1-3's first; the return ring then held slots for the out-of-order tickets: +20 cycles on `perf_read_inflight`); a rotor that moved only on a fire re-picked the fired pair in the fire cycle, before anything registered could mask it (bank-rotating single-entry writes at 50% at the board geometry); an unbounded hold starved the next requester behind a long-gated bank (contract bench `hold_on_gate_block`) | `mc_bank_pick.sv` |
| Hint only when the hop equals the pipe depth; hops shorter than the pipe are speculated on the held winner from registers only (ACT->COL, PRE->ACT, last COL->PRE, COL->COL on the same row when no other pair asks); the COL->COL speculation requires the candidate's own recorded hit | the direct winner load from the hint was a fire-cone arc; the stale record hit after an ACT cost one cycle per row on col_major (gap 2 before every inter-row hop); keyed on `behind_same_row` alone the COL->COL speculation re-loaded a column for a pair whose next entry was a miss and the PRE never won (351k-cycle write hang on col_major) | `mc_bank_pick.sv` |
| Write sink: ONE register-only predicate from the CAM, `wr_commit_ready_now` (the CAM's own accept condition: queue ready and registered occupancy below `WR_DRAIN_AHEAD`; no commit_valid, no drain-pop term), gated at the arbiter and re-checked at fire | the earlier `commit_ready` was a function of commit_valid (loop); the interim acc / noacc split subtracted the drain pop, which reaches through the fetch arbitration to BOTH consumer readies (DFI `cm_rd_ready`, AXI `snarf_rd_ready`) -- the worst 100 MHz cone (AXI order FIFO -> drain pop -> arbiter -> winner, 18 levels, -2.5 ns) -- and it assumed the held winner would commit, which under tCCD gated every other request and cost one cycle per burst on `perf_write_ceiling` (83%) | `mc_wr_data_cam.sv`, `mc_xddr2_entry_store.sv`, `mc_storage_plane.sv`, `mc_scheduler_plane.sv`, `mc_bank_pick.sv`, both cores, the contract bench |
| Refresh grant pulses only after init (`init_done_i`) | the init sequence's two REFs pass through the same override and the refresh controller banks any grant with no backlog as a pull-in credit; two init-time credits consumed the first two tREFI ticks of every run (pumice ISSUE-022: exactly 2 tREFI soft violations per BANK_PICK run, none on FRFCFS) and left `refresh_credit`'s strict arm one REF short once the core ran its stretch faster (16.5 vs Phase 2's 27 cycles per burst) | `mc_bank_pick.sv`; ISSUE-022 closed |
| pumice `BOARD_GEOM` gets its own `SIM_BUILD_ROOT` | cocotb-test rebuilds only on source mtime, so the board geometry (a Verilator parameter) ran on the default geometry's models: 217 cells in 113 s, three failures against BL8 models, and the Phase 2 "216 passed at the board geometry" was the same reuse reporting green | `dv/tests/Makefile`; handbook `running-regressions` |
| `bin/vivado_timing_failures.py --xlsx` (sheets: cones by instance pair, bins, raw; negative slack in red); `bin/render_block_diagram.py` reports the title state | the owner's miss deliverable; the owner's bold-top-title rule (same day) | `bin/`, handbook `block-diagrams` |
| build-perf: `PUMICE_SYS_100=1` MMCM profile (VCO 800, sys 100, sys2x 200, idelay /4, `FPGA_CLK_HZ` 100e6) and `PUMICE_SCHED_CORE=0|1` define | the two clocks and the two cores from one flow | `ddr2_char_top.sv`, `fpga/tcl/create_project.tcl` |

Each bring-up finding above was caught by a regression cell or a perf
proxy on the way, never by inspection: the hang by the col_major proxy
(wr_ok false, 2 038 mismatches, WR gap histogram with one 351 627-cycle
entry), the per-burst write loss by `perf_write_ceiling` (208 stalls of
max run 1, fires every 5 cycles at tCCD 4 in the pick trace), the read
ordering loss by `perf_read_inflight` (R-channel burst cadence: Phase 2
248 x 4 + 7 x 10, the interim text 239 x 4 + 7 x 6 + 8 x 8 + one 20).

## 3. Timing, final text

### 3.1 `pumice_core` out of context (synth + opt + place + phys_opt + route, xc7a100t-1, `-mode out_of_context`, SCHED_CORE=BANK_PICK)

| clock | period | WNS (ns) | failing / total endpoints | worst cone (startpoint -> endpoint instance, count, logic / route ns) |
|---|---|---|---|---|
| aclk | 10 ns (100 MHz) | -0.611 | 156 / 16 387 | write CAM snarf match (registered probe row vs entries) -> read CAM: 83 endpoints at -0.33, 2.7 / 7.5; pick core refresh counter -> bank timer presets 49 at -0.32; drain occupancy -> write column gate -> the registered stale mask 14 at -0.61, 2.7 / 7.9; bank timer -> hold bit 7 at -0.29; request register -> arbiter -> pick register 2 at -0.36 |
| dfi_clk | 5 ns (200 MHz) | -2.358 | 485 / 2 767 | `mc_dfi_rd_aligner` age -> rd CDC FIFO write: 362 endpoints; aligner -> credit 31; CDC -> cmd formatter 33; wr serializer -> wd CDC 12 |

Synthesis estimate for the same run: aclk -0.383 (14 / 16 381), dfi_clk
-2.998 (404 / 2 763). The aclk cones are route-dominated (2-3 ns of logic
in 7-8 ns of route on a 20%-full part placed with no floorplan), and
placements of near-identical text swung the post-route aclk WNS between
-0.19 and -0.71 ns across this phase. The number to believe is the
synthesis estimate plus the floorplan the harness build will impose. No
aclk cone crosses the storage / scheduler boundary any more except the
registered sink predicate into the registered mask, and no fire-cone arc
reaches a register's load enable. The dfi_clk cone is the one the plan
names as independent of the pick core (the parked plan's Task 5 skid); it
is unchanged by this phase.

Utilisation of the core: 12 420 LUT / 7 402 FF (Phase 2 text: 12 221 /
7 332).

The same OOC flow on the intermediate texts, for the record (aclk, 100 MHz,
post-route): Phase 2 text + record hit + one-hot shadow + every-cycle winner
load: -2.525, 1 057 / 16 323 (drain-pop cone); + `wr_commit_ready_now`:
-0.192, 116 / 16 319; + rotor-on-fire: -0.520, 23 / 16 320; + the hold mux:
-0.212, 4 / 16 323; + the grant gate: -0.708, 405 / 16 316; + the stale
mask computed live: -2.187, 1 332 (synthesis -1.67 / 330: the mask at the
arbiter's root); + the mask registered per source: -0.611, 156 (synthesis
-0.383 / 14).

### 3.2 build-perf board builds (ddr2_char harness + pumice, Nexys A7)

| build | clock | WNS (ns) | failing / total endpoints |
|---|---|---|---|
| `PUMICE_SYS_75=1`, BANK_PICK, final text | `w_sys_i` 75 MHz | +0.077 | 0 / 77 093 (the text before the stale mask: +0.102, 0 / 77 028; Phase 2 text: -3.175, 122) |
| `PUMICE_SYS_100=1`, BANK_PICK, final text | `w_sys_i` 100 MHz | -2.574 | 3 463 / 77 128 (the text before the stale mask: -2.537, 3 062 / 77 056; Phase 2 text: -6.672, 11 899; FRFCFS control: -2.555, 6 296). Hotspots: read CAM 442, write CAM 247, the pick core 238, bank timers ~100 each, then the harness (APB converter 140, generators, trace RAMs) |

The 75 MHz build is the gate (WNS >= 0 on `w_sys_i`): closed, +0.077. The
100 MHz board build misses by 2.6 ns; the harness alone cannot close it
(section 1). Its failing endpoints are binned in
`debug/timing_bins_board_100.xlsx`.

For the comparison the owner asked for, the LiteDRAM reference's read and
write paths from its AXI user port to the multiplexer's DFI command output
are drawn in the same style:
`projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/flows-litedram-uart/docs/graphviz/litedram_{rd,wr}_path.png`
(from the LiteX source; per-beat native commands, a 16-deep in-order
lookahead FIFO plus a one-deep head per bank, a five-state bank FSM with
one row register, two eight-way round-robins under global timers, and the
steerer's phase registers as the only flop between the bank FSMs and the
DFI).

### 3.3 The miss deliverable

`projects/components/mem-ctrl-ip/debug/` (gitignored) was cleared and
holds: `timing_bins_pumice_core_ooc_100.xlsx` (the OOC run of 3.1, sheets
cones / bins / raw), `timing_bins_board_100.xlsx` (the harness build of 3.2
at 100 MHz) and `rd_pick_path.png` /
`wr_pick_path.png` (+ `.dot`): the read and write command paths through the
storage records and `mc_bank_pick`, every register stage drawn, the failing
post-route cones in red with their WNS and endpoint counts.

## 4. Gates

| gate | result |
|---|---|
| contract bench, BANK_PICK (baseline, hold-on-gate-block: bank 1 fires while bank 0 is gated beyond the lookahead, bank 0 once within two cycles of the gate opening; zero-bubble, post-pop, override) + records fub test | 8 passed, 3 xfailed (the FRFCFS strict xfails), on the final text |
| pumice `perf_write_ceiling`, default geometry (t_ccd 4) / board geometry (one beat per burst) | 100.00% W utilisation, 0 backpressure / 99.61%, 1 stall (interim texts: 83.12% with 208 stalls; 50% at the board geometry) |
| pumice `perf_read_inflight` | R cadence 248 x 4 + 7 x 10, span 1 062 cycles -- identical to the Phase 2 text (interim: 1 082) |
| pumice `test_pumice_core_dfi.py`, all 16 cells, default geometry, on the final text | 16 passed |
| pumice `refresh_credit`, `refresh_collide`, `perf_write_ceiling`, `perf_paging_sweep`, `perf_read_inflight` at the board geometry, own build root | pass |
| pumice `make clean-all && make run-all-func-both` on the final text (board geometry in its own build root; its write-ceiling output reads 256 beats / 257 cycles, one beat per burst, so the models ARE the board geometry) | 216 passed / 1 skipped default geometry (244 s); 216 passed / 1 skipped board geometry (75 s, 107 fresh models) |
| granite `make clean-all && make run-all-func` (FRFCFS default, records wired, `wr_commit_ready_now` wired) | 6 passed, 1 xpassed (`top_geared[gate-8-12]`, non-strict xfail), as Phase 2 |
| lint -Wall on `mc_bank_pick`, `mc_wr_data_cam`, `mc_xddr2_entry_store`, `pumice_core`, `granite_core`, `scoria_core`, `andesite_core` | clean apart from the pre-existing `cal_busy_o` UNDRIVEN, SYNCASYNCNET on the reset trees, PINCONNECTEMPTY / UNUSEDSIGNAL in untouched modules, and the pre-existing `rd_ret_busy_o` PINMISSING in `mc_dfi_3p1_plane` / `mc_dfi_4p0_plane` |

## 5. Performance (pumice-CAM perf proxy, board geometry, 75 MHz, tREFI 585)

Programmed timings and floors as in the Phase 2 report §5 (col_major rd gap
6 -> 369.2 MB/s, wr gap 8 -> 319.9; streaming 599.9).

| run | Phase 2 text | Phase 3 final text |
|---|---|---|
| col_major, txn 256, wr / rd MB/s | 310.9 / 358.7 (txn 1024) | 310.0 / 355.6 (model violations: `tWR` 255, the Phase 0 §5 pre-existing note; no `tREFI` entry -- ISSUE-022 closed) |
| col_major command gaps (RD / WR / ACT) | 1 and 6 / 1 and 8 / 13-15 | 1 and 6 (253 rows) / 1 and 8 (248) / 13-15 |
| col_major, tRTP=1 (LiteDRAM profile), wr / rd | 311.3 / 387.6 (txn 1024) | 311.1 / 383.3 (txn 256; rd inter-row gap 5 on 252 of 256 rows, the floor; LiteDRAM in this harness 304 / 386) |
| 4 wr + 4 rd generators, txn 256: incremental / row_major / col_ilv / col_major wr, rd | 566.8, 535.4 / 570.4, 531.5 / 536.3, 533.9 / 461.2, 460.3 | 461.0, 458.3 / 458.7, 458.3 / 477.6, 485.5 / 458.8, 459.0 (mism 0; `tWR` 143, no `tREFI`; before the stale mask: 420.2, 436.8 / 417.4, 435.0 / 453.2, 464.7 / 417.3, 434.6) |
| one generator, txn 1024: col_major / col_ilv / row_major wr, rd | 310.9, 358.7 / 459.0, 457.3 / 577.7, 576.9 | 310.8, 359.2 / 460.0, 459.1 / 576.3, 578.2 (mism 0; `tWR` only, no `tREFI`) |

Before the stale-winner mask (the last change of the phase) the
many-requester families were below Phase 2: col_ilv 418 / 436 and the
four-generator streaming families 420 / 437, while single-bank, streaming
and the LiteDRAM profile were at parity. The loss predated the hold, the
sink and the grant changes (the first restructure step measured the same),
and raising `WR_DRAIN_AHEAD` to 3 (one more burst of drain slack, run once
as an experiment, text restored) left the four-generator numbers
bit-identical, so it was neither. The command-gap histogram on col_ilv
showed one 2-gap and one 3-gap per eight columns; `PERF_PICK_TRACE=1` on
the proxy (new) showed the mechanism in one screen: after a column the
class alternation prefers a row command, the only row request was the
stale request of the pair whose ACT was firing in that very cycle, so it
was re-picked and every row switch paid a bubble. Phase 2's stale-winner
mask had covered exactly that; it is back, from registers only, and
col_ilv measures 460.0 / 459.1 (Phase 2 459.0 / 457.3). With eight
generators the mask recovers col_major to parity (459 / 459) and lifts the
streaming families from 420 / 437 to 461 / 458, which is still 19% / 14%
below Phase 2's 567 / 535: a second many-requester mechanism remains
(section 6). A wider mask (keyed on "no same-row entry behind", held two
cycles) measured worse on both counts (col_major writes 291, eight
generators 446) and was dropped.

## 6. Left for later phases

- **Eight-generator streaming is 19% below Phase 2** (461 / 458 vs
  567 / 535) while every one-generator family, col_major with eight
  generators, and the LiteDRAM profile are at parity. Measured, not
  guessed: the same traced stream issues 521 ACTs per 4 096 columns on this
  text (7 529 per run of the four-generator proxy) (one row switch per eight columns, each generator's bank visit) and
  108 on the Phase 2 commit (one per 38); the busy window is 96% firing, so
  the loss is command slots, not bubbles. Not the hold (the loss predates
  it), not the write sink (`WR_DRAIN_AHEAD` 3 is bit-identical), not the
  stale re-pick (masked; the wider mask did not move it), and not the page
  policy's idle-timeout close (`TEST_PAGE_POLICY=1`, static open, gives
  bit-identical 461 / 459 with the same ACT count): the switches are demand
  misses, the per-bank oldest-first head alternating between generators'
  rows every eight columns, which the Phase 2 text somehow served in longer
  same-row runs. The one decode difference left is the record's hit (one
  cycle stale, classified at the storage edge) against Phase 2's live hit
  in the decode; the Phase 2 text can be traced with the proxy's new
  `PERF_PICK_TRACE` by adding the probe to its test file in a worktree.
  Tools: `PERF_PICK_TRACE=1 TEST_NUM_GEN=4 TEST_FAMILIES=incremental
  TEST_TXN=64` and the cycle classifier in this session's scratch.
- 100 MHz on the controller alone is 0.5 ns away on aclk with two endpoints
  in the arbiter (route-dominated) and 21 in the storage plane's snarf match
  -> read insert arc; the harness build cannot show it. A floorplanned
  (Pblock) implementation of the core, or registering the snarf hit one
  cycle (it already is "valid one cycle after the probe"; the read intake
  would wait a cycle on a hit), are the two remaining moves.
- The dfi_clk aligner -> CDC cone (-2.07 ns at 200 MHz, 362 endpoints) is
  the parked plan's Task 5 skid; untouched here.
- pumice ISSUE-022 is closed by the grant gate (section 2); the perf proxy's
  `tREFI` count on the final text is in section 5.
- The default `run-all-func-both` of any suite whose geometry is a parameter
  needs a build root per geometry; pumice has it now, the other areas that
  run two parameter sets in one directory should be checked the same way.
