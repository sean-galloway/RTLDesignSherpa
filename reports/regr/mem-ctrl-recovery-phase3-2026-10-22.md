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
| **Follow-up (same day, after the phase commit 5fc49292c):** the stale mask covers BOTH cycles the request register describes a fired entry. Cycle N (the fire) as above; cycle N+1 by a fourth registered source loaded from the column fire itself, keyed on the fired record's `behind_empty` (the same column-fire term the pop shadow loads from; the request register at N+1 was decoded from the record in the fire cycle, which still shows the entry) | with four generators per direction a column that emptied its pair was re-picked the cycle after it fired, failed its class at the fire stage, and the page policy's idle-timeout close (`tr_init` 2) took that free slot and closed another generator's open row: 187 closes in a 2 063-cycle trace, every one exactly two cycles after a column fire of the stale winner's pair; 199 ACTs against Phase 2's 21 in the same window. Phase 2 had the same timeout request asserted (1 926 of 2 063 cycles) and never served it, because its slot-compared shadow left no free slot. Keyed on `behind_empty` the mask is free (an empty pair has nothing to pick); keyed on "another row behind" and held two cycles it had cost the write PRE a cycle | `mc_bank_pick.sv` |
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
-2.998 (404 / 2 763).

The follow-up text (second-cycle mask, section 2), same flow: aclk -0.777,
758 / 16 379 (synthesis -0.675 / 17): bank timer -> bank timer 435 at
-0.777, write CAM snarf -> read CAM 276 at -0.63, the pick core 13 at
-0.758 (hold bit -> arbiter root -> one-hot carry chain -> stale-mask
register, 2.8 ns logic / 7.8 ns route, 14 levels -- the same cone as the
-0.61 above, placed worse), bank timers -> decode 10 at -0.34; dfi_clk
-2.303, 526 / 2 767 (aligner -> CDC, unchanged). The two large cones are
untouched modules swinging with placement; the mask's fourth source is one
more input to the register mux at the arbiter's root (a single LUT6) and
adds no level. The aclk cones are route-dominated (2-3 ns of logic
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
| `PUMICE_SYS_75=1`, BANK_PICK, follow-up text (second-cycle mask) | `w_sys_i` 75 MHz | +0.021 | 0 / 77 114 (hold +0.022, 0 failing) |
| `PUMICE_SYS_75=1`, pumice on its new FR-FCFS default (owner's core assignment, same text otherwise) | `w_sys_i` 75 MHz | +0.068 | 0 / 85 665 (the research core is the larger one; the floor holds on both) |
| `PUMICE_SYS_75=1`, pumice FR-FCFS, BUG-030 text (predictor, fire-side feed, explicit timeout flag, REGISTERED demand veto) | `w_sys_i` 75 MHz | +0.013 | 0 / 85 908 (the first build of the fix, with the veto live: -0.277, 15 / 86 116, the arbiter's pick cone) |
| `PUMICE_SYS_100=1`, BANK_PICK, follow-up text | `w_sys_i` 100 MHz | -2.716 | 2 553 / 77 114 (phase commit: -2.574, 3 463; hotspots read CAM 440, harness write engines 266 + 106 + 89 and W skid 252, read intake AR 133, the pick core 124, hist_rd 117 -- harness-dominated as before) |
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
| follow-up text (second-cycle mask): contract bench + records fub | 8 passed, 3 xfailed |
| follow-up text: pumice `perf_write_ceiling`, `perf_read_inflight`, `refresh_credit`, `core_close*`, `core_waw`, `core_b2b`, default geometry, fresh build dirs | 6 passed; write ceiling 100.00% / 0 stalls (default geometry), 99.61% / 1 stall (board geometry, own build root); read in-flight 256 bursts, span 1 062 cycles, R cadence 248 x 4 + 7 x 10 -- all identical to the phase commit |
| follow-up text: granite `make clean-all && make run-all-func` | 6 passed, 1 xpassed |
| follow-up text: pumice `make clean-all && make run-all-func-both` | 216 passed / 1 skipped default geometry (238 s); 216 passed / 1 skipped board geometry, own build root (221 s fresh build, 69 s on the re-run the Makefile chains) |
| lint -Wall on `mc_bank_pick`, `mc_wr_data_cam`, `mc_xddr2_entry_store`, `pumice_core`, `granite_core`, `scoria_core`, `andesite_core` | clean apart from the pre-existing `cal_busy_o` UNDRIVEN, SYNCASYNCNET on the reset trees, PINCONNECTEMPTY / UNUSEDSIGNAL in untouched modules, and the pre-existing `rd_ret_busy_o` PINMISSING in `mc_dfi_3p1_plane` / `mc_dfi_4p0_plane` |

## 5. Performance (pumice-CAM perf proxy, board geometry, 75 MHz, tREFI 585)

Programmed timings and floors as in the Phase 2 report §5 (col_major rd gap
6 -> 369.2 MB/s, wr gap 8 -> 319.9; streaming 599.9).

| run | Phase 2 text | Phase 3 final text |
|---|---|---|
| col_major, txn 256, wr / rd MB/s | 310.9 / 358.7 (txn 1024) | 310.0 / 355.6 (model violations: `tWR` 255, the Phase 0 §5 pre-existing note; no `tREFI` entry -- ISSUE-022 closed); follow-up text 310.0 / 355.6, identical (`tWR` 259; incremental, one generator, txn 256: 568.2 / 563.0) |
| col_major command gaps (RD / WR / ACT) | 1 and 6 / 1 and 8 / 13-15 | 1 and 6 (253 rows) / 1 and 8 (248) / 13-15 |
| col_major, tRTP=1 (LiteDRAM profile), wr / rd | 311.3 / 387.6 (txn 1024) | 311.1 / 383.3 (txn 256; rd inter-row gap 5 on 252 of 256 rows, the floor; LiteDRAM in this harness 304 / 386); follow-up text 311.1 / 383.3, identical |
| 4 wr + 4 rd generators, txn 256: incremental / row_major / col_ilv / col_major wr, rd | 566.8, 535.4 / 570.4, 531.5 / 536.3, 533.9 / 461.2, 460.3 | **follow-up text: 567.4, 568.4 / 568.4, 569.2 / 536.0, 534.1 / 461.0, 460.1** (mism 0; `tWR` 96, no `tREFI`; ACT 2 956 per run against 7 529). Phase commit: 461.0, 458.3 / 458.7, 458.3 / 477.6, 485.5 / 458.8, 459.0 (`tWR` 143; before the cycle-N mask: 420.2, 436.8 / 417.4, 435.0 / 453.2, 464.7 / 417.3, 434.6) |
| one generator, txn 1024: col_major / col_ilv / row_major wr, rd | 310.9, 358.7 / 459.0, 457.3 / 577.7, 576.9 | 310.8, 359.2 / 460.0, 459.1 / 576.3, 578.2 (mism 0; `tWR` only, no `tREFI`); follow-up text 310.8, 359.2 / 458.5, 457.6 / 576.3, 578.2 (col_major and row_major bit-identical; col_ilv 35 cycles in 10.7k) |
| **granite** (FRFCFS default, records + `wr_commit_ready_now` wired; `test_granite_char_perf.py`), txn 256: incremental / row_major / col_ilv / col_major wr, rd | 2026-10-20 baseline, txn 1024 (`reports/regr/pumice-100mhz-baseline-2026-10-20.md`): 556.1, 558.7 / 570.1, 568.7 / 307.2, 353.1 / 221.0, 245.2 | follow-up text, txn 256: 551.4, 556.4 / 570.9, 565.4 / 307.9, 350.4 / 221.4, 244.5 (mism 0); txn 1024: 556.1, 558.7 / 570.1, 568.7 / 307.2, 353.1 / 221.0, 245.2 -- bit-identical to the baseline. Granite's pick core is still FRFCFS, so the Phase 2 / 3 col_major gain is pumice-only until Phase 4 flips `SCHED_CORE` |

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
streaming families from 420 / 437 to 461 / 458, which was still 19% / 14%
below Phase 2's 567 / 535 at the phase commit. A wider mask (keyed on "no
same-row entry behind", held two cycles) measured worse on both counts
(col_major writes 291, eight generators 446) and was dropped.

**Follow-up, same day.** The owner's ruling after the phase report (100 MHz
is a future goal; each injector must run eight threads at once) made the
eight-generator loss the first item. Tracing the Phase 2 commit (in a
worktree, with the proxy's `PERF_PICK_TRACE` probe ported into its test
file) beside the phase text, both with the page policy's timeout fields in
the probe: the two cores have the same ~80 free slots per 2 063 cycles and
the same idle-timeout request asserted almost always (Phase 2: 1 926
cycles, with a pre-ready bank for 806 of them), yet Phase 2 fires 0 timeout
PREs and 21 ACTs where the phase text fires 187 and 199. Every one of the
187 sits exactly two cycles after a column fire of the pair the stale
winner names, with that pair's request gone (`req` bit 0, class mismatch,
`cls_ok=0`): the request register describes a fired entry for TWO cycles
(decoded from the record one cycle before the pick, and again from the
record in the fire cycle, which still shows the entry while the pop shadow
re-aims only the candidate), the cycle-N mask covered the first, and the
re-pick at N+1 reached the fire stage with an empty candidate. That free
slot satisfied `w_to_pre`, which closed the lowest expired open row -- a
different generator's -- and the next access to it paid PRE + ACT + tRCD.
The timeout PRE itself fires by design (fixed_open, `tr_init` 2); the slot
was the bug. The second-cycle mask (section 2) removes it: 567.4 / 568.4
streaming, 568.4 / 569.2 row_major, 536.0 / 534.1 col_ilv, 461.0 / 460.1
col_major with four generators per direction -- at Phase 2 on writes and
above it on reads (Phase 2's reads were 535 / 532), ACTs per run 7 529 ->
2 956 (the remaining ones are col_major's row walks). The one-generator
table is unchanged to the cycle on col_major and row_major and within 35
cycles on col_ilv. The harness caps `NUM_GEN` at 4 per direction (the GO
register's start bits): pumice TASK-043 carries the eight-injector point;
`NUM_GEN` is plumbed through the sim top, the harness and the proxy
(`"NUM_GEN": max(4, TEST_NUM_GEN)`) so `TEST_NUM_GEN=8` reaches the
engine block the day the register widens.

### 5.1 Controller x family x threads (owner's request, 2026-10-22)

**Core assignment (owner, the same evening): granite, the product, carries
the BANK_PICK core; pumice, the research controller, carries FR-FCFS.** The
defaults flipped in `granite_core` / `pumice_core` and every pumice harness,
sim top and proxy default followed; both cores stay selectable through
`SCHED_CORE`. The table's main columns are the shipping defaults ON THE
BUG-030 TEXT (section 5.2); the fourth column is pumice FR-FCFS as it
measured before BUG-030's fix, and the fifth the BANK_PICK cross-control on
pumice (same day, before the flip), kept because they show the result
follows the CORE, not the backend.

All three controllers through the SAME injectors, observers and host
program, in simulation: pumice and granite on their char-harness sim tops,
LiteDRAM on `litedram_char_uart_tb_top` (the A/B flow's `char_engine_harness`
driving LiteX's `litedram_core_sim`: LiteDRAMCore + SDRAMPHYModel + VexRiscv
BIOS; new this day, `test_litedram_char_perf.py`). Threads = generators per
direction, one bank apart, write phase then read phase, AXI burst 8 beats of
64 bits, txn 256 per generator, 75 MHz, board geometry (BL4 x16), peak 600
MB/s; LiteDRAM as `litedram_hp.yml` (cmd_buffer_depth 16, ROW_BANK_COL,
auto-precharge lookahead). Every cell is integrity-clean (0 mismatched
beats, both engines completed). The LiteDRAM one-thread column sits within
1-2% of its 2026-09-10 board matrix at the same operating point (554 / 557
vs 554 / 564 incremental, 302 / 382 vs 304 / 386 col_major), the sim
proxy's calibration against silicon.

Eight per direction needed the harness widened (pumice TASK-043, sim side):
`chargen_regs.rdl` WR_GEN / RD_GEN arrays 4 -> 8 (the global block moved
0x400 -> 0x600; hosts address by name), GO gained wr_go4..7 / rd_go4..7,
`char_engine_block` gathers eight, the granite harness / sim top / perf
proxy carry `NUM_GEN`. The LiteDRAM sim core must be regenerated with its
BIOS (`flows-litedram-uart/regen.sh --bios`; three LiteX-venv patches,
recorded in that flow's tooling notes).
**1 thread per direction**

| family | LiteDRAM | granite (BANK_PICK) | pumice (FR-FCFS) | pumice FR-FCFS before BUG-030 | control: pumice BANK_PICK |
|---|---|---|---|---|---|
| incremental | 554 / 557 | 568 / 568 | 551 / 550 | 551 / 550 | 568 / 563 |
| row_major | 560 / 571 | 576 / 572 | 564 / 565 | 564 / 565 | 571 / 572 |
| col_ilv | 275 / 280 | 461 / 451 | 306 / 350 | 308 / 350 | 458 / 455 |
| col_major | 302 / 382 | 311 / 358 | 195 / 194 | 195 / 194 | 310 / 357 |

**2 threads per direction**

| family | LiteDRAM | granite (BANK_PICK) | pumice (FR-FCFS) | pumice FR-FCFS before BUG-030 | control: pumice BANK_PICK |
|---|---|---|---|---|---|
| incremental | 408 / 416 | 572 / 566 | 544 / 551 | 556 / 558 | 572 / 566 |
| row_major | 409 / 416 | 570 / 569 | 556 / 556 | 565 / 565 | 574 / 571 |
| col_ilv | 376 / 380 | 511 / 507 | 396 / 436 | 398 / 436 | 508 / 506 |
| col_major | 269 / 274 | 420 / 459 | 307 / 350 | 266 / 289 | 420 / 459 |

**4 threads per direction**

| family | LiteDRAM | granite (BANK_PICK) | pumice (FR-FCFS) | pumice FR-FCFS before BUG-030 | control: pumice BANK_PICK |
|---|---|---|---|---|---|
| incremental | 402 / 410 | 567 / 566 | 520 / 531 | 306 / 353 | 567 / 568 |
| row_major | 403 / 411 | 570 / 568 | 523 / 534 | 307 / 353 | 568 / 569 |
| col_ilv | 366 / 373 | 529 / 536 | 368 / 401 | 307 / 353 | 536 / 534 |
| col_major | 271 / 277 | 461 / 460 | 307 / 354 | 307 / 353 | 461 / 460 |

**8 threads per direction**

| family | LiteDRAM | granite (BANK_PICK) | pumice (FR-FCFS) | pumice FR-FCFS before BUG-030 | control: pumice BANK_PICK |
|---|---|---|---|---|---|
| incremental | 391 / 399 | 557 / 555 | 464 / 493 | 307 / 354 | 557 / 556 |
| row_major | 392 / 400 | 558 / 557 | 464 / 492 | 307 / 354 | 558 / 557 |
| col_ilv | 375 / 381 | 534 / 526 | 393 / 425 | 307 / 354 | 538 / 529 |
| col_major | 277 / 280 | 459 / 458 | 307 / 354 | 307 / 354 | 459 / 458 |

Reading it: the BANK_PICK core (granite) holds 93-95% of peak on the
streaming families at every thread count and climbs with threads on the
bank-interleaving families (col_ilv 461 -> 534, col_major 311 -> 459: more
banks in flight hide the row walks); its 8-thread streaming cells sit 10
MB/s under the 4-thread ones (not the page policy: unchanged with the timer
off). The FR-FCFS core (pumice) matches it on streaming at one and two
threads, holds 520 / 531 at four and 464 / 493 at eight on the fixed policy
(it read 307 / 354 at both before BUG-030; the gap to the 554 / 553
timer-off ceiling is the mistake predictor's re-learning after each real
conflict clears a bank's mark, section 5.2); its single-thread col_major is
the 195 / 194 of the Phase 0 baseline (inter-row gap 17 against the JEDEC
floor of 6 / 8). LiteDRAM matches both on streaming at one thread and falls
to ~400 / 410 from two threads up (per-bank round-robin paying turnaround
and bank switches per request); its col_major is flat ~270-300 and its
col_ilv ~375. Gates on the shipping text: pumice `run-all-func-both` 216
passed / 1 skipped at both geometries; granite `run-all-func` 6 passed /
1 xfailed (the `top_geared[gate-8-12]` cell, whose DFI loopback model is
order-coupled to the FR-FCFS interleave: it xpassed on FR-FCFS and fails as
its marker says on a per-bank core; the board bench is its real check);
common-ip contract bench 8 passed / 3 xfailed.

### 5.2 Why FR-FCFS collapsed from four threads up (pumice BUG-030)

The first §5.1 table showed FR-FCFS at a pattern-independent 307 / 354 from
four threads per direction, two threads still at 556 / 558. A flat number
across incremental, row_major, col_ilv and col_major cannot be DRAM timing,
so it was traced rather than explained.

| evidence (FR-FCFS, row_major, txn 256) | 2 threads | 4 threads |
|---|---|---|
| wr / rd MB/s | 561.6 / 561.2 | 306.5 / 353.0 |
| ACTs (write + read phase) | 36 | 2 099 for 16 384 columns: one per 8-column burst |
| ACT cadence | - | 15 cycles (the single-bank row-walk floor) |
| page stats (write phase) | miss 17, empty 1, hits 4 078 / 4 096 | miss 1 049, empty 3, hits 7 154 / 8 192 |
| DFI trace | - | every bank on row 0 throughout; each PRE in the slot between two bursts, 16 cycles after that bank's last column; the next ACT reopens row 0 |
| same run, `PAGE_TIMEOUT_CFG.tr_init = 0` | - | **554.2 / 553.3, 128 ACTs** (refresh reopenings) |

The closer is the page policy's fixed_open idle timer (`mc_page_policy`,
common-ip): reset policy_mode 3 / tr_init 2, "the measured optimum" of
2026-09-26 on single-thread row walks. It expires a bank whose row has seen
no COMMAND for tr_init cycles, with no view of the window, and the arbiter
serves the PRE as its lowest-priority pick, in any free slot. Four threads
one bank apart leave every bank idle for three bursts between visits, so
every bank is expired almost always and the first free slot closes a row
whose next burst is already queued; the ACT round trips create more free
slots. BANK_PICK hid it by leaving no free slot while streaming (the
four-generator loss fixed earlier today was this same policy taking the
stale-pick slot); two FR-FCFS threads happen to fill every slot.

Two instruments lied on the way. The perf proxy's `TEST_PAGE_POLICY` writes
the legacy `REFRESH_TUNING.page_policy_or`, not `PAGE_POLICY_CFG.policy_mode`,
so the "static_open was bit-identical" statements earlier in this report
(section 6 as first written, and this section's own first pass) never
turned the timeout off; `TEST_PAGE_MODE` and `TEST_TR_INIT` now reach the
engine. And the page stats classified these closes as conflict misses
(`w_pre_was_timeout` read `r_expired` after the row image had already cleared
it), which pointed the investigation at the row-hit logic for an hour.

Fix (BUG-030): the scheduler plane computes a per-bank "a queued column
wants this bank's open row" from whichever storage view the core consumes
(the records' head hit on BANK_PICK; a compare of the flat vectors against
the registered row image on FR-FCFS); `mc_page_policy` treats it as activity
(re-warms the idle timer) and as a live veto on the close request. The
telemetry keeps a two-cycle shadow of the expired flags so a timeout close
classifies as one. **The veto alone does not move the matrix**: re-run with
it in place, both cores are bit-for-bit the pre-veto table (FR-FCFS 306 /
353 at four threads). With four or more generators in a 16-entry window a
bank's next burst is usually not admitted yet when its last column fires,
so the policy sees no queued demand and the 2-cycle timer wins; the veto
stays as the correct, free guard for the case where demand is visible, and
the lever is the timer value (BUG-030 carries the tr_init sweep: 32
restores four-thread streaming to 554 / 557 and keeps the one-thread
col_ilv benefit at 306 / 349; 128 keeps streaming and loses col_ilv to
247 / 261; and at eight threads 32 and 64 both still thrash, 307 / 352,
because the eight-bank revisit interval is ~70 cycles -- no single value
serves every thread count). So the policy also gained a per-bank MISTAKE
PREDICTOR: a timeout close whose row the next ACT to that bank reopens marks
the bank keep-open until a conflict precharge clears it; a stream pays one
reopen per bank, a row walk never trips it. The predictor was inert until a
third defect fell: the policy consumed the plane's command-FIFO READ side
while the bank image updates at the cores' FIRE into that FIFO, so every
command reached it late, the expired flag was already cleared (the
telemetry mislabel above, beyond any shadow's reach), the timer re-warmed
late and the predictor never armed. Fed from the fire side and classified on
the cores' own flag (next paragraph), FR-FCFS reads 520 / 531 incremental
and 523 / 534 row_major at four threads (307 / 353 before; ceiling with the
timer off 554 / 553), 464 / 493 at eight (307 / 354 before), 368 / 401
col_ilv at four; one thread keeps col_ilv at 306 / 350 and col_major at
195 / 194; the page stats call the closes timeouts. The residual against
the ceiling is the predictor re-learning a bank after each real conflict
clears its mark, largest at eight threads; a two-state mark or a larger
tr_init default would narrow it and is left as the owner's tuning call. One more: in the full-family run col_ilv read
254 / 298 after the streaming families, because the policy inferred
"timeout close" from its own expired flag, which is also true for a demand
conflict on an idle bank, so the keep-open marks left by the stream were
never cleared. The cores now export which branch fired
(`cmd_timeout_pre_o`) and the policy classifies on that. The first board
build of all this missed the 75 MHz floor (-0.277 ns, 15 endpoints, the
FR-FCFS arbiter's pick cone): the policy's request had grown live terms
that feed the arbiter's timeout branch; the demand vector is registered in
the plane now, and the build on that text is in section 3.2. The reset
default stays tr_init 2 in this commit: at one thread the
early close is worth 308 / 350 against 238 / 260 on col_ilv on FR-FCFS and
458 / 455 against 423 / 456 on BANK_PICK (bank-interleaved row walks, where
the next access to a bank is a different row and the veto does not apply)
and nothing on col_major on either core; whether the default is right is
the owner's call, the veto makes it safe under streaming either way. The
new `TEST_PAGE_MODE` knob is verified against the engine: four-thread
FR-FCFS under policy_mode 1 (static_open) with the veto in place reads
543 / 547 with 37 ACTs at txn 64. The
8-thread BANK_PICK streaming cells (557 vs 567 at four) are NOT this policy:
unchanged at tr_init 0.

## 6. Left for later phases

- **Eight injectors per direction** (owner's load point, pumice TASK-043):
  the harness GO register has four start bits per direction; widen it
  (`chargen_regs.rdl`, regenerate through `bin/peakrdl_generate.py -o`),
  lift the `char_engine_block` check, the host's GO / config loops, then
  `TEST_NUM_GEN=8` on the proxy and the board, with LiteDRAM's number at
  eight in the same harness. The four-generator loss that stood here at the
  phase commit is fixed (section 5, follow-up); with eight the thing to
  watch is the same signature: `PERF_PICK_TRACE` cycles with `fire=1
  topre=1 cls_ok=0`, i.e. a free slot handed to the idle-timeout close.
- **The idle-timeout close under streaming load** was found and fixed the
  same night: pumice BUG-030, section 5.2. What remains is the default
  itself (`tr_init` 2 was tuned on one thread) -- a policy question for the
  paging modes, with the one-thread numbers in 5.2 as the trade.
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
