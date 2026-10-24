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
| `PUMICE_SYS_75=1`, FR-FCFS, TASK-044 forward paths, pick-cycle hints read from the pick comb | `w_sys_i` 75 MHz | -2.212 | 96 / 86 378 (arg_sel + pick mux + fire cone chained into the classify cone; 18 levels, 15.7 ns, 80 % route) |
| `PUMICE_SYS_75=1`, FR-FCFS, TASK-044 final text (hints rebuilt from the pre-pick registers) | `w_sys_i` 75 MHz | +0.001 | 0 / 86 323 (LUTs 42 822, FFs 33 985; text md5 verified against the built sources) |

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

### 5.3 Area: LUT / FF / BRAM / DSP for the three controllers (owner's request, 2026-10-23)

Two views, because they answer different questions. "Standalone" is the
controller synthesized out of context on xc7a100t-1 through one flow
(synth, opt, place, phys_opt, route; `-flatten_hierarchy rebuilt`) at the
configuration the perf table was measured at: 16 entries, RD_RET_DEPTH 64,
32-bit beat, x16 device, BL4, 13 row bits, 8 banks, AXI id 8, sys 75 MHz /
dfi 150 MHz. "On the board" is the same block read out of the routed
Nexys A7 checkpoint, where Vivado has pruned everything the
characterization harness ties off. LiteDRAM is one flat LiteX module
(controller + a7ddrphy + VexRiscv BIOS + CSR); its controller-only line is
a partition of the routed board checkpoint by the generator's signal
prefixes (`main_litedramcore_*` plus the bankmachine / roundrobin /
multiplexer glue), raw cells, so it is an estimate. Recipes and reports:
`scratchpad/area/{pumice_board,granite_board,litedram_ooc,board_pumice_deep,board_litedram_cells}`.

| item | LiteDRAM | granite BANK_PICK | pumice FR-FCFS |
|---|---|---|---|
| standalone controller, LUT | ~1 200 (est.) | 22 471 | 19 982 |
| standalone controller, FF | ~1 000 (est.) | 6 621 | 7 864 |
| standalone controller, BRAM36 | 0 | 2 | 2 |
| standalone controller, DSP | 0 | 0 | 0 |
| standalone, 75 MHz WNS (aclk) | n/a (unconstrained) | +0.268, 0 / 13 091 | -29.603, 4 208 / 16 573 |
| standalone LiteX core incl. PHY + CPU + CSR, LUT / FF | 4 576 / 3 360 | - | - |
| standalone LiteX core, BRAM36 + BRAM18 / DSP | 13 + 9 (BIOS ROM 8, SRAM 2, CPU 1 + 8) / 4 | - | - |
| on the board, controller LUT | 2 435 (leaf = controller + PHY + CSR) | 8 340 (Oct 17, FR-FCFS core, not timing clean) | 8 235 |
| on the board, controller FF | 2 069 | 4 062 | 5 530 |
| on the board, controller BRAM36 | 12 (10 are BIOS ROM / SRAM) | 2 | 2 |
| on the board, controller DSP | 0 | 0 | 0 |
| on the board, CPU (VexRiscv) LUT / FF / BRAM / DSP | 1 924 / 1 279 / 1+8 / 4 | - | - |
| on the board, PHY LUT / FF | ~500 / 496 (inside the leaf) | 420 / 509 (a7ddrphy) | 421 / 509 (a7ddrphy) |
| on the board, controller + csr + DFI shims, LUT / FF | - | 8 870 / 5 871 | 9 158 / 7 383 |
| whole bitstream, LUT (% of 63 400) | 28 427 (44.8) | 35 359 (55.8, placed Oct 17) | 41 063 (64.8) |
| whole bitstream, FF | 24 826 | 29 053 | 33 753 |
| whole bitstream, BRAM36 tiles / DSP | 17.5 / 20 | 2 / 16 | 2 / 16 |
| generators per direction in that bitstream | 4 | 4 | 8 |

Standalone split, board geometry (LUT): granite = entry store 16 562 +
scheduler plane 3 040 (bank pick 745, bank timers 1 912) + AXI plane 1 436
+ DFI plane 430; pumice = scheduler plane 9 443 (arbiter 7 265, bank
timers 1 547) + storage plane 8 127 (wr CAM 4 574, rd CAM 3 554) + AXI
plane 1 501 + DFI plane 435. At the cores' default geometry (64-bit beat,
BL8, 8 entries, RD_RET 32, 75 MHz) they are 11 598 / 6 671 (granite,
+0.691) and 10 833 / 7 079 (pumice, -10.568); at 16 entries 23 614 /
7 938 and 20 075 / 9 113. Both window structures grow roughly with the
square of NUM_ENTRIES (granite's entry store 4.7k at 8, 16.6k at 16).

Three things the table says beyond the numbers. (1) Standalone, the
FR-FCFS arbiter does not close 75 MHz at 16 entries (-29.6 ns on a
7 265-LUT pick cone); it closes on the board (+0.013) only because the
harness constants let Vivado remove ~60 % of the core (19 982 to 8 235 on
identical parameters). BANK_PICK closes standalone at the same
configuration. (2) The pumice-vs-granite in-context numbers are within
2 % of each other in LUTs; FR-FCFS carries 36 % more flops. The granite
board figure is the Oct 17 FR-FCFS placed build (a peer's active area, no
BANK_PICK bitstream exists yet). (3) LiteDRAM's controller proper is about
one seventh of either; what it does not have is the window (CAMs / entry
store) and the runtime policy engine, which is where the 2x concurrent-load
advantage of section 5.1 comes from.

### 5.4 Why BANK_PICK still beats FR-FCFS at one thread (measured, 2026-10-23)

Section 5.2 is the multi-thread story (the page policy). The one-thread
gaps are the pick core itself. Both cores were traced on the same proxy,
one generator, txn 256, with every scheduler fire logged
(`PERF_CMD_TRACE=1`, histograms of fire-to-fire gaps per command kind;
`scratchpad/gaps/core{0,1}_{incremental,col_ilv,col_major}.json.gaps.json`).
Floors from the test's own JEDEC model at this point: a same-bank row
switch costs 6 cycles between reads and 8 between writes, i.e. 13 / 15
cycles per 8-column row on col_major.

| item | granite BANK_PICK | pumice FR-FCFS |
|---|---|---|
| col_major, ACT-to-ACT gap (cycles per 8-column row) | 13 / 15 (251 / 250 of 518) | 24 (490 of 518) |
| col_major, column gap at the row switch (rd / wr) | 6 / 8 = the floor | 17 / 17 |
| col_major, MB/s wr / rd | 310 / 356 | 194 / 194 |
| col_ilv, ACT-to-ACT gap | 9 / 10 / 11 (162 / 213 / 114) | 13 / 15 (248 / 248) |
| col_ilv, column gaps | 1 (1570) and 2 (472): a row command slips between columns | 1 (1791) then 6 / 8 (250): the stream stops for the row commands |
| col_ilv, MB/s wr / rd | 459 / 451 | 306 / 353 |
| incremental, gap at each row change | 2 | 6 / 8, PRE and ACT as separate transits (PRE-to-ACT 3) |
| incremental, MB/s wr / rd | 568 / 563 | 551 / 550 |

Reading. On col_major BANK_PICK sits exactly on the JEDEC floor: the last
column of a row carries auto-precharge (CLOSE_ON_DRAIN is exact: no
same-row entry behind it), the next-op hint lands the ACT and the first
column as soon as tRP / tRCD open, so a row costs 13 (reads) or 15
(writes) cycles. FR-FCFS pays 24: pumice carries CLOSE_ON_DRAIN=0
(BUG-027: the arbiter's AP term treats the youngest in-window column as
the last demand and chopped page-hit streams every NUM_ENTRIES bursts), so
every row close is an explicit PRE, and each dependent hop (column to
PRE, PRE to ACT, ACT to column) transits the three-stage pick pipeline
with no lookahead: 11 cycles over the floor per row, pattern-independent.
On col_ilv the banks are independent, and BANK_PICK's ACT/PRE-versus-column
alternation issues the next bank's row commands inside the current bank's
column run (gaps of 2 instead of 6 / 8), so a row costs 9 to 11 cycles;
FR-FCFS runs the columns, stops, does the row commands, resumes: 13 / 15,
the same bill it pays on col_major. Incremental is the same mechanism at
a 1-in-85 row-change rate, hence 3 %.

None of this is the page policy and none of it changes with tr_init. It is
the design difference the Phase 2 core was built to remove (its header:
"Without the hint every hop pays one cycle of pipeline latency (gap 9 vs
the floor of 6 on col_major reads)"). Two levers exist for FR-FCFS if the
research SKU is to keep that core: an exact close-on-drain predicate (the
one BANK_PICK uses, "no same-row entry behind this column", instead of
"youngest in window") so BUG-027 does not return, and a next-op hint /
lookahead decode in `mc_cmd_arbiter`. Filed as pumice TASK-044.

### 5.5 TASK-044: the FR-FCFS core on the JEDEC floor (2026-10-23)

Section 5.4 measured the gap; this is the fix. Three changes in the
arbiter, one in the page policy, one in the DV framework's DRAM model, and
pumice's close-on-drain default back on. Design note:
`vault/handbook/design/dependent-hops-forward-the-pick.md`.

**Arbiter (`mc_cmd_arbiter`).** (1) The close-on-drain predicate counts a
pending same-row entry (allocated, data not landed: the write CAM's
`sch_pend_o`, now exported by the storage plane as `wr_sch_pend_o`) as
demand, in the pre-pick last-column detect and the fire-stage sibling
re-check -- the predicate BUG-027 lacked. (2) Dependent hops classify
against the command being picked this cycle (`w_act_pick` / `w_pre_pick`),
the one in the output register, or the one fired last cycle, instead of
the two-cycle-stale bank image: a column is a hit behind its ACT, an ACT a
candidate behind its PRE (`r_pre_closing`, the demand twin of
`r_ap_closing`), and ACT candidates are guarded against ACTs only. (3) The
fire stage is the only JEDEC authority: a column fires only onto the LIVE
open row equal to its own (`w_col_row_ok`), and HOLDS, bounded, for tRCD
(when the lookahead says it is within reach); an ACT holds while its bank
is closed inside tRP / tRC or still draining an auto-precharge. A
speculation whose premise never fired is dropped there.

**Page policy (`mc_page_policy`).** The exact predicate still cannot see a
burst whose AW has not arrived; a just-in-time stream lost a row per burst
and six BUG-027 cells failed again (write ceiling: W channel stalled 98
cycles; read-in-flight 0.81 beats/cycle). The close is now ARMED PER BANK
(`drain_close_ok_o`): an ACT to a different row after a short-lived
previous row (at most `DRAIN_ARM_MAX_COLS` = 8 columns) arms it, an ACT
reopening the closed row disarms it, evidence is gathered only in the
fixed_open timer mode (a close-page mode leaves every row "short", and the
board-geometry paging sweep lost 17 % of its 8-bank window to one
auto-precharge per bank before that gate), and RDA / WRA count as
predicted closes for the BUG-030 mistake predictor.

**DRAM model (RDS-DV 92ec9bd).** `_pending_auto_pre` called `on_precharge`
at the column's own cycle and reported one phantom tRTP / tWR per RDA /
WRA; `on_auto_precharge` now records the device's internal close at the
earliest legal instant and times the next ACT's tRP against it. The
write-side `tWR` / `tRP` counts that remain are the uncalibrated
write-recovery anchor, pumice ISSUE-023 (256 per col_major run on BOTH
cores before this work; reads are clean).

**Hop by hop (col_major, one generator, cycles; floor = tRTP or tWR, tRP,
tRCD = 2 / 4, 2, 2):**

| hop | floor | before | exact close-on-drain | + forward paths | + pick-cycle classify (final) |
|---|---|---|---|---|---|
| last column to row close | 4 (wr) | 6 (PRE) | AP on the column | AP | AP |
| close to ACT | tRP 2 (6 after the last WR with AP) | 6 | 9 | 8 | 6 |
| ACT to first column | 2 | 5 | 5 | 3 | 2 |
| row period rd / wr | 13 / 15 | 24 / 24 | 19 / 21 | 16 / 18 | 13 / 15 |

**Same injectors and observers, pumice FR-FCFS, MB/s wr / rd, peak 600
(granite BANK_PICK from 5.1 for reference):**

| threads | family | pumice before (488a9654c) | pumice TASK-044 | granite BANK_PICK |
|---|---|---|---|---|
| 1 | incremental | 551 / 550 | 560 / 559 | 568 / 568 |
| 1 | row_major | 564 / 565 | 568 / 569 | 576 / 572 |
| 1 | col_interleave | 306 / 350 | 383 / 457 | 461 / 451 |
| 1 | col_major | 195 / 194 | 309 / 351 | 311 / 358 |
| 2 | incremental | 544 / 551 | 564 / 563 | 572 / 568 |
| 2 | row_major | 556 / 556 | 571 / 569 | 570 / 571 |
| 2 | col_interleave | 396 / 436 | 459 / 508 | 511 / 507 |
| 2 | col_major | 307 / 350 | 384 / 456 | 420 / 459 |
| 4 | incremental | 520 / 531 | 541 / 556 | 567 / 566 |
| 4 | row_major | 523 / 534 | 544 / 558 | 570 / 568 |
| 4 | col_interleave | 368 / 401 | 441 / 488 | 537 / 535 |
| 4 | col_major | 307 / 354 | 384 / 459 | 461 / 460 |
| 8 | incremental | 464 / 493 | 510 / 538 | 557 / 555 |
| 8 | row_major | 464 / 492 | 511 / 539 | 558 / 557 |
| 8 | col_interleave | 393 / 425 | 469 / 508 | 538 / 532 |
| 8 | col_major | 307 / 354 | 385 / 460 | 460 / 458 |

col_major at one thread is on the floor (13 / 15 cycles per row; the first
row per bank still closes by the timer while the predictor gathers
evidence). What is left against BANK_PICK: col_interleave writes (the
per-bank core slips the next bank's row commands inside the column run;
the arbiter's column-first class priority does not, and an alternation
would chop the write runs pumice's perf-shape cells pin), and the
multi-thread streaming residual (BUG-030's predictor re-learning after a
real conflict, improved from 464 to 510 at eight threads by the faster
hops, not closed).

**Gates on the final text:** pumice 217 / 217 at both geometries (the
close-drain probe no longer skips), the six BUG-027 cells and
`test_pumice_close_drain` at both geometries, granite 6 / 1 xfailed,
common-ip fub + macro 25 / 3 xfailed, formal `mc_cmd_arbiter` prove PASS,
Verilator clean on pumice / scoria / andesite (area lint) and granite
(elaborates, warning count unchanged at 200), RDS-DV `test_dfi_dram_state`
46 / 46. Board (3.2): the first build of the forward paths missed the 75 MHz
floor by 2.212 ns with the pick-cycle hints read from the pick comb; rebuilt
from the pre-pick registers the floor holds at +0.001, 0 / 86 323, on the
committed text (the thin positive margin is the design point).

### 5.6 TASK-045: bank preparation -- the FR-FCFS core matches the per-bank core on the streams (2026-10-23)

Owner, after 5.5: "Pumice is supposed to be the research uber performant
model ... every vendor and many research papers say FR-FCFS is highest
performing. So either our FR-FCFS design is broken or everyone is wrong",
and, on the first answer, "your reasoning on why per bank is better on the
existing traffic is flawed. In these cases FR-FCFS should match per bank."
Correct on both counts. What follows was measured on the isolated core
bench first (`dv/tests/top/test_pumice_core_bankprep.py`: pumice_core +
the JEDEC-timed DFI slave, AXI BFMs, one 8-column row per burst hopping
banks, every scheduler fire logged, 40 s a run, and a per-cycle arbiter
trace that lists the same-row siblings the fire stage sees), then on the
proxy. The bench is where the mechanisms were found; the proxy only sees
bandwidth.

**What was wrong, in command slots per 8-column row on the bank walk
(col_interleave, one thread, writes):**

| text | slots per row | ACT period | explicit PRE per row | read rows left open |
|---|---|---|---|---|
| TASK-044 (column-first) | 12: ACT, tRCD bubble, 8 columns, close, tRP bubble | 12 | 1 | -- |
| row_first (`access_pref` 2) | 9 | 9 | 0 | 52 of 128 (reads) |
| alternation, pre-pick held while a row class takes the slot | 9 wr / 11 rd | 9 / 11 | 0 / 115 | 115 of 128 |
| alternation + close decided at the fire stage (SHIPPED, `access_pref` 0) | 9 / 9 | 9 / 9 | 0 / 0 | 0 |
| column-first kept as `access_pref` 1 | 12 | 12 | 1 | -- |

Column-first is textbook FR-FCFS and free exactly when the command bus has
slack. At the board point (BL4 on x16, DFI 1:2, one command per cycle)
one column per cycle fills the data bus AND the command slot, tCCD is 1,
and every row command costs a column slot; column-first spent it after the
run, with tRCD in the open. The per-bank core's alternation spends it
inside the column's own dead time: after a column a ready row command (an
ACT to an idle bank, the demand PRE of a drained one), after a row command
columns, one class pending falls through. That is now the FR-FCFS default
class priority (`mc_cmd_arbiter`, `r_last_was_col`); it never takes a
column's ELIGIBLE slot, which is what row_first does (TASK-002's "one slot
in five"), and at tCCD >= 2 it measures the same as column-first because
the ACT already landed in the dead time. Column-first stays reachable as
encoding 1 and is now a row of the paging-sched cross gate.

**The trap it uncovered.** The close-on-drain candidate was the
age-youngest same-row column, the last one only while columns issue
strictly oldest-first. Once a row command can interpose, the column in the
pre-pick drops back to classify (its slot is masked as in flight, so the
STAGE-1b selection is already the next column) and re-issues behind its
younger sibling: the candidate fires with a sibling in the window (demoted,
correctly) and the true last column carries no flag -- 61 of 128 read rows
stayed open and were closed by a demand PRE two slots later. Holding the
pre-pick column made it worse (the refused 1b selection was masked all the
same: 115 rows). The fix is the fire stage owning the close: a column with
no same-(bank,row) entry anywhere in the live window, valid or pending,
either direction, on a bank the page policy has armed, closes
(`w_ap_last`; promote as well as demote; `cmd_op_o` follows). Handbook:
`vault/handbook/design/dependent-hops-forward-the-pick.md`.

**Also landed, measured inert on these shapes but kept as correct:** the
page policy's idle-timeout veto counts a write allocated at AW whose data
has not landed (`wr_sch_pend_i`) as demand for its row (`mc_scheduler_plane`
FR-FCFS branch); drain-close arms on a demand precharge followed by an ACT
to a different row as well as on a short row (`mc_page_policy`,
`!r_to_closed`): 305 fewer explicit PREs per eight-thread run, bandwidth
within 3 MB/s either way.

**Perf proxy, board geometry, 75 MHz, txn 256, blen 8, wr / rd MB/s (BANK_PICK = granite, 5.1):**

| threads | family | pumice TASK-044 | pumice TASK-045 | granite BANK_PICK |
|---|---|---|---|---|
| 1 | incremental | 560 / 559 | 564 / 559 | 568 / 568 |
| 1 | row_major | 568 / 569 | 568 / 568 | 576 / 572 |
| 1 | col_interleave | 383 / 457 | 458 / 501 | 461 / 451 |
| 1 | col_major | 309 / 351 | 309 / 351 | 311 / 358 |
| 8 | incremental | 510 / 538 | 539 / 560 | 557 / 555 |
| 8 | row_major | 511 / 539 | 539 / 561 | 558 / 557 |
| 8 | col_interleave | 469 / 508 | 516 / 537 | 538 / 532 |
| 8 | col_major | 385 / 460 | 459 / 507 | 460 / 458 |

Reads are at or above the per-bank core on every family and thread count
(col_major eight threads 507 vs 458). Writes match at one thread (within
1.4 percent) and trail by 3-4 percent at eight (539 vs 557, 516 vs 538).
The eight-thread write residual is NOT the arbiter: on the incremental
trace the FR-FCFS core issues 761 ACTs per 16 384 columns against the
per-bank core's 523, each paired with a precharge, where the address walk
needs one row per 2 048 columns -- the 2-cycle idle timer (`tr_init` 2,
tuned on one thread, 5.2 / section 6) closing banks whose generator has
nothing in the 16-entry window (eight generators, two bursts fit), and the
per-bank core merely presenting fewer free slots to the timeout branch.
Timer sweep at eight threads on this text: `tr_init` 8 is identical to 2 (539 / 560, 540 / 562, 516 / 538), `tr_init` 0 (timer
off) gives 555 / 560, 556 / 561, 524 / 540, 458 / 507 -- the streaming writes
land on the per-bank core's 557 / 558 and col_interleave closes to 524 vs
538. So the FR-FCFS core matches at eight threads too once the idle close
is not taking its free slots; what the default should be above one thread
is the policy question already filed in section 6.

**The family where the window matters (TASK-046, `mixed`):** generators
paired on a bank one row apart, each row_major inside its row, reads and
writes concurrent from one GO, read region pre-written so the data check
holds (`perf_mixed_family.py`, shared by both proxies). Same harness,
eight generators:

| core | total MB/s | wr / rd | mean latency wr / rd (cycles) | mismatched |
|---|---|---|---|---|
| FR-FCFS (TASK-045 text) | 311.3 | 155.6 / 155.7 | 112 / 190 | 0 |
| BANK_PICK | 81.9 | 41.0 / 41.0 | 687 / 423 | 0 |

The per-bank head record is the oldest schedulable entry of the bank and
the pair's bursts interleave in age, so it alternates the two rows on every
column (PRE + ACT per column, ~15 cycles a column); the FR-FCFS core picks
the oldest READY column across the window and a thread's eight same-row
columns leave together. 3.8x. So the ruling stands on evidence now: the
product core is the right one for streams and costs nothing there; the
research core is the one that earns its window.

**Gates on the final text:** pumice `make clean-all && make run-all-func-both`
218 / 218 at both geometries (the bench is the 218th), the TASK-002 cross
gate with column-first as its 11th scheduling row, the six BUG-027 cells
and `test_pumice_close_drain` at both geometries, granite 6 / 1 xfailed,
common-ip fub + macro 25 / 3 xfailed, formal `mc_cmd_arbiter` prove PASS
(from clean), Verilator clean on pumice / scoria / andesite area lint,
pumice CSR block regenerated (docs only changed). Board: the arbiter-only
text built to -0.156 ns on w_sys_i (15 endpoints: 7 on the arbiter's
r_rd_pop -> arg_sel -> r_bank path, 80 percent route, 8 on harness
rd_engine paths that were clean before), LUT 42 842 / FF 33 956 against
TASK-044's 42 822 / 33 985 (+0.001); the complete text -0.200 ns, 15 endpoints, bit-identical on a second build
(the flow is deterministic; LUT 42 833 / FF 34 000). An out-of-context run at
the board generics (same flow as 5.3) of the TASK-044 text and this text put
the arbiter's `r_rd_pop -> r_bank` path at 20 LUT levels / 3.40 ns logic
against 19 / 3.08 ns -- the new text did not deepen it; the loss was
placement of a cone at the knife edge. The cure is a shorter cone: the pick
comb's idle-timeout close branch now reads a guard built from the pre-pick
and output-register shadows only (`w_guarded_to`), not the STAGE-1b
selection of the same cycle (safe for that branch: an ACT is selected at 1b
for an open bank only while it is closing, which a timeout target is not;
a column or demand PRE for the named bank meets the closed row at its fire
stage and is rejected there); refresh and ZQ drain guards keep the full
vector. Every gate above re-run on that text with identical results (proxy
numbers bit-identical). Board on the shipped text: +0.019 ns on w_sys_i, 0 / 108 344 failing endpoints (0 / 86 406 on the 75 MHz
group), LUT 42 888 / FF 34 026, built text == committed text (md5 of the
pumice_core filelist, 0 mismatches). The thin positive margin is the design
point.

### 5.7 TASK-048: the idle timer above one thread (2026-10-23)

Owner: "Do 1." Timer on (`tr_init` 2, the 2026-09-27 reset) against timer
off (`tr_init` 0), FR-FCFS core, TASK-045 text, wr / rd MB/s:

| threads | incremental | row_major | col_interleave | col_major |
|---|---|---|---|---|
| 1, tr 2 / tr 0 | 564 / 559, 564 / 565 | 568 / 568, 574 / 562 | 458 / 501, 457 / 501 | 309 / 351, 309 / 348 |
| 2, tr 2 / tr 0 | 566 / 564, 569 / 568 | 571 / 569, 568 / 569 | 506 / 525, 498 / 524 | 458 / 504, 458 / 502 |
| 4, tr 2 / tr 0 | 557 / 566, 565 / 566 | 559 / 569, 567 / 568 | 495 / 522, 497 / 523 | 458 / 506, 457 / 505 |
| 8, tr 2 / tr 0 | 539 / 560, 555 / 560 | 539 / 561, 556 / 561 | 516 / 537, 524 / 540 | 459 / 507, 458 / 507 |
| 8, `mixed` total | 311 vs 319 with the knob written over APB; 311.3 again at the shipped reset path (the 8 is the concurrent start moving with the extra register write, not the timer) | | | |

Never more than 8 MB/s worse in a cell, up to 17 better at eight threads,
a tie at one; `tr_init` 8 is identical to 2 at eight threads, so the
timer's length is not the variable, its existence is. The September board
result that introduced it (+41 percent col_interleave at one thread) was
measured before close-on-drain existed; the armed auto-precharge now does
that job. Shipped: `tr_init` resets to 0 under `policy_mode` 3 (which keeps
the drain-close arming, so this is open page plus the armed close, not open
page). The proxy at the reset defaults, the pumice regression at both
geometries and the board build on that text: proxy at the reset path (no CSR write) one thread 564 / 559, 568 / 568,
457 / 501, 309 / 351 and eight threads 554 / 561, 556 / 562, 524 / 540,
458 / 507 (mismatched 0 everywhere); pumice `make clean-all && make
run-all-func-both` 218 / 218 at both geometries; pumice area lint clean;
board 75 MHz +0.019 ns, 0 / 108 344 endpoints, LUT 42 888 / FF 34 026 (a
reset constant moves no logic), built text == committed text.

### 5.8 TASK-049: the injectors learn the window families (2026-10-23)

Owner: "Can the injectors be updated to create those?" The address generator
under both injectors was always two-dimensional; the injectors fed the
transaction counter to one dimension and held the other at zero. Two fields
in `AXI_ATTR` now shape the index first: `idx1_shift` splits it between the
two dimensions (one thread can alternate rows inside a bank), `addr_lfsr`
replaces the counter with a 16-bit LFSR (a pseudo-random walk inside the wrap
region; the paths step their own copies in lockstep, a reader with the
writer's seed reads the writer's sequence, repeats validate under the
address-hash data mode). Framework doc:
`projects/fpga-systems/rtl/mem_char_framework/docs/address_modes.md`.

| family | threads | FR-FCFS (TASK-048 text) | BANK_PICK | mean latency wr / rd (cycles) |
|---|---|---|---|---|
| `row_thrash` (one bank, two rows, a 2-beat burst to each in turn) | 1 | 269.4 / 302.9 | 128.7 / 142.9 | 49 / 65 vs 95 / 95 |
| `row_thrash` | 8 | 285.5 / 286.1 | 283.0 / 280.5 | 49 / 51 vs 51 / 51 |
| `random` (LFSR over two rows by eight banks per thread, 8-beat bursts) | 1 | 460.1 / 490.8 | 471.1 / 484.3 | 51 / 50 vs 51 / 50 |
| `random` | 8 | 430.6 / 479.3 | 406.3 / 444.0 | 54 / 55 vs 53 / 56 |

Mismatched 0 in every cell. `row_thrash` at one thread is the textbook case:
eight 2-beat bursts in the 16-entry window, the window serves the four A
hits then the four B hits (two activates per eight bursts), the per-bank head
record alternates rows (eight), 2.1x. At eight threads a bank holds at most
two of its own bursts in the window and the cores meet. `random` ties at one
thread and gives the window 6-8 percent at eight. Together with `mixed` (5.6,
3.8x) these are the shapes that justify the research core; the streams (5.5)
are where it had to stop losing.

The read engine's error-bit popcount (`$countones` of a 64-bit XOR) is now
registered in two stages: the eight-injector board build (TASK-043, the
harness at 85 percent of the part) had it as the worst path, -0.442 ns with
59 of 89 failing endpoints in the read engines (20 in the arbiter, congestion).
Default build (four injectors) on the new text: first -0.118 ns on the
arbiter's `r_wr_pop -> column select -> timeout-PRE guard -> r_bank` path
(the guard still carried the STAGE-1b column shadow through
`w_col_inflight_guard`; dropped, the guard is registered shadows only), then
+0.014 ns, 0 / 112 789 endpoints, LUT 44 887 / FF 35 593 (+2 000 LUT for
the address LFSRs and index shaping). Gates: val/amba injector tests (the 7
`fill_mismatch_err_bits` cells caught the two-stage accumulate landing one
cycle after done; done settles two cycles now) 159 / 159 on the corrected
read-injector and pair files, mem_char_framework dv 17 / 17, framework
functional suite 222 / 2 xfailed (a loaded-machine run failed 10 cells that
pass 10 / 10 alone: ISSUE-024, the engine wait is wall-clock), pumice 218 /
218 both geometries, granite 6 / 1 xfailed, common-ip 25 / 3 xfailed, formal
PASS, lints clean.
Eight-injector build on the new text: -0.212 ns, 36 failing endpoints (19 arbiter, 17 read engine 4), LUT 57 642 / FF 46 059 -- 91 percent of the xc7a100t; the popcount cone is gone from the list and what fails now is congestion. Eight injectors do not close 75 MHz on this part; the shipped harness default goes back to four (`CHAR_NUM_GEN` build knob for eight).

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
  same night: pumice BUG-030, section 5.2. The default itself (`tr_init` 2,
  tuned on one thread) is RESOLVED in 5.7 / TASK-048: it resets to 0.
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
