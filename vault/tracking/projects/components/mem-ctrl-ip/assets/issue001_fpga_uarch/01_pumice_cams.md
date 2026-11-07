# pumice storage plane - FPGA microarchitecture review (read-only)

Scope: `projects/components/mem-ctrl-ip/common-ip/rtl/{macro/mc_storage_plane.sv, fub/mc_wr_data_cam.sv, fub/mc_rd_cmd_cam.sv, fub/mc_bank_head_records.sv}`. No repo file was modified. All paths below are relative to `/mnt/data/github/RTLDesignSherpa/`.

## Board parameterization used for every size/cost below

| Param | Value | Where set |
|---|---|---|
| NUM_ENTRIES = N_SRAM_SLOTS | **8** | `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/build-perf/rtl/ddr2_char_harness.sv:739` (`WR_CAM_DEPTH(8)`) -> `ddr2_char_framework/rtl/ddr2_char_macro.sv:535-536` -> `pumice_core.sv:57-58` |
| AXI_ID_WIDTH | 8 | `ddr2_char_harness.sv:63` |
| RD_RET_DEPTH (ticket width TW) | 64 (6 b) | `build-perf/rtl/ddr2_char_top.sv:315` |
| NUM_BANKS / ROW_WIDTH / COL_WIDTH | 8 / 13 / 10 (key = 26 b, +8 b id = 34 b) | `ddr2_char_harness.sv:71`, `ddr2_char_macro.sv:85-86` |
| AXI_DATA_WIDTH (DW) | 64 | `ddr2_char_top.sv:239` |
| AXI_BEATS_PER_BURST | **1** (BL4 x16, 32-bit beat, DFI 1:2 -> BURST_WORDS=1, `pumice_core.sv:103-120`) | `ddr2_char_top.sv:240-253` |
| AGE_WIDTH | 16 | `pumice_core.sv:87` |
| WR_MERGE_EN / RD_MERGE_EN | **1 / 1** - `pumice_top.sv:323-354` and `pumice_top_geared.sv` do not pass them, so `pumice_core.sv:72-73` defaults apply | |
| SCHED_CORE | 0 = FR-FCFS (`mc_cmd_arbiter`) | `ddr2_char_top.sv:351` |

## Measured, not estimated

### Board timing reports (`build-perf/fpga/`)
- `reports/` (Oct 27 04:14, **pre-merge**: zero `r_mgid/r_mgfill/stat_merge` names in its path report): 75 MHz **closes, WNS +0.029 ns**, 47,365 LUT.
- `reports_sys75_2026-10-27/` (Oct 27 16:55, **merge-era**: 6,253 mentions of those names): **WNS -5.630 ns, 4,221 failing endpoints**. `timing_failing_hotspots.txt:3-5`: `u_store_plane/u_wr_cam` **974** failing endpoints (rank 1 of the whole chip), `u_axi_plane/u_rd_ring` 787, `u_store_plane/u_rd_cam` **461** (rank 3). The two CAMs own 34% of all failures.
- Source attribution from `timing_failing_setup_full.txt`: **1,105 of the 1,120 wr_cam paths start at `u_sched_plane/u_bank_timers`** flops; **all 461 rd_cam paths start at `u_wr_cam/r_bank`** flops. Both are cross-plane combinational cones (analysed under Findings 1 and 2).
- Worst wr_cam path: bank_timers `r_rc_reg` -> `u_wr_cam/r_strb_reg_0_7_3_3/DP/I` (RAMD32 write data), -4.029 ns, 20 levels, 79% route. Worst rd_cam path: `u_wr_cam/r_bank_reg[4][2]` -> `u_rd_cam/r_bank_reg[7][1]/CE`, -1.578 ns, 11 levels, 88% route.
- `sys100` run: wr_cam 1,005 failing endpoints, rank 4 behind the char-gen engines.

### Out-of-context Vivado 2025.1 synth of `mc_storage_plane`, xc7a100tcsg324-1, 13.333 ns clock, board generics, `XILINX USE_ASYNC_RESET` defines (scratchpad, nothing written to the repo): `/tmp/claude-1000/-mnt-data-github-RTLDesignSherpa/af42be44-f9ae-4bc5-806e-3e1980146142/scratchpad/ooc/util_hier_{board_merge1,board_merge0,n16_merge1}.txt`, `timing_*.txt`

| Instance | board, merge ON (LUT / FF / BRAM) | board, merge OFF | N=16, merge ON |
|---|---|---|---|
| mc_storage_plane total | 7,100 / 2,604 / 1 RAMB36 | 6,623 / 2,366 / 1 | 20,376 / 4,115 / 1 |
| u_wr_cam (mc_wr_data_cam) | **1,327** (16 LUTRAM) / 973 / 1 | 1,025 / 832 / 1 | 3,099 / 1,811 |
| u_rd_cam (mc_rd_cmd_cam) | **553** / 601 | 382 / 504 | 1,295 / 1,280 |
| u_wr_heads (mc_bank_head_records) | **2,554** / 496 | 2,554 / 496 | 8,004 / 512 |
| u_rd_heads | **2,553** / 496 | 2,553 / 496 | 7,975 / 512 |
| post-synth worst slack @13.333 ns | +0.498 ns (15 levels, ends at `r_strb` DP/I) | +4.211 ns | **-1.343 ns** standalone |

Caveat: OOC keeps every output port. In the real pumice build (SCHED_CORE=FR-FCFS) both `mc_bank_head_records` instances are dead and pruned (`macro/mc_scheduler_plane.sv:1046` ANDs `wr_head_i/.../rd_head2_i` into `_unused_arb`), and `sch_head_rel_o` constant-propagates away without `PUMICE_ENHANCED` (`fub/mc_cmd_arbiter.sv:955`). So the live storage-plane cost on the board is ~1,900 LUT / ~1,600 FF, and the merge feature is **+473 LUT / +238 FF of that plus the whole timing failure** (OOC slack 4.2 -> 0.5 ns; full chip +0.03 -> -5.63 ns, same-day builds).

## Summary table (ranked by expected board LUT saving, then timing risk)

| # | Structure | file:line | Size at board config | LUT / FF (measured or est.) | Why ASIC-shaped | FPGA alternative | Gives up |
|---|---|---|---|---|---|---|---|
| 1 | Write-combining CAM scans (`w_mg_match`, `w_mgt_match`, id-clash scans, youngest-by-matrix) + rd-cam `w_mg_hit` | `mc_wr_data_cam.sv:337-364, 388-430`; `mc_rd_cmd_cam.sv:198-214` | 3 x (8 entries x 34-bit compare) + 3 x 8x8-bit id scans + 2 x N^2 youngest picks | **+473 LUT / +238 FF measured** (wr +302/+141, rd +171/+97); owns 1,435 failing endpoints | Fully associative match every cycle on two different keys; merge decision feeds `ins_ready_o`, `wd_ready_o`, every entry CE and `r_strb` write data in the same cycle; `w_mgt_match` reads the scheduler's live `commit_valid_i` (`:396`) | Coalesce adjacent same-id same-address narrow writes at the intake with ONE registered 34-bit compare against the last pushed AW (the half-beat pairs the feature exists for arrive back-to-back from one engine), or build with MERGE_EN=0 on the FPGA SKU | Merging of non-adjacent pairs. Not load-bearing: a full-beat write never merges; a half-beat workload costs one masked BL4 per half, which the 300-400 MT/s DRAM at a 75-100 MHz host absorbs |
| 2 | `mc_bank_head_records` (two instances) | `mc_bank_head_records.sv:92-168` | 8 banks x {head, head2} from 8 entries: 56 pairwise 16-bit compares, 8x(13-bit 8:1 mux + compare), 64 masked popcounts, 16 x 8-way priority muxes of 30-bit records | **2,554 LUT each, 5,107 total measured** (8,000 each at N=16); 0 on the board today (pruned) | Derives per-bank order from an N^2 age matrix every cycle: O(B x N^2) popcounts + O(B x N x W) priority muxes | Per-(direction,bank) in-order FIFO of slot indices with the head read off the FIFO front and `same-row-behind` a stored bit - which is exactly `fub/mc_bank_fifo_store.sv` (1,460 lines, header lines 7-60) that granite already builds under `STORE_BACKEND=1` (`granite_core.sv:554-558`) | Nothing for a BANK_PICK scheduler (it only ever fires heads). **Action: never build SCHED_CORE=BANK_PICK on the CAM backend**; the records are the price of pairing an age-matrix CAM with a per-bank head contract |
| 3 | Snarf (read-your-write forward): registered probe, `w_sn_match`, youngest pick, `u_snarf_q`, shared BRAM read-port arbitration, anti-starvation counter, `w_sn_idle` | `mc_wr_data_cam.sv:456-487, 604-620, 737, 764-777, 285-287` | 8 x 34-bit compare + 64-term youngest + 3x8 FIFO + 2:1 index/tag muxing on a 64-bit port | est. 150-250 LUT, ~60 FF (hand: 8x14 LUT compare + 24 youngest + ~50 port mux + FIFO/ctrl); owns all 461 rd_cam failing endpoints | Associative match whose result `snarf_hit_o` leaves the plane combinationally and re-enters it: `snarf_hit_o:487` -> `mc_rd_intake.sv:486 ar_push_valid_o = r_s_valid && !w_hit && ...` -> `mc_storage_plane.sv:294 ins_valid_i` -> `mc_rd_cmd_cam.sv:214 w_ins_alloc` -> 8 entries x 61 bits of CE | Delete it. B is strobed only at drain evict (`:789-802`, `:973-981`), after which the entry is gone, so no read that AXI4 requires to observe a write (master waits for BRESP, IHI0022 "read and write interaction") can ever hit. If kept: register `snarf_hit_o` one more cycle so the hit never reaches the rd_cam allocation in the same cycle | Read-your-write latency for a same-id read that overtakes its own uncommitted write; those reads go to DRAM and wait behind the write at the bank |
| 4 | Free-running 16-bit age per entry: `r_age`, `r_age_ctr`, `w_rel` subtractors, `r_age_exceed` compares (both CAMs) | `mc_wr_data_cam.sv:183, 202, 227-231, 593-602`; `mc_rd_cmd_cam.sv:161-162, 169-173, 313-322` | 2 x (8 x 16 b age + 8 x 16-bit subtract + 8 x 16-bit >=) | est. ~190 LUT + 144 FF per CAM (16 LUT + 4 CARRY4 per subtract, ~8 LUT per compare) | On a base build the ONLY survivor of all this is the 1-bit `sch_age_exceed_o`; `sch_head_rel_o` is pruned, `oldest_*`/`sched_lu_*` are tied off (`mc_storage_plane.sv:236-249, 305-319`) | Per-entry 8-bit saturating counter stepped by one shared /16 prescaler (age_thresh is already in units of 16 cycles, `:319, :599`), compared directly with `age_thresh_i`; or a per-entry countdown loaded with the threshold -> ~8 FF + ~6 LUT per entry | The wrap-safe 16-bit relative age, needed only for `PUMICE_ENHANCED` global order |
| 5 | `r_strb` LUTRAM read-modify-write + strobe snapshot | `mc_wr_data_cam.sv:250, 920, 1011-1013` | 8 x 8 b, 2 async read ports + 1 write (RAMD32 confirmed in both reports) | ~16 LUTRAM (in the 16 measured) | Write DATA is `w_fill_merge ? old|new : new` - the terminal node of the merge cone in BOTH the OOC and the board worst paths | Falls out with #1 (data = `wd_strb_i`); if merge stays, decide the merge on the stable fill-FIFO head one cycle early and register it (the probe already gets this treatment at `:450-455`) | Nothing |
| 6 | N^2 age matrix `r_older` (both CAMs) + its re-registration in the arbiter | `mc_wr_data_cam.sv:210, 864-867`; `mc_rd_cmd_cam.sv:167, 353-356`; `mc_cmd_arbiter.sv:1137, 1157` | 2 x 64 FF + 128 FF copy; 1-bit compares | ~64 FF + ~64 LUT enable each; fine at N=8 | O(N^2) flops and O(N^2) AND-reduce per pick; 4x at N=16 (OOC: wr_cam 1,327 -> 3,099 LUT, rd_cam 553 -> 1,295, plane fails 13.3 ns standalone) | KEEP at N=8. If the window ever grows, per-bank FIFO order (#2's alternative) replaces the matrix entirely | - |
| 7 | Entry field flop arrays written by `w_free_slot`, read in parallel by every comparator | `mc_wr_data_cam.sv:177-201`; `mc_rd_cmd_cam.sv:154-161` | wr: 73 b x 8 (incl. 8-bit `r_mgid`); rd: 61 b x 8 | ~584 / ~488 FF (measured totals 973 / 601 incl. skid, probe regs, counters) | Inherent to a CAM: every key visible every cycle forbids LUTRAM/BRAM | Only shrinks by removing consumers (#1, #3, #4 remove `r_id` compares, `r_mgid`, `r_age`). Payload fields are correctly FDRE (no reset); only control bits are FDCE (`:825-833`, `:334-337`) | - |
| 8 | SRAM slot pre-allocator `r_sram_occ`/`r_ptr`/`r_pv` + 3 pointer muxes | `mc_wr_data_cam.sv:184-185, 213-224, 690-708` | 8 x 3 b + 8 b occ + 3 x (8:1 x 3 b) | est. ~40 LUT / ~32 FF | A second allocator for a resource that is 1:1 with entries at the board config (`N_SRAM_SLOTS == NUM_ENTRIES`) | `generate if (N_SRAM_SLOTS == NUM_ENTRIES)` slot = entry index | Decoupled slot count (never used by any build found) |

## Keep as-is (correct FPGA shape)

- **`r_mem` write-data store** `mc_wr_data_cam.sv:248-251, 985-1009`: reset-free process, byte-enable write, one registered read -> maps to 1 RAMB36 (8 x 64 b, 1.4% of the tile, but the board uses 2 of 135 so it does not matter). The latency-1 contract and warning (`:995-1003`) are right. Could be RAM32M (~11 LUT) at this depth; no reason to bother.
- **2-deep prefetch skid** `:261-275, 719-760, 904-951`: ~300 FF / ~100 LUT, needed to stream a synchronous-read RAM at 1 beat/cycle; correct even at 1-beat bursts.
- **gaxi_fifo_sync instances** `u_fill_q` (42 b x 8), `u_snarf_q` (3 x 8), `u_drain_q` (3 x 8), `u_done_q` (17 x 4): reset-free `mem[]` with async `g_mux` read (`rtl/amba/gaxi/gaxi_fifo_sync.sv:200-219`) -> RAM32M LUTRAM (confirmed `gen_auto.mem_reg_0_7_18_23` names). Correct.
- **Free-slot find-first** (`:304-312`, `mc_rd_cmd_cam.sv:178-186`): 8-bit priority encoders, trivial.
- **Rate-matched commit gate** `commit_ready_o/commit_ready_now_o` `:650-669`: the pop-free predicate is the right call; no combinational loop (arbiter consumes `wr_commit_ready_i` only in its registered pick, `mc_cmd_arbiter.sv:881, 1655-1662`; fire is `r_pick_valid && cmd_ready_i && w_out_safe`, `:449`). DRC of the merge-era build has no LUTLP/latch findings.
- **Registered snarf probe** `r_sp_*` `:456-461, 837-843` and **registered `r_age_exceed`**: the right pattern - it just needs to be applied to the merge decision and to `snarf_hit_o` too.
- `mc_rd_cmd_cam` otherwise (382 LUT / 504 FF with merge off): a sane 8-entry scheduling window; its only large consumer is the exported N^2 matrix, fine at N=8.

## Correctness / timing smells for an FPGA

1. **Scheduler fire cone drives both intake readies combinationally** (`mc_wr_data_cam.sv`): `commit_valid_i` (= `w_fire_out && r_wr_commit`, `mc_cmd_arbiter.sv:1890`, where `w_fire_out` includes the live bank-timer `bank_rdwr_ready_i`, `:395-401`) -> `w_commit_fire:651` -> `w_mgt_match[i] ... !(w_commit_fire && commit_slot_i==i)` `:396` -> `w_fill_merge_now:419` -> `w_fb_alloc:425-426` -> `ins_ready_o:361` and `wd_ready_o:427-430` -> `w_ins_alloc/w_fb_alloc:379, 846` -> every entry field CE (`:850-867`) and `r_strb` data (`:1012`). This is the 1,105-endpoint, -4.0 ns cone and violates the plane contract the records header states (`mc_bank_head_records.sv:12-14`). Also note `ins_ready_o` (AW side) depends on `wd_valid_i` (W side) through `w_fb_alloc`; legal for a slave, but it is one more long comb path.
2. **Storage -> AXI plane -> storage in one cycle** via `snarf_hit_o` (Finding 3). All 461 rd_cam failures.
3. **`ins_merge_o/ins_merge_ticket_o`** (`mc_rd_cmd_cam.sv:212-213`) are combinational from `ins_*` through the 8 x 34-bit compare and an 8:1 ticket mux into the return ring's allocation the same cycle (`:79-83`). Same shape as (2); not yet in the 75 MHz failing set, will be at 100 MHz.
4. **Async reset everywhere** (`ALWAYS_FF_RST` is unconditionally `negedge rst`, `rtl/amba/includes/reset_defs.svh`; `USE_ASYNC_RESET` changes nothing there). Storage arrays are correctly kept out of the reset process (`r_mem`, `r_strb`, FIFO `mem[]`), and payload entry fields are not reset; only control bits are FDCE. No BRAM-under-reset hazard remains. Residual cost: FDCE forces a separate control set per reset domain mix - acceptable.
5. **N=16 is not a board option**: the macro default `WR_CAM_DEPTH=16` (`ddr2_char_macro.sv:92`) would make the storage plane alone 20k LUT and fail 13.3 ns in isolation (`util_hier_n16_merge1.txt`, `timing_n16_merge1.txt`). The harness's override to 8 (`ddr2_char_harness.sv:739` with its O(N^2) comment) is load-bearing and should become the macro default.
6. No latches, no comb loops found (Vivado DRC clean on both counts; all `always_comb` blocks fully assign their outputs with defaults first).

## Bottom line for the owner

- The pumice storage plane's CAM core at N=8 is ~1,400 LUT / ~1,300 FF with merge off and closes 75 MHz; that part is acceptable on the A7 (`reports/` run).
- What breaks it is the **TASK-060 combiners**: +473 LUT measured and two cross-plane same-cycle cones that turned a +0.03 ns build into -5.63 ns on the same day. On the FPGA SKU set `WR_MERGE_EN=RD_MERGE_EN=0` (or coalesce adjacent pairs at the intake with one registered compare) - that alone recovers ~34% of the failing endpoints and the whole wr_cam/rd_cam hotspot.
- Second, remove or register the **snarf** path; it is a latency optimization AXI4 does not require and it is the entire rd_cam failure set.
- Third, replace the 16-bit free-running ages with per-entry 8-bit prescaled counters (~380 LUT / ~290 FF across both CAMs, estimated).
- `mc_bank_head_records` is the single most expensive block (5.1k LUT at N=8, 16k at N=16) but is dead on the board; treat it as a hard rule against pairing BANK_PICK with the CAM backend - the per-bank FIFO store (`mc_bank_fifo_store`) is the FPGA-native form of the same contract and already exists.