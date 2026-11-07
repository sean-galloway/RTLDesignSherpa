# What the Artix-7 build reports say costs the most in pumice and granite

Scope: existing Vivado 2025.1 reports under `projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/` (abbreviated `R/` below), plus two hierarchical utilization reports generated in this session from the routed checkpoints. Nothing in the repo was modified. Parser scripts and per-build tables are in `/tmp/claude-1000/-mnt-data-github-RTLDesignSherpa/af42be44-f9ae-4bc5-806e-3e1980146142/scratchpad/fpga_reports/` (`parse_paths.py`, `parse_hier.py`, `*_buckets.md`, `*_top.md`, `*_paths.tsv`, `hier_*.tsv`, `pumice_util_hier.txt`, `granite_util_hier_1026.txt`).

## 0. Which build is which (read this before the numbers)

From the `Clock Summary` and `Design Timing Summary` sections of each `timing_summary.txt`:

| dir (under R/) | w_sys_i (ctrl clk) | w_sys2x_i (DRAM CK) | WNS ns | TNS ns | failing EP | total EP |
|---|---|---|---|---|---|---|
| build-perf/fpga/reports (pumice "latest") | **20.000 (50 MHz)** | 10.000 | +0.029 | 0 | 0 | 113066 |
| build-perf/fpga/reports_sys75_2026-10-27 | 13.333 (75 MHz) | 6.667 | -5.630 | -3862 | 4221 | 113281 |
| build-perf/fpga/reports_sys100_2026-10-27 | 10.000 (100 MHz) | 5.000 | **-9.005** | -40373 | **22755** | 113323 |
| targets/granite/fpga/reports_n4_2026-10-17 (OLD entry_store arch) | 13.333 | 6.667 | -5.929 | -11714 | 3725 | 94154 |
| targets/granite/fpga/reports_retime_2026-10-18 (old arch) | 13.333 | 6.667 | -1.346 | -1416 | 1814 | 95500 |
| targets/granite/fpga/reports_retry3a (old arch, 10-18) | 13.333 | 6.667 | -0.730 | -415 | 1333 | 95504 |
| targets/granite/fpga/reports (granite "latest", dated 10-26) | **13.333 (75 MHz)** | 6.667 | +0.299 | 0 | 0 | 104733 |
| targets/granite/fpga/reports_sys100_2026-10-27 | 10.000 | 6.667 | -0.753 | -275 | 756 | 106478 |
| ..._2026-10-27_rtl_plus_pick | 10.000 | 6.667 | -0.907 | -390 | 858 | 106542 |
| ..._2026-10-27_rtl_store_policy_timers | 10.000 | 6.667 | -0.583 | -229 | 766 | 106701 |
| ..._2026-10-28_addr_gen_reg | 10.000 | 6.667 | -0.234 | -5.5 | 67 | 107610 |
| ..._2026-10-28_harness_regs | 10.000 | 6.667 | -0.114 | -0.4 | 7 | 107780 |
| ..._2026-10-28_timer_set_lag | 10.000 | 6.667 | **+0.004** | 0 | 0 | 107847 |
| ..._2026-10-29_ddr400 | 10.000 | 5.000 | **+0.021** | 0 | 0 | 107862 |

Corrections to the brief:
- The passing pumice build is a **50 MHz** controller clock (`w_sys_i` 20 ns), not 75. At 75 MHz pumice fails by 5.6 ns, at 100 MHz by 9.0 ns.
- Granite's +0.299 slack is the **75 MHz** build. At 100 MHz granite passes by +0.004 (10-28 timer_set_lag) and +0.021 ns (10-29 ddr400).
- Granite 10-17/10-18 reports are the **previous architecture** (`u_entry_store` + `g_bank_sched.u_bank_sched`). From 10-27 the core is `g_fifo_store.u_fifo_store` (16 x `gaxi_age_fifo_sync`) + `g_bank_pick` + `g_page_policy`.
- `utilization_hier*.txt` in `reports/`, `reports_retime_2026-10-18/`, `reports_n4_2026-10-17/` are byte-identical copies (md5 `8c83493f...`, dated Oct 17 17:17). So there is one pre-rearch hier data point (10-17), the 10-29 one, and the 10-26 one I generated from the routed `.dcp`.

## 1. Pumice at 100 MHz: where the 22,755 failing endpoints are

Source: `R/build-perf/fpga/reports_sys100_2026-10-27/timing_failing_setup_full.txt` (all 22,755 paths parsed), cross-checked with `timing_failing_hotspots.txt` / `timing_failing_endpoints.csv` in the same dir.

Whole set: mean 6.3 logic levels (max 24), **route share 86%**. Controller-only paths (5,572 EP): mean **1.03 ns route per net**; harness paths 2.14 ns/net; granite 10-27 controller paths 0.62 ns/net. Pumice is congested: 75.6% LUTs, **95.2% of slices occupied** (`utilization_impl.txt`), and that inflates every path.

### 1.1 Failing endpoints by RTL block

| endpoint block | failing EP | worst slack ns | mean levels | mean route ns | mean logic ns |
|---|---|---|---|---|---|
| harness u_gen_unit (4 wr + 4 rd char engines) | 6596 | -3.573 | 5.1 | 8.85 | 1.82 |
| harness u_chargen_regs (PeakRDL CSR fields) | 3897 | -4.938 | 2.3 | 10.23 | 0.97 |
| harness u_hist_rd / u_hist_wr | 1892 / 1050 | -4.424 / -4.648 | 5.1 / 4.0 | 10.4 / 12.7 | 1.2 / 1.0 |
| harness u_bridge (AXIL xbar + APB adapters) | 1680 | -3.437 | 8.9 | 9.29 | 1.66 |
| **ctrl u_store_plane/u_wr_cam (mc_wr_data_cam)** | **1171** (1005 in the CAM itself) | **-7.441** | **16.3** | 11.41 | 2.74 |
| **ctrl u_axi_plane/u_rd_ring (mc_rd_return_ring)** | 944 | -4.501 | 9.2 | 11.57 | 1.68 |
| **ctrl u_sched_plane/g_arbiter.u_arbiter (mc_cmd_arbiter)** | 914 | **-9.005** | 7.7 | 9.80 | 1.66 |
| ctrl g_page_policy.u_page_policy | 849 | -4.404 | 9.4 | 9.21 | 2.20 |
| harness u_dfi_mon_ram | 550 | -3.984 | 8.5 | 9.45 | 1.57 |
| ctrl u_store_plane/u_rd_cam (mc_rd_cmd_cam) | 489 | -4.515 | 9.6 | 10.73 | 1.64 |
| harness u_skid_w | 465 | -3.373 | 7.1 | 10.83 | 1.37 |
| ctrl u_sched_plane/u_bank_timers | 428 | -2.371 | 10.1 | 8.40 | 1.98 |
| ctrl_wrap u_core/u_csr (pumice_csr) | 276 | -2.145 | 4.6 | 9.00 | 1.40 |
| ctrl u_axi_plane/u_rd_intake | 244 | -3.675 | 8.9 | 9.98 | 1.64 |
| ctrl u_dfi_plane/u_cdc | 139 | -3.698 | 6.7 | 9.51 | 1.75 |
| ctrl u_axi_plane/u_wr_intake | 12 | -6.190 | 17.5 | 11.79 | 2.89 |

Controller 5,572 (24%), harness 17,183 (76%). The harness is the count; the controller is the depth: every path worse than -6.2 ns is controller, and the 60 worst are all arbiter/CAM.

### 1.2 Failing startpoints (who launches the long cones)

| startpoint block | paths | worst ns | mean levels |
|---|---|---|---|
| harness u_gen_unit | 6049 | -4.424 | 6.6 |
| harness r_rst_sync_reg (one reset flop) | 3399 | -2.572 | 2.0 |
| harness u_chargen_shim APB-CDC FIFO rd pointer (fanout to 3.9k CSR flops) | 3159 | -4.938 | 2.4 |
| **ctrl u_bank_timers (`r_rp` tRP countdown 2055 paths, `r_ap_pending` 404)** | **2518** | **-7.441** | **12.8** |
| harness u_bridge | 2205 | -3.984 | 9.1 |
| **ctrl u_wr_cam (`r_fdone` 1290, `r_valid` 240)** | 1567 | -4.501 | 8.7 |
| ctrl g_arbiter (`r_rd_pop`/`r_wr_pop` age popcounts, `r_row`, `r_bank` replicas) | 534 | -9.005 | 9.1 |
| ctrl u_rd_ring (`r_tail`, `r_fptr`) | 320 | -4.208 | 8.7 |
| ctrl u_rd_cam (`r_valid`, `r_row`) | 179 | -8.978 | 7.1 |

Controller flows (count): bank_timers -> wr_cam **1114**; wr_cam -> rd_ring 811; wr_cam -> rd_cam 463; bank_timers -> page_policy 460; bank_timers -> arbiter 451; arbiter -> page_policy 389; wr_cam -> arbiter 273; rd_ring -> rd_intake 234. The per-bank timer "safe" bits (`mc_bank_timer.r_rp`) are consumed combinationally by the write CAM's per-entry eligibility, the arbiter classify stage and the page policy in the same cycle; the write CAM's fill-done bits (`r_fdone`) feed the read-return ring and the read CAM in the same cycle.

Failing endpoint register families inside the controller (count, worst): rd_ring `r_src` 768 (-4.50); page_policy `g_telemetry.stat_row_hit_o` 460 (-2.48); wr_cam `r_row` 208 (-5.71), `r_col` 160 (-5.83), `r_id` 128 (-5.95), `r_age` 128 (-5.68), `r_mgid` 64, `r_older` 56, `r_bank` 48 (-6.02), BRAM `r_mem_reg` DP/SP data pins 80 (**-7.44**), `WADR*` 48; rd_cam `r_age` 128, `r_row` 104, `r_col` 80, `r_older` 56; bank_timers `r_preblk` 123, `r_rc` 86, `r_rcd` 83, `r_rp` 75; arbiter `r_wr_pre_q/r_wr_col_q/r_wr_act_q` (the 60 worst) and `stall_*_o` telemetry 5 x 32.

The two biggest harness items are not logic depth: `r_rst_sync_reg -> */CLR,PRE,R` (3,399 recovery/removal checks on the async-reset net reaching 23,833 async-reset flops; 2 levels, 9 ns route) and `u_chargen_shim/u_apb_cdc/u_cmd_cdc_fifo/.../counter_bin_reg -> u_chargen_regs/field_storage_reg[...]` (2,684 paths, 2 levels, ~14 ns route: one FIFO-pointer-derived write strobe fanning out to all 3,897 CSR field flops).

### 1.3 The 20 worst paths (all one cone)

Same start/end/slack as the first 20 rows of `timing_worst.txt`. Clock skew -0.13 ns; budget 10.0 ns. Every path: 3.2-3.8 ns in LUTs (0.124 ns/LUT), ~15 ns in routing.

| # | slack | levels (mix) | data path = logic + route | start -> end | LUTs by module |
|---|---|---|---|---|---|
| 1 | -9.005 | 23 (LUT6=18 LUT5=4 LUT3=1) | 18.87 = 3.31 + 15.56 | arbiter `r_rd_pop_reg[7][2]` -> arbiter `r_wr_pre_q_reg[3]/D` | wr_cam 12, arbiter 9, rd_cam 2 |
| 2 | -8.978 | 24 (LUT6=14 ... MUXF7=1) | 18.81 = 3.82 + 14.99 | rd_cam `r_valid_reg[1]` -> arbiter `r_wr_col_q_reg[2]/D` | wr_cam 15, arbiter 8, rd_cam 1 |
| 3 | -8.956 | 22 | 18.84 = 3.57 + 15.27 | rd_cam `r_valid_reg[1]` -> arbiter `r_wr_col_q_reg[6]` | wr_cam 13, arbiter 8, rd_cam 1 |
| 4-6, 8, 19 | -8.93..-8.82 | 24 | 18.8 = 3.82 + 15.0 | rd_cam `r_valid_reg[1]` -> arbiter `r_wr_col_q_reg[0,4,5,1,3]` | same cone |
| 7, 9, 12, 15, 16, 18 | -8.93..-8.84 | 22 (LUT6=14-15 LUT5=4-5) | 18.7 = 3.18 + 15.5 | arbiter `r_rd_pop_reg[5][0]` -> arbiter `r_wr_act_q_reg[1,5,2,0,6,4]` | arbiter 11, wr_cam 10, rd_cam 1 |
| 10, 11, 13, 14, 17, 20 | -8.92..-8.80 | 22-23 | 18.7 = 3.3 + 15.4 | arbiter `r_rd_pop_reg[7][2]` -> arbiter `r_wr_pre_q_reg[0,2,5,1,6,4]` | wr_cam 11-12, arbiter 9, rd_cam 2 |

Path 1 cells in order: `rd_act_s[1]_i_140, _i_112` (arbiter read-ACT slot pick) -> `rd_col_s[1]_i_32, _i_11, _i_2, rd_col_s[0]_i_2` (read-COL slot pick) -> `rd_col_bank[2]_i_2` (bank of the picked read slot, placed in u_rd_cam) -> `r_rd_pre_q[1]_i_19, r_rd_pre_q[7]_i_24, _i_8` (read PRE candidate mask) -> `r_wr_pre_q[7]_i_98 ... r_wr_pre_q[3]_i_1` (13 LUTs, write PRE candidate mask, placed in u_wr_cam). Paths 7/9/12: `rd_act_s -> rd_act_bank -> r_rd_act_q -> r_wr_act_q`; paths 2-6: `rd_pre_s -> rd_pre_bank -> r_rd_col_q -> r_wr_col_q`.

**RTL structure:** `mc_cmd_arbiter` STAGE-1a (`projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arbiter.sv`, 1,999 lines). The read-side slot pick (`rd_{act,col,pre}_s`, an argmax over NUM_ENTRIES=8 read-CAM entries using `r_rd_pop[]` age popcounts and the `r_rd_older` matrix, decl. lines 313-318/1135-1141) resolves to a bank, which then qualifies the **write**-side candidate masks `r_wr_{pre,col,act}_q` (same-bank exclusion/turnaround), which fold in the write CAM's per-entry row/col/bank compare against the open-row image and the bank-timer `safe_*` bits. Read pick is serialized in front of the write mask: one ~23-level cone. The arbiter's own comment (~line 1100) records the QoS argmax used to be "the last ~15 LUT levels of the 27-level Vivado path that missed 50 MHz (pumice ISSUE-027)"; it was balanced, and the path is still 22-24 levels at 100 MHz and **27 levels** in the passing 50 MHz build (`build-perf/fpga/reports/timing_summary.txt`: `r_rd_pop_reg[6][1] -> r_wr_pre_q_reg[5]`, 19.78 ns = 3.80 logic + 15.98 route, slack +0.029 at 20 ns). At 0.124 ns/LUT + ~0.6 ns/net even uncongested, 23 levels is ~17 ns: this cone cannot make 10 ns on a -1 Artix-7 by placement alone.

Second cone (worst -7.44, 1,114 paths): `u_bank_timers/g_bank[*].u_bt/r_rp` -> `u_wr_cam` entry eligibility -> BRAM `r_mem_reg` write-port data/address pins, 16-18 levels (timer-ready -> CAM pick -> SRAM fill). Third (worst -4.50, 811 paths): `u_wr_cam/r_fdone` -> `u_rd_ring/r_src` (768 EP).

### 1.4 Pumice at 75 MHz (`reports_sys75_2026-10-27`, 4,221 failing)

Harness nearly clean; controller alone fails by 5.6 ns: wr_cam 1120 EP (-4.03, 16.6 levels), rd_ring 787 (-1.45), rd_cam 461 (-1.58), rd_intake 195, page_policy 135, arbiter 118 (**-5.63**, 23-24 levels, 18.8 ns, same `r_rd_pop -> r_wr_col_q` cone). Flows: bank_timers -> wr_cam 1105, wr_cam -> rd_ring 785, wr_cam -> rd_cam 461.

## 2. Granite: what was worst, and what is on the knife edge

### 2.1 Old architecture (10-17 / 10-18 / retry3a, 75 MHz)
- 10-17 (-5.929, 3,725 EP, route 83%): all controller failures start in `u_entry_store` (2,029 startpoints) and end in `g_bank_sched` (901) or `u_bank_timers` (864), 21-22 levels. Worst: `u_entry_store/r_wr_sched_reg[2] -> u_cmd_fifo/gen_auto.mem_reg_0_15_6_11/RAMC_D1/I`, 21 levels (CARRY4=2 LUT6=15 MUXF7=1), 18.81 ns = 4.00 + 14.81. Cells: `r_ws[4][slot]/[row]/[vld]` (per-bank write-head scan) -> `r_actfire0` -> `r_open_row[*]` (bank_timer) -> cmd_fifo LUTRAM write; nets `r_open_row[3]_i_10_1` fo=51 1.48 ns, `r_ws_reg[6][vld]_1` fo=31.
- 10-18 retime (-1.346): same cone, 17 levels, 13.9 = 3.7 + 10.2: `u_entry_store/r_rd_valid_reg[6]` (fo=55) -> `r_rs[7][row][12]` -> `r_rdfire0` -> `counter_bin_curr` -> cmd_fifo `mem_reg/WE`.
- retry3a/fp1 (-0.730): `u_entry_store/r_wr_sched_reg[4] -> u_bank_timers/g_bank[1].u_bt/r_preblk_reg[7]/CE`, 18 levels, 13.64 = 3.82 + 9.82. `reports_fp1/VERDICT.txt`: four Pblock floorplans all made it worse (-2.6 to -3.1).
- Utilization (10-17 `utilization_hier_deep.txt`): `mc_xddr2_entry_store` **4,725 LUT** / 806 FF / 1 RAMB36 = 57% of granite_core's 8,340 LUTs; `mc_bank_sched` 888; `mc_bank_timers` 468.

### 2.2 New architecture (10-27 onward, 100 MHz)
- 10-27 (-0.753, 756 EP): 587 are harness `u_gen_unit` address generators (8 levels incl. one DSP48E1, 10.5 ns = 5.0-5.2 logic + 5.4 route: `r_lfsr/r_*_req_count -> u_addr_gen_*/r_s1_offset_0_reg`). Controller: `g_fifo_store/g_q[*].u_wq` 26 (-0.346), `u_dfi_plane/u_cdc` 24 (-0.076), `g_bank_pick` 18 (**-0.728**, 11.9 levels), `u_global_timers` 12, `g_page_policy` 8 (-0.706, 14.5 levels).
- 10-27 rtl_plus_pick (-0.907): bank_pick `r_cls_reg[3][0] -> r_pick_cls_reg[1]`, 17 levels (CARRY4=6 LUT6=8), 10.81 = 3.22 + 7.59; nets `r_pick_pair[3]_i_50` fo=33, `r_dir_i_4` fo=22.
- 10-27 rtl_store_policy_timers (-0.583): bank_pick `r_stale_spec_reg[5] -> r_stale_pick_reg[14]`, 11 levels, 10.64 = 3.15 + 7.49; `r_req_reg[12] -> r_pick_cls_reg[0]`, 11 levels, 10.49 = 1.88 + **8.61 route**.
- 10-28 addr_gen_reg (-0.234, 67 EP): bank_pick `r_stale_pick -> r_stale_pick` 11-13 levels; harness `r_beats_in_burst -> o_beats_mismatched/CE` 18-19 levels (CARRY4=11-12 comparator chain).
- 10-28 harness_regs (-0.114, 7 EP): all bank_pick (`r_req_reg[5] -> r_pick_cls_reg[0]` 11 levels 10.02 = 1.82 + 8.20).

### 2.3 Knife edge in the passing builds

| build | worst setup path | slack | levels | data path | structure |
|---|---|---|---|---|---|
| 10-28 timer_set_lag, 100 MHz | `g_bank_pick/r_cls_reg[4][1] -> r_stale_pick_reg[14]/D` | **+0.004** | 14 (CARRY4=4 LUT6=5) | 9.96 = 2.74 + 7.22 | bank_pick stale-pick one-hot mask from class register |
| same, next | `r_cls_reg[8][1] -> r_pick_cls_reg[0]` +0.009; `r_cls_reg[4][1] -> r_stale_pick_reg[13]` +0.012; harness `u_wr_order_q/r_rd_ptr -> w_channel skid CE` +0.027 x5; `u_addr_gen_r/r_s2_addr -> o_beats_mismatched/CE` +0.035 | | | | |
| 10-29 ddr400, 100 MHz | `u_ctrl/u_csr/field_storage_reg[TIMINGS_RTP_RTW][tRTP][value][3] -> u_rd_ring/u_issue_q/fifo_control_inst/rd_empty_reg/D` | **+0.021** | 13 (LUT6=8) | 9.88 = 2.07 + 7.81 | **CSR timing value -> bank_timer compare (`r_pre_rdy`, `r_preblk`, `r_rp`) -> bank_pick fire (`r_wrfire0`, `r_tccd_fwd`, `g_pred_cmd_reg.r_pc_to`) -> issue_q FIFO full/empty** |
| same, next | `r_stale_fire_reg[5] -> r_stale_pick_reg[9]` +0.034; tRTP -> `g_q[4].u_wq/wr_full` +0.036; tRTP -> `u_issue_q/wr_full` +0.041; tRTP -> `g_q[5].u_wq/wr_full` +0.041; `r_hold_reg_replica -> r_pick_cls_reg[0]` +0.058; tRTP -> `g_q[1].u_rq/rd_empty` +0.065 | | | | |
| granite "latest", 75 MHz | `g_bank_pick/r_hold_reg -> r_pick_cls_reg[1]` | +0.299 | 11 (LUT6=7) | 12.96 = 2.45 + **10.51 route** | `r_hold_reg_0` net **fanout 138**, 1.33 ns; then `r_stale_pick[7]_i_5 .. r_pick_cls[1]_i_1` |
| same, next | CSR write `u_chargen_shim/u_cpuif/r_cmd_pwdata_reg[8] -> u_chargen_regs/...START_ADDR[8]` +0.359; `r_hold_reg -> r_stale_pick_reg[14]` +0.564; `u_bank_timers/g_bank[6]/r_row_valid -> g_page_policy/r_keep_open_reg` +0.769 | | | | |

The granite knife edge is one block, `mc_bank_pick` (726 LUT / 194 FF): the effective-winner mux (`r_hold ? r_held_cls : r_pick_cls`, mc_bank_pick.sv:521, `r_hold` fo=138) feeding the `r_stale_pick` one-hot mask and `r_pick_cls`, 11-14 levels with 7-10 ns of route. In 10-29 a second cone appears: the CSR-held JEDEC timing value (`tRTP`, fo=11) compared combinationally in the bank timers, through the bank_pick fire stage into the issue/bank FIFO full/empty flags in one cycle (13 levels, +0.021).

## 3. Utilization

### 3.1 Granite controller per module (LUT / LUTRAM / FF / RAMB36)

Sources: 10-17 `R/targets/granite/fpga/reports_n4_2026-10-17/utilization_hier_deep.txt` (old arch); 10-26 = this session's `granite_util_hier_1026.txt` from `targets/granite/fpga/build/.../granite_char_top_routed.dcp` (the 75 MHz "latest" build); 10-29 `R/targets/granite/fpga/reports_sys100_2026-10-29_ddr400/utilization_hier.txt`.

| instance (module) | 10-17 old arch | 10-26 new, 75 MHz | 10-29 new, 100 MHz |
|---|---|---|---|
| u_ctrl (granite_top_geared) | 8534 / 370 / 4591 / 2 | 5156 / 404 / 3799 / 2 | 5654 / 404 / 4267 / 2 |
| u_core (granite_core) | 8340 / 370 / 4062 / 2 | 4918 / 404 / 3298 / 2 | 5456 / 404 / 3766 / 2 |
| u_entry_store (mc_xddr2_entry_store) | **4725 / 4 / 806 / 1** | - | - |
| g_fifo_store.u_fifo_store (mc_bank_fifo_store) | - | 2088 / 196 / 1501 / 1 | **2204 / 196 / 1524 / 1** |
| .. own logic (excl. queues) | - | 456 / 0 / 1203 / 1 | 372 / 0 / 1226 / 1 |
| .. g_q[0..7].u_rq/u_wq (16 x gaxi_age_fifo_sync) | - | 86-94 LUT, 12 LUTRAM, 18 FF each | 87-204 LUT each (q[1].u_wq 204, q[5].u_rq 143, q[7] 135/141); ~1,770 LUT total |
| .. u_wr_drain_q | 216 / 4 / 10 | 99 / 4 / 10 | 67 / 4 / 10 |
| u_sched_plane | 1578 / 24 / 1140 | 1478 / 24 / 816 | 1753 / 24 / 875 |
| .. g_bank_sched.u_bank_sched | 888 / 0 / 586 | - | - |
| .. g_bank_pick.u_bank_pick | - | 716 / 0 / 191 | **726 / 0 / 194** |
| .. g_page_policy | - | 150 / 0 / 192 | 203 / 0 / 215 |
| .. u_bank_timers (8 x mc_bank_timer) | 468 / 0 / 440 | 393 / 0 / 320 | **568 / 0 / 352** |
| .. u_global_timers | 135 / 0 / 69 | 123 / 0 / 60 | 165 / 0 / 62 |
| u_axi_plane | 1278 / 180 / 1172 / 1 | 963 / 66 / 790 / 1 | 1097 / 66 / 1176 / 1 |
| .. u_rd_ring (mc_rd_return_ring) | 248 / 8 / 245 / 1 | 365 / 8 / 245 / 1 | **506 / 8 / 629 / 1** |
| .. u_rd_intake / u_wr_intake / u_wr_split | 425/92/434, 237/80/388, 299/0/63 | 198/26/236, 260/32/228, 77/0/45 | 193/26/236, 258/32/230, 76/0/45 |
| u_dfi_plane | 404 / 162 / 398 | 282 / 118 / 163 | 284 / 118 / 163 |
| u_train_plane | 238 / 0 / 518 | - | - |
| u_init_plane | 117 / 0 / 28 | 111 / 0 / 28 | 110 / 0 / 28 |
| u_csr (granite_csr) | 194 / 0 / 529 | 242 / 0 / 501 | 200 / 0 / 501 |

Growth 10-26 -> 10-29 (+538 LUT core): bank_timers +175, rd_ring +141 LUT / +384 FF, fifo_store +116 (q[1].u_wq +110), page_policy +53, global_timers +42. The rearchitecture (10-17 -> 10-26) cut the core 8,340 -> 4,918 LUTs, almost all of it the 4,725-LUT entry store becoming a 2,088-LUT FIFO store.

### 3.2 Pumice controller per module (from the routed checkpoint; caveat)

Generated this session (`pumice_util_hier.txt`) from `R/build-perf/fpga/build/vivado_project/ddr2_char.runs/impl_1/ddr2_char_top_routed.dcp` (Oct 27 09:58). **Caveat:** that checkpoint is a 50 MHz build with **7 wr + 7 rd** char engines (57,417 LUT, 56 DSP; impl log WNS -0.968), not the 4+4 (46,861 LUT, 32 DSP) in the three pumice report dirs. The controller is the same source and parameters, so its numbers are representative; the harness numbers are not comparable.

| instance (module) | LUT | LUTRAM | FF | RAMB36 |
|---|---|---|---|---|
| u_ctrl/u_core (pumice_top) | 11897 | 432 | 6509 | 2 |
| u_core (pumice_core) | 11257 | 432 | 5936 | 2 |
| **u_sched_plane (mc_scheduler_plane)** | **4970** | 24 | 2467 | 0 |
| .. **g_arbiter.u_arbiter (mc_cmd_arbiter)** | **3426** | 0 | 1139 | 0 |
| .. u_bank_timers (8 x mc_bank_timer) | 913 | 0 | 441 | 0 |
| .. g_page_policy | 367 | 0 | 744 | 0 |
| .. u_global_timers / g_refresh | 141 / 80 | 0 | 69 / 42 | 0 |
| **u_store_plane (mc_storage_plane)** | **3710** | 56 | 1492 | 1 |
| .. **u_wr_cam (mc_wr_data_cam)** | **2329** | 56 | 988 | 1 |
| .... own logic | 1584 | 8 | 950 | 1 |
| .... u_fill_q (8x42 gaxi_fifo_sync) / u_snarf_q / u_drain_q | 432 / 189 / 94 | 28 / 4 / 4 | 10 each | 0 |
| .. u_rd_cam (mc_rd_cmd_cam) | 1382 | 0 | 504 | 0 |
| u_axi_plane (mc_axi4_plane) | 2078 | 190 | 1617 | 1 |
| .. u_rd_ring (own 635 + u_issue_q 324) | 958 | 8 | 693 | 1 |
| .. u_rd_intake / u_wr_intake / u_wr_split | 476 / 290 / 285 | 96 / 86 / 0 | 444 / 370 / 68 | 0 |
| u_dfi_plane | 411 | 162 | 332 | 0 |
| u_init_plane | 105 | 0 | 28 | 0 |
| u_csr (pumice_csr) | 711 | 0 | 573 | 0 |

Bank timers are uneven: `g_bank[1].u_bt` 349 LUT and `g_bank[5].u_bt` 270 vs 43-63 for the other six (synthesis pulled scheduler/CAM logic into them; they are also the bank-timer hotspots in `timing_failing_hotspots.txt`). Pumice core is 2.06x granite core (11,257 vs 5,456 LUT); the arbiter alone (3,426) is 4.7x granite's bank_pick (726); the two CAMs (3,711) are 1.7x granite's whole FIFO store (2,204).

### 3.3 Whole-design resources (`utilization_impl.txt`; xc7a100t: 63,400 LUT, 126,800 FF, 135 RAMB36 / 270 RAMB18, 240 DSP)

| | pumice 50 MHz | pumice 100 MHz | granite 75 MHz | granite 100 MHz 10-29 | granite old 10-17 |
|---|---|---|---|---|---|
| Slice LUTs | 46861 (73.9%) | 47947 (75.6%) | 39233 (61.9%) | 36695 (57.9%) | 36924 (58.2%) |
| LUT as Logic | 44735 | 45821 | 37127 | 34589 | 34854 |
| **LUT as Memory = as Distributed RAM** | **2126** | 2126 | 2106 | 2106 | 2070 |
| LUT as Shift Register | 0 | 0 | 0 | 0 | 0 |
| Slices occupied | 15040 (**94.9%**) | 15089 (**95.2%**) | 13603 (85.8%) | 13642 (86.1%) | 13328 (84.1%) |
| Slice Registers (0 latches) | 35512 | 35613 | 32654 | 33719 | 29031 |
| F7 / F8 Muxes | 1560 / 140 | 1560 / 140 | 1090 / 137 | 1106 / 140 | 1008 / 126 |
| Unique Control Sets | 1187 | 1319 | 1077 | 1161 | 1181 |
| **Block RAM Tile (RAMB36)** | **2 of 135 (1.48%)** | 2 | 2 | 2 | 2 |
| RAMB18 | 0 of 270 | 0 | 0 | 0 | 0 |
| DSP48E1 | 32 | 32 | 32 | 32 | 16 |

Registers by type (Clock Enable / Synchronous / Asynchronous columns):

| | pumice 50 | pumice 100 | granite 75 | granite 100 (10-29) | granite 10-17 |
|---|---|---|---|---|---|
| CE, **async Reset** | **23766** | 23833 | 21873 | 22790 | 21109 |
| CE, sync Reset | 10883 | 10883 | 10106 | 10058 | 7212 |
| CE, async Set | 677 | 711 | 494 | 690 | 525 |
| CE, sync Set | 186 | 186 | 181 | 181 | 185 |
| no reset | 0 | 0 | 0 | 0 | 0 |

67-69% of all flops carry an **asynchronous** reset; none is reset-free. All 32 DSPs are harness (`u_addr_gen_*`, 4 per engine); the controllers use none.

Where the 2,126 LUTRAM go (synth `Distributed RAM: Final Mapping Report`): `u_dfi_mon_ram/.../g_wstrb.r_mem_reg` 512x32 = **RAM64M x 176** and `u_debug_sram/.../g_wstrb.r_mem_reg` 256x64 = **RAM64M x 176** (1,432 LUTs for two harness SRAMs that would each fit one RAMB36); the rest are gaxi FIFOs of depth 4-128.

**Storage comment:** 135 x 36 kb = 4.86 Mb of BRAM is available and 2 tiles are used, one holding an **8 x 64-bit array (512 bits)** (`mc_wr_data_cam/r_mem_reg`) and the other a 64x64 read-return ring. Meanwhile ~2.1k LUTs are distributed RAM and tens of thousands of flops hold CAM/queue state (pumice wr_cam 988 FF + rd_cam 504 + rd_ring 693 + arbiter 1,139; granite fifo_store 1,524 + rd_ring 629; harness `u_hist_rd/u_hist_wr/r_ts_reg[*][*][*]` timestamp arrays 2,278 + 1,725 FF, which alone are 2,048 failing endpoints). The main storage resource idles while the slice fabric is 95% full, which is what inflates route delay on every pumice path.

## 4. Synthesis-log RAM inference

Logs: `R/build-perf/fpga/build/vivado_project/ddr2_char.runs/synth_1/runme.log` (pumice) and `R/targets/granite/fpga/build/vivado_project/ddr2_char.runs/synth_1/runme.log` (granite).

### 4.1 Block RAM (`Block RAM: Final Mapping Report`)
| design | module | object | depth x width | note |
|---|---|---|---|---|
| pumice | mc_wr_data_cam | `r_mem_reg` | **8 x 64** | 1 RAMB36 for 512 bits, forced by `(* ram_style = "block" *)` (mc_wr_data_cam.sv:248); `[Synth 8-7052]` no output register could be merged |
| pumice | u_rd_ring | `r_mem_reg` | 64 x 64 | 1 RAMB36; 8-7052 |
| granite | g_fifo_store.u_fifo_store | `r_mem_reg` | **8 x 72** | 1 RAMB36; `[Synth 8-7082]` "better mapped onto distributed LUT RAM... depth (3 address bits) is shallow", overridden by `ram_style="block"` (mc_bank_fifo_store.sv:377) |
| granite | u_rd_ring | `r_mem_reg` | 64 x 64 | 1 RAMB36 |

### 4.2 Distributed RAM: 48 (pumice) / 50 (granite) arrays, all `gaxi_fifo_sync/async` `gen_auto.mem_reg` or the two `sdpram_core` harness SRAMs. Largest controller ones: `u_dfi_plane/u_cdc/g_async.u_rd_fifo` 64x67 = 23 RAM64M, `u_rd_intake/u_order_fifo` 128x19 = 14 RAM64M, `u_wr_intake/g_wd_fifo` 16x73 = 13 RAM32M; granite's 16 age queues `g_q[*].u_wq/u_rq/mem_reg` 8x4 = 3 RAM32M each.

### 4.3 Blocked: `[Synth 8-4767] ... implemented in registers` 35 arrays (pumice) / 30 (granite), **one reason every time**: `1: RAM is sensitive to asynchronous reset signal. this RTL style is not supported.` followed by `RAM "<x>" dissolved into registers`.

| array (RTL file) | pumice | granite | what it is |
|---|---|---|---|
| `wr_fifo_reg`, `rd_fifo_reg` x7 each (generated `bridge_ddr2_char_axil/*_adapter.sv`) | yes | yes | harness bridge APB adapter FIFOs |
| `r_sk_data`(64b), `r_sk_blast`, `r_sk_strb`, `r_sk_slast`, `r_sk_mgv`, `r_sk_mgid`, `r_sk_iscm`, `r_sk_id`, `r_sk_agg` (mc_wr_data_cam.sv:262-271, `[SKID_DEPTH]`) | yes | `r_sk_data`(72b)/blast/slast/id (mc_bank_fifo_store.sv:382-385) | **the BRAM prefetch skid** beside each write-data BRAM |
| `r_ptr`, `r_mgid`, `r_last`, `r_id`, `r_q` (mc_wr_data_cam.sv `[NUM_ENTRIES]`) | yes | - | per-entry CAM tags |
| `r_ticket` (mc_rd_cmd_cam.sv:160) | yes | - | read CAM ticket |
| `r_wr_bank`, `r_wr_id`, `r_wr_last`, `r_rd_bank`, `r_rd_ticket` (mc_bank_fifo_store.sv:356-863) | - | yes | FIFO-store per-entry tags |
| `w_trk_mem_reg` (host_adapter.sv), `host_64b/32b_wdest_mem_reg` (xbar), `r_q` (char_gen_wr_order_q) | yes | yes | harness |

Cause: the repo reset macro `ALWAYS_FF_RST` = `always_ff @(posedge clk or negedge rst)` (`rtl/amba/includes/reset_defs.svh:55-62`). mc_wr_data_cam.sv uses it for 3 of its 5 always blocks; only `r_mem` (posedge-only blocks at ~1005/1011) could become RAM. Every indexed array written inside an `ALWAYS_FF_RST` block becomes flops + per-entry write-enable decode + read mux, which is where the 988 FF / 1,584 own-LUTs of the write CAM and the 1,226 FF of granite's fifo_store come from.

### 4.4 Other notes
- `[Synth 8-5544] ROM "r_older_reg[N]1" won't be mapped to Block RAM because address size (3) smaller than threshold (5)` x14 (pumice): the NUM_ENTRIES x NUM_ENTRIES `r_older` age matrices in both CAMs are being treated as 8-entry lookup tables.
- `[Synth 8-5546] ROM "w_slot_free" ... too sparse` x2 (pumice).
- `[Synth 8-3936] unconnected internal register 'w_cand_reg[N][slot]' trimmed from 8 to 3 bits` x16 (granite, mc_bank_pick.sv:289).
- `[Synth 8-3848] Net cg_in[...][next] does not have driver` x52 (granite, char_engine_block.sv:312: PeakRDL hw-next inputs undriven).
- No latch, combinational-loop or multi-driven messages in either log; `8-7129 unconnected port` hits are the unused DFI phase-2/3 ports of `a7ddrphy`.

## 5. Optional task 5 (hier utilization from checkpoints): done

`/tools/Xilinx/2025.1/Vivado/bin/vivado` exists; both routed `.dcp`s exist. Two batch runs (`pumice_hier.tcl`, `granite_hier.tcl` in the scratchpad, run via `setsid nohup ... -mode batch`) finished in under 4 minutes and produced `pumice_util_hier.txt` and `granite_util_hier_1026.txt` (depth 8), used in 3.1/3.2. A trailing `report_timing_summary -max_paths 1 -no_detailed_paths` in the scripts errored on an invalid flag combination; it was not needed. The pumice checkpoint is a 7+7-engine 50 MHz build (caveat in 3.2).

## 6. Ranked: RTL structures the FPGA data says are the most expensive / slowest

1. **pumice `mc_cmd_arbiter` read-pick -> write-mask cone (STAGE-1a).** 22-24 LUT levels at 100 MHz, 27 at 50 MHz; the 60 worst paths of the sys100 build (-9.005..-8.80 ns, 18.8 ns = 3.3 logic + 15.5 route) and the only thing holding the 50 MHz build at +0.029. 3,426 LUT / 1,139 FF, the largest block in either controller. Cells `rd_{act,col,pre}_s -> rd_*_bank -> r_rd_{pre,act,col}_q -> r_wr_{pre,act,col}_q`, fed by `r_rd_pop[]`/`r_rd_older` and the CAM row/bank compares. Evidence: `reports_sys100_2026-10-27/timing_failing_setup_full.txt` paths 1-20; `build-perf/fpga/reports/timing_summary.txt`; `pumice_util_hier.txt`.
2. **pumice `mc_wr_data_cam`: bank-timer `r_rp` -> entry eligibility -> BRAM write port.** 1,005 failing EP (worst -7.44 on `r_mem_reg` DP/SP/WADR, 16-18 levels), 1,114 paths from `u_bank_timers/r_rp`; 2,329 LUT / 988 FF / 1 RAMB36 for 8 entries plus 715 LUTs in three side FIFOs (`u_fill_q` 432 for 8x42). Nine of its arrays are flops because of the async-reset block.
3. **Async-reset storage arrays (both designs).** 35/30 arrays dissolved to registers, all for `RAM is sensitive to asynchronous reset signal`; 23.8k/22.8k async-reset flops; 2 of 135 BRAMs used while 2,126 LUTs are distributed RAM and slices are 95% full. This is the structural reason the designs are LUT/route-bound. Evidence: synth `runme.log` 8-4767; `utilization_impl.txt` register/memory sections; `reset_defs.svh`.
4. **pumice `mc_rd_return_ring` `r_src`/`r_shadow` fed from `wr_cam/r_fdone`.** 944 failing EP (768 on `r_src`, -4.50, 9 levels, 11.6 ns route), 811 wr_cam -> rd_ring paths; 958 LUT / 693 FF / 1 RAMB36.
5. **granite `mc_bank_pick` effective-winner -> `r_stale_pick`/`r_pick_cls` cone.** The worst setup path in every granite build since 10-27 (-0.907 .. +0.004 .. +0.299): 11-17 levels, `r_hold` fo=138, 7-10.5 ns route; 726 LUT. Plus the 10-29 CSR `tRTP` -> bank_timer compare -> bank_pick fire -> FIFO full/empty cone (13 levels, +0.021). Evidence: `timing_summary.txt`/`timing_worst.txt` of reports, 10-28_timer_set_lag, 10-29; 10-27 series.
6. **granite (old) `mc_xddr2_entry_store` per-bank head scan -> bank_sched fire -> bank_timer `r_open_row`/`r_preblk` CE.** 4,725 LUT, 21-22 levels, -5.9 ns at 75 MHz, immune to floorplanning (fp1 VERDICT). Retired by the 10-27 rearchitecture, which halved granite_core.
7. **pumice `mc_rd_cmd_cam`** (1,382 LUT / 504 FF, 489 failing EP, -4.5; `r_older` seen as 8-entry ROMs) and **`mc_page_policy` 32-bit per-bank telemetry counters** (`g_telemetry.stat_*_o`: 460+32+32+32 failing EP, 744 FF) on the same bank-timer fanout.
8. **pumice `mc_bank_timers`:** 913 LUT (vs 568 granite) for 8 banks; 2,518 failing startpoints because `safe_*` are combinational ANDs of countdown flags consumed the same cycle by CAM, arbiter and page policy; bank[1]/bank[5] instances absorb 270-349 LUTs of neighbour logic.
9. **Harness, not controller:** `u_chargen_regs` 3,897 failing EP from one APB-CDC-pointer-derived write strobe (2 levels, 14 ns route); `u_hist_*/r_ts_reg` 2,048 EP of timestamp arrays in flops; `r_rst_sync_reg` 3,399 recovery checks on the async reset net; granite `u_gen_unit` address generators 587-629 EP at 100 MHz (8 levels incl. DSP48E1, 5 ns logic) and `o_beats_mismatched` 18-19 level CARRY4 chains. These set the failing-endpoint count in every build, and the two harness SRAMs cost 1,432 LUTRAM that two BRAM tiles would absorb.
