# Scheduler-plane FPGA review (read-only) — pumice / granite shared `mc_scheduler_plane`

Path convention: `R = /mnt/data/github/RTLDesignSherpa/projects/components/mem-ctrl-ip/common-ip/rtl`. Files cited as `fub/x.sv:N` or `macro/x.sv:N` are under `R`. Board reports cited are under `/mnt/data/github/RTLDesignSherpa/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/`. Nothing was modified.

## Board parameterization actually in use

| | granite (Nexys A7, 100 MHz) | pumice (Nexys A7 build-perf, 75 MHz) |
|---|---|---|
| Pick core | `SCHED_CORE = MC_SCHED_BANK_PICK` → `mc_bank_pick` (granite_core.sv:48, plane macro/mc_scheduler_plane.sv:775-777) | `SCHED_CORE = 0` FR-FCFS → `mc_cmd_arbiter` (pumice_core.sv:66; ddr2_char_top.sv:351) |
| NUM_ENTRIES / banks / IW | 8 (`GRANITE_SEAM_N`, granite_pkg.sv:28) / 8 / 8; ROW_WIDTH 13 on the board harness (granite_char_harness.sv:32) | 8 (`WR_CAM_DEPTH 8`, ddr2_char_harness.sv:739) / 8 / 8, AGE_WIDTH 16 |
| Bank timers | TW=5, `BANK_EVT_REG=1` (SET_LAG), LA=2, LA_AP=1 (granite_core.sv:77-78; plane :661-671) | TW=8, EVT_REG=0, LA=4 (plane :76-84, :661) |
| FAST_RD_RELEASE | built and forced on (`fast_rd_en_i=1'b1`, granite_core.sv:868, :889) | built, runtime bit (pumice_core.sv:75) |
| DUAL_ISSUE / QoS / ORDER modes | off / not wired (`_unused_pick`, plane :890-900) / n.a. | DUAL_ISSUE off unless `PUMICE_DUAL_ISSUE`; QoS **runtime** (`sched_qos_en_i`) so the trees are always built; order/col_sel/row_sel runtime |
| Page policy | on, PP_TIMEOUT_CLOSE on, telemetry off, stall stats off (granite_core.sv:852-858) | on, telemetry on, stall stats on |
| Refresh features | POSTPONE/PULLIN/REFPB/DRAIN_BURST all off (granite_core.sv:877-880) | all on |

Measured (granite `reports_sys100_2026-10-29_ddr400/utilization_hier.txt:107-119`): `mc_scheduler_plane` 1753 LUT / 875 FF; `mc_bank_pick` 726/194; `mc_bank_timers` 568/352 (8 × 67-82 LUT / 44 FF); `mc_global_timers` 165/62; `mc_page_policy` 203/215; cmd FIFO 104 (24 LUTRAM). WNS +0.021 ns at 100 MHz (timing_summary.txt:156). No hierarchical report exists for the pumice build; its `utilization_impl.txt` shows 47,336 LUTs total vs granite's 36,695 on the same harness family, and its 2026-10-27 sys75 report has WNS −5.63 ns with the worst 6 paths all inside `g_arbiter.u_arbiter` (`r_rd_pop_reg → r_wr_col_q_reg`, timing_worst.txt:16-34) — treat that number as "that build", but the path itself is structural (finding 1 below).

Note on the owner's "AXI_ID_WIDTH 8→9 doubled the arbiter" data point: `AXI_ID_WIDTH` reaches `mc_cmd_arbiter` as `IW` (fub/mc_cmd_arbiter.sv:96) and is never used in the body. The doubling must have been in the storage plane (CAM id matching / what the CAM exports), not in this plane.

## Summary table (ranked: LUT savings, then timing risk)

| # | Structure | Where | Size at board config | Est. LUT/FF | Why ASIC-shaped | FPGA alternative | Gives up |
|---|---|---|---|---|---|---|---|
| 1 | Same-(bank,row) population matrices `rd_pop/wr_pop/rd_xpop/wr_xpop` (pumice) | fub/mc_cmd_arbiter.sv:1031-1060 | POOL=16; 16×16 pairs × 2 (same-dir + cross-dir) of 3+14-bit equality + 32 popcounts, recomputed every cycle | ~900-1,700 LUT | O(N²) comparators recomputed from static CAM fields; an ASIC absorbs 240 17-bit compares in a couple of gate levels | Maintain `behind_same_row` / sibling flags incrementally in the CAM at insert/commit (what `mc_bank_head_records` does once per direction, fub/mc_bank_head_records.sv:~95-110), or fix `col_sel/row_sel`=0 so `pops` are never read | population-weighted column/row pick modes (research knobs `sched_col_sel_i 1/2`) |
| 2 | Per-entry classify `pool_col_m/act_m/pre_m` (pumice) | fub/mc_cmd_arbiter.sv:832-909 | 16 entries × (8:1 × 14-bit open-row mux + 14-bit eq (`phit`), 3 more row compares (`phit_spec` :846-850), ~8 one-bit 8:1 guard muxes) | ~900-1,200 LUT | row-hit recomputed every cycle from a bank-indexed register file instead of stored | Per-entry registered `hit` flag in the CAM updated on ACT/PRE events to its bank (granite's record contract: mc_common_pkg.sv:160-169, mc_bank_fifo_store.sv:1333); pre-decode 8-bank × 3-class eligibility once, entries index it | nothing functionally (hit is 1 cycle stale, already the granite contract) |
| 3 | `arg_sel` ×4 + `arg_oldest` ×2 argmax matrices (STAGE-1b, pumice) | fub/mc_cmd_arbiter.sv:1062-1094, :919-937, calls :1225-1235 | 8×7 pair cells each with two 4-bit magnitude compares + age bit + 8→3 encode, ×4; plus 2 age-only | ~800-1,000 LUT | N² pairwise compare matrix per class per direction | Per-bank heads (bank_pick shape) or FIFO order per bank (fifo_store); if FR-FCFS kept, `col_sel/row_sel` as build params =0 → `arg_sel` collapses to `arg_oldest` (~60 LUT each) | same as #1 |
| 4 | `mc_bank_timer` ×8: duplicated CSR arithmetic + 5 down-counters | fub/mc_bank_timer.sv:147-151 (`f_ld`), :222-230 (`t_X <= LA+1`), :165-200 (counters) | 8 × (5 × 5-bit counters, 6 saturating subtracts of CSRs, 5 CSR compares, max+add for LA_AP :232-240) = 568 LUT/352 FF measured | −150..−200 LUT by hoisting the CSR arithmetic; −250..−300 by SRL delay lines; −100 by 5→3 counters | per-bank replication of logic that is identical in every instance; decrement+load+zero-detect per constraint | (a) compute `f_ld(t,LD)`, `t<=LA+1`, `t<=1` ONCE in `mc_bank_timers` (or in the CSR block, registered) and pass the derived values; (b) SRLC32E dynamic-tap delay lines for tRCD/tRP/tRC/tRAS (tap = CSR value, runtime-programmable); (c) merge {tRC,tRP}→`act_block` and {tRAS,preblk}→`pre_block` with `max()` on load | (b): timings > 31 cycles need SRL cascade or saturation (TW=5 already saturates at 31, fub/mc_bank_timers.sv:97-104); CSR changes only while idle (already the practice, plane :1141-1147 comment) |
| 5 | FR-FCFS open-row demand `g_demand_vec` (pumice) | macro/mc_scheduler_plane.sv:397-421 | 16 × (8:1 × 14-bit mux + 14-bit eq) OR-reduced per bank; output registered :386-389 | ~450-550 LUT | duplicates #2's row compare a second time in the plane | per-entry registered hit → per-bank OR of `valid & hit & (bank==b)` (~50 LUT) | nothing |
| 6 | `qos_top` ×6 (pumice) | fub/mc_cmd_arbiter.sv:1106-1131 | 6 × (8 × 4-bit mask, 7 compare-selects in 3 levels, 8 × 4-bit eq) | ~300-400 LUT | runtime-enabled, so the tree is built whether or not QoS is used (ISSUE-027 already made it a tree) | build-time `HAS_QOS` (granite leaves it unconnected); or fold AxQOS into the insert-time age matrix so QoS is free at pick | runtime QoS toggle |
| 7 | FAST_RD_RELEASE `S_MAX` max tree (both cores) | macro/mc_scheduler_plane.sv:1141-1175 | 12 + 3 × 16-bit compare-select, 4×16 + 17 + 17 FF, for a value that is constant during traffic | ~150-200 LUT / 98 FF | parallel max over 16 CSRs of static data | one software-written `S_MAX` CSR, or a serial 16-cycle scan with one comparator (~12 LUT); keep `r_smax` reset to all-ones | nothing (the owner's comment already says the lag is invisible) |
| 8 | `mc_global_timers` tFAW 4-slot sliding window + two min-searches | fub/mc_global_timers.sv:131-152, :168-176, :199-215 | 4 × 8-bit slots, 2 × 3 serial 8-bit compares, registered pick | ~70-90 of 165 LUT, 34 FF | sliding window implemented as 4 countdowns + argmin | SRL of length tFAW: push 1 per ACT, 3-bit up/down count of pulses in the window, `ok = count < 4` (~6 LUT, 4 FF); tRRD/tWTR/tRTW/tCCD likewise SRL + flag | tFAW > 31 cycles needs cascade (not at 75-100 MHz DDR2) |
| 9 | `mc_page_policy` idle counters + last-row compare + live find-first | fub/mc_page_policy.sv:367-369, :512-538, :463-465, :543-557 | 8 × 8-bit reload counters (64 FF), 8 × 14-bit `r_last_row` (112 FF), 8 × 14-bit compare, 8-wide find-first feeding both pick combs live (arbiter :1690-1696; bank_pick :1096-1100) | ~80 LUT / 72 FF for counters; the find-first is a timing item | per-bank counters for an idle timer; comb request into the fire cone | SRL per bank (push on activity, tap = `tr_init`); REGISTER `timeout_pre_req/bank` (one cycle stale is fine — the owner already did exactly this for `open_row_demand`, plane :380-389) | nothing |
| 10 | STAGE-1b → STAGE-1a same-cycle feedback (pumice) — **timing** | fub/mc_cmd_arbiter.sv:474-520 (`w_if_*_sel` from `w_sel_*_s`), :565-575 (`w_rd_col_inflight_ent[w_sel_rd_col_s]`), :588-590 (`w_col_sel_now`), :557, :597-599 | 1a flop → `arg_sel` (6-8 levels) → `f_bank` 8:1 → `1<<` decode → guard OR → classify AND (:876-909) → `qos_top` (6-9 levels) → `r_*_q` | 0 LUT; ~20 LUT levels | the "pipeline" is not a pipeline: 1b's result gates 1a's mask in the same cycle | register the 1b shadows (bank_pick's `r_stale_pick/_win/_spec/_fire`, fub/mc_bank_pick.sv:656-671, :1318-1324 is the worked example) | one extra cycle of double-issue exposure, already covered by `rd/wr_sch_valid_i` re-validation (:1210-1220) |
| 11 | `w_out_ready` as clock-enable of ~400 FFs (pumice) — **timing** | fub/mc_cmd_arbiter.sv:468 (def), :1153, :1316 (CE of STAGE-1a and pre-pick) | cone = `w_out_safe`/`w_out_hold` ← live `bank_*_ready_i`, `w_col_row_ok` (8:1 × 14 + eq, :390-391), `w_ap_sibling` (16 × 17-bit compares, :750-770) | — | deep cone on a high-fanout enable | free-running 1a/pre-pick (drop, never hold — the owner's own measurement :340-352 says drop is lossless); supply "sibling exists" as a registered CAM flag so `w_ap_fire` is a register read | hold-under-backpressure of the pre-pick (a FIFO slot's worth of re-pick) |
| 12 | `mc_bank_pick` payload lookup at end of fire cone | fub/mc_bank_pick.sv:1131-1160 (`cmd_row_o = w_sel_is_wr ? w_wr_slot_row[w_sel_slot] : ...`) | 2 × 8:1 × (13+10) bits by a slot that is itself an 8-bit field muxed 16:1 (`w_sel_cand`, :1005) | ~120 LUT | wide one-hot/indexed mux of the payload in the issue cycle | register the winner's row/col one cycle ahead from `r_pick_pair`/`r_held_pair` (only the pop-shadow second-record case is truly live); or a LUTRAM copy of slot fields read by the registered slot | one cycle of payload staleness on the shadow path (needs the second record's slot registered too) |
| 13 | `mc_bank_pick` arbiter: 16:1 record mux, 3 × 16-bit `rr_onehot` carry chains, 5-way class select | fub/mc_bank_pick.sv:1005, :357-364, :779-781, :790-803 | NPAIR=16 | ~350-400 LUT of 726 | — (already O(N) one-hot logic) | keep; see timing note on `r_stale_fire → r_stale_pick` | — |

## 1. The two pick cores: which shape is right

**`mc_cmd_arbiter` (pumice).** Per cycle it recomputes, from the CAM's flat per-entry vectors (`*_sch_bank/row/col/older_i`, fub/mc_cmd_arbiter.sv:179-199):

1. Eligibility: `pool_col_m/act_m/pre_m` over POOL=16 entries (:832-909) — row hit via `r_bank_open_row[pbank]` 8:1 mux + 14-bit eq per entry, three speculative row compares (`phit_spec` :846-850), eight bank-indexed guard vectors, direction/turnaround/sink gates.
2. Populations: `rd_pop/wr_pop/rd_xpop/wr_xpop` (:1031-1060) — full 16×16 bank+row equality twice (same-dir and cross-dir), 32 popcounts.
3. Order overlays: `w_rd_head/w_wr_head` N² on the older matrix (:968-980), age/QoS masking, `qos_top` ×6 (:1106-1131).
4. STAGE-1a flops (:1144-1165): 6 masks, both 64-bit older matrices, 4 × 8 × 4-bit pops, `r_ap_snap` (~316 FF).
5. STAGE-1b: `arg_sel` ×4 (each 56 pair cells × two 4-bit magnitude compares + age bit) and `arg_oldest` ×2 (:1225-1235); the CLOSE_ON_DRAIN `w_rd/wr_ylast` which re-muxes the live CAM fields by the comb `w_sel_*_s` and runs 8 more compares each (:1264-1288); the pre-muxed operands (6 × 8:1 of 3..27 bits, :1311-1340).
6. Pick comb (:1606-1710): 12-way priority with the refresh drain find-first (:1519-1527).
7. Output register → fire stage with live re-check (:394-470), `w_ap_sibling` 16 compares (:750-770), `w_col_row_ok` (:390).

Estimated at pumice's config: ~4,500-5,200 LUTs for the arbiter alone (classify ~1,100, pop matrices ~1,000-1,700, ylast/sibling ~300, arg_sel/oldest ~1,000, qos ~360, premux/guards ~350, pick+fire+stats ~400). Cross-check: pumice total is 10.6k LUT above granite on the same harness (47,336 vs 36,695), of which the arbiter-vs-bank_pick delta and the two open-row compare banks plausibly account for roughly half; the rest is the CAM store. No hierarchical report exists to confirm — recommend one `report_utilization -hierarchical` run.

Combinational depth of the 1a→1a loop (finding 10): `arg_sel` (≈6-8 LUT levels) → `f_bank` 8:1 (2) → decode (1) → guard OR (1-2) → classify AND (2) → `qos_top` (6-9) → qos_en mux (1) ≈ 20 levels. At 100 MHz on a -1 Artix (~0.45 ns LUT + ~0.5 ns route per level) the budget is 8-9 levels. The board's own worst path (`r_rd_pop_reg → r_wr_col_q_reg`) is this loop; the arbiter's TASK-045/049 comments (:597-617) record trimming it twice for 0.1-0.2 ns at 75 MHz. It cannot reach 100 MHz without registering the 1b shadows.

**`mc_bank_pick` (granite).** Three stages, every stage fed by flops (fub/mc_bank_pick.sv:21-27): decode over 16 pair heads (:440-497, ~3 LUT/pair), rotor arbiter on one-hot vectors with per-source `rr_onehot` and registered stale masks (:673-880), fire with live timer read (:1031-1056) and `w_hold_next` ending in D inputs (:1085). Measured 726 LUT / 194 FF; my structural estimate (stage 0 shadow muxes ~130, decode ~50, arbiter ~350-400, fire+payload+dir ~250) matches.

**Verdict: bank_pick is the FPGA shape.** It replaces the 16-entry pool with 16 pair heads (one per bank per direction), the age matrix with per-bank FIFO order held in the store, and the one-hot payload mux with a slot lookup. What it gives up — FR-FCFS among non-head entries of the same bank, population-weighted picks, QoS, cross-entry in-order — matters little with 8 entries over 8 banks (rarely >2 per bank). The owner's own measurements in the comments favour it (e.g. plane :415-421: 761 vs 523 ACTs per 16,384 columns, 539 vs 557 MB/s). If pumice must keep FR-FCFS as the research core, the FPGA-correct refactor is to move the per-entry work into the CAM as **registered per-entry flags** (hit, same-row-behind, sibling-exists, maintained at insert/commit/ACT/PRE events) and let the arbiter pick on bits, not fields; `mc_bank_head_records` (fub/mc_bank_head_records.sv:95-130) is the pattern.

## 2. Why the one-cycle pick-and-issue loop matters less than the code assumes

At DFI 1:2 the plane emits at most one command per host cycle (one FIFO push, plane :1079-1083; DUAL_ISSUE adds only a row command on the other phase). The owner's arbiter comment (:1475-1480) says that at the board geometry one column per host cycle saturates both the command slot and the data bus. So **throughput** of the pick must be 1/cycle, and any pipelining that keeps 1/cycle costs nothing on bank-interleaved streams. What a deeper pipeline costs is **dependent-hop latency** on a single bank: ACT→COL (tRCD = 2 host cycles at 100 MHz DDR2-400), PRE→ACT (tRP = 2), COL→PRE (tRTP 1-2). Those hops equal the pipeline depth, so each extra stage is +1 cycle per hop on single-bank streams only (the owner measured col_major gap 9 vs floor 6 without the hint, bank_pick :41-48). bank_pick already pays for this correctly: register-only hint/speculation (:1212-1230, :836-880) rather than a live bypass. The arbiter instead reaches for live terms (`phit_spec` against `w_act_pick`, `w_col_hold`, `w_act_hold`) that pull the fire cone into the classify cone — that is the ASIC habit to break.

## 3. Per-bank timers (`mc_bank_timer`, fub/mc_bank_timer.sv)

Shape: five saturating down-counters per bank (`r_rcd, r_ras, r_rc, r_rp, r_preblk`, :130; loads :165-200), `safe_*` = AND of zero-detects (:203-210), lookahead `r_X <= LA` (:222-230), LA_AP max+add (:232-240), SET_LAG "effective" fold (:155-163). FF per bank at TW=5: 25 counter + 1 + 13/14 row + 1 AP + 4 lag = 44 yes. LUT 67-82 per bank; the instance-to-instance variance itself says the per-instance CSR arithmetic was not merged.

Where the LUTs go (per bank, est.): 5 × (decrement + load mux + `!=0`) ≈ 45-50; `f_ld(t, LD)` saturating subtracts of CSR values ×6 ≈ 15-20 (**identical in all 8 instances**); `t_X <= LA+1` and `t_X <= 1` CSR compares ×7 ≈ 7 (identical in all 8); LA_AP `max` + 7-bit add + compare ≈ 10.

Does "JEDEC timings as CSRs" force this shape? **No.**
- Hoisting the CSR-derived constants (`f_ld` results, `t<=LA+1`, `t<=1`) into `mc_bank_timers` once, or registering them in the CSR block, is a pure win: −150..−200 LUT, and it takes the CSR fields off the fire cone (see timing: granite's top path starts at `field_storage_reg[TIMINGS_RTP_RTW][tRTP]`, timing_worst.txt:16-24 — that is `t_rtp_i` entering `w_preblk_z` :160 and the hint compare bank_pick :1225).
- **SRLC32E delay lines** are runtime-programmable: the 5-bit dynamic tap address *is* the CSR value. ACT strobe → SRL(tap = tRCD-1-LA) → "la" pulse; two FFs later → live pulse; a 1-FF flag cleared by the strobe and set by the pulse replaces counter + zero-detect + `<= LA` compare. Works for tRCD, tRP, tRC, tRAS (their triggers cannot repeat inside their own window because tRC/tRP+tRCD gate the next trigger). `preblk` (tRTP/tWR) *can* retrigger inside its window (columns at tCCD) — keep it a counter or add a 2-bit in-flight count. SET_LAG's "effective" fold disappears (shift the tap by one). Range: granite already saturates at 31 (TW=5), the same as one SRL32. Est. −250..−300 of the 568 LUT; FF roughly flat (−25 counter bits, +~16 SRL/flag FFs per bank net −9).
- Shared time base + "ready-at" timestamps: 5 timestamps per bank still need 5 magnitude compares (3-4 LUT each) plus wrap handling, vs the counter's ~10; a ~30% saving at best and the lookahead becomes a subtract. Not recommended over SRLs.
- Merging counters (5→3: {tRC,tRP}→`act_block` loaded with `max(cur, t)`, {tRAS,preblk}→`pre_block`) is exact (both constraints are ANDed today, :203-210) and simplifies the AP fire (`w_ap_fire = ap_pending && pre_block==0`, cf. :174). −~100 LUT, −80 FF. Independent of the SRL choice.

Keep: `EVT_REG`/SET_LAG (the owner's 2026-10-28 census shows why, :54-66), the row image on the live strobe, TW=5 saturation.

## 4. `mc_global_timers` (fub/mc_global_timers.sv) — 165 LUT / 62 FF

Next-state computed once and both the counters and the `ok` outputs registered from it (:120-130, :243-258) — keep, that is exactly right for the FPGA (zero comb at the consumer). The tFAW window (:131-152 argmin ×2 in parallel, :168-176, :199-215) is ~half the block; an SRL window + 3-bit in-flight counter gives the same `ok` with ~6 LUT. The single counters (tRRD/tWTR/tRTW/tCCD, 8-bit) could each be SRL + flag (~2 LUT, 2 FF). Low priority (~100 LUT total), but the same pattern as the bank timers so it comes for free with that rework.

## 5. `mc_page_policy` (fub/mc_page_policy.sv) — 203 LUT / 215 FF

Per-bank idle countdown (:512-538), per-bank `r_last_row` 13/14-bit + compare against the ACT row (:414, :463-465, :492-495), drain-arm/keep-open predictor bits, and a comb find-first producing `timeout_pre_req_o/bank_o` (:543-557) consumed live by both pick cores (arbiter :1690-1696; bank_pick :1096-1100 with two more live 8:1 muxes of `bank_row_active_i`/`bank_pre_ready_i`). `PRED_CMD_REG` (:279-338) already registers the command input for granite — good. Recommend: register `timeout_pre_req/bank` (an idle timer tolerates a stale cycle; the owner did this for `open_row_demand`, plane :380-389) and, if the timer rework happens, SRL the idle timers (−~70 LUT/56 FF). The 14-bit `r_last_row` per bank is needed after the row closes, so it cannot share the timers' `open_row`.

## 6. `mc_xddr2_refresh_ctrl` (skim, fub/mc_xddr2_refresh_ctrl.sv)

16-bit tREFI countdown (:120-127, :184-196), 4-bit pending/pull-in credits, burst counter, rotor; all outputs registered (:357-379). Granite compiles the credit/REFpb/drain features out. Nothing ASIC-shaped here; keep.

## 7. Plane glue (macro/mc_scheduler_plane.sv)

- `g_demand_vec` open-row compares on FR-FCFS (:397-421): second copy of the classify row compare (finding 5); becomes a per-bank OR once the CAM carries a hit flag.
- FAST_RD_RELEASE `S_MAX` tree (:1141-1175): ~180 LUT + 98 FF computing a constant (finding 7). Both boards build it.
- Command FIFO (`gaxi_fifo_sync` 35 × 16, :1090) + CMD_DELAY token shift (:1125-1135) + `r_tok_cnt` (:1190-1195): small, correct, keep. CMD_FIFO_DEPTH 16 could be 8 (CMD_DELAY_EFF is 9 on the board, granite_core.sv:273) but it is LUTRAM already.
- `r_rd_ret_busy` 2-FF sync (:763-772), `r_open_row_demand` register (:386-389): keep.

## 8. Timing risk at 100 MHz on a -1 Artix

Pumice (FR-FCFS):
1. STAGE-1a → STAGE-1a through `arg_sel` → `w_if_*_sel` guards → classify → `qos_top` (finding 10). The measured worst path (`r_rd_pop → r_wr_col_q`). Will not close at 100 MHz as written.
2. `w_out_ready` CE fan-out from `w_ap_sibling`/`w_col_row_ok`/live timer bits (finding 11).
3. `w_rd/wr_ylast` (:1264-1288): comb `w_sel_*_s` → 8:1 × 17-bit mux → 8 compares → `rd_col_ap` flop; sits after the full `arg_sel` in the 1b cycle.
4. Fire stage → `evt_*` → `mc_bank_timer` counter loads with SET_LAG=0 (plane :84 sets `BANK_EVT_REG` only for BANK_PICK): `w_ap_sibling` → `w_ap_fire` → `evt_ap_o` → `r_ap_pending` and `cmd_op_o` → FIFO. Turn `BANK_EVT_REG` on for pumice too (the plane already supports it).
5. Pick comb (:1606-1710) is ~12-way priority over pre-muxed registers — moderate, probably fine.

Granite (BANK_PICK), from the 0.021 ns build:
1. CSR `tRTP` field → bank timer `w_preblk_z` fold (:160) / hint compare (bank_pick :1225) → `w_fire` → `rd_issue_valid_o` → ring FIFO flags (three of the top five paths, timing_worst.txt:16-24). Register the CSR-derived predicates once (section 3).
2. `r_stale_fire → r_stale_pick` and `r_hold → r_pick_cls` (0.034-0.058 ns): the select loop the owner has been trimming (bank_pick :656-671, :776-803). Further relief: register `w_self_stale` one more cycle or drop `r_stale_fire` into the decode instead of the select.
3. Payload 8:1 × 23-bit by a 16:1-muxed slot at the end of the fire cone (finding 12).

## Keep-as-is

- `mc_bank_pick` overall shape: per-bank heads, rotor, registered stale masks, `r_hold` 2:1 of registers, per-source `rr_onehot`, hint/speculation as register-only predicates, hit carried in the record.
- `mc_global_timers` single next-state + registered `ok` outputs.
- `mc_bank_timers` EVT_REG/SET_LAG, live row image, TW=5 saturation, LA_AP term.
- `mc_page_policy` PRED_CMD_REG; `r_open_row_demand` register in the plane.
- Command FIFO + CMD_DELAY token shift; `rd_ret_busy` synchronizer; refresh controller.
- The arbiter's fire-stage live re-check as the JEDEC authority (:394-470) — the principle is right; only its inputs (`w_ap_sibling`, `w_col_row_ok`) need to become registers.

## Suggested order of work

1. Hoist CSR-derived timer constants out of the 8 `mc_bank_timer` instances (−150..−200 LUT, removes the CSR fan-out critical path on granite). Mechanical, both cores.
2. Replace the FAST_RD_RELEASE max tree with a CSR or serial scan (−~180 LUT/98 FF). Mechanical, both cores.
3. Register `timeout_pre_req/bank` in `mc_page_policy`. Mechanical, both cores.
4. SRL delay lines (or at least 5→3 counters) in `mc_bank_timer`; same pattern for tFAW. −250..−400 LUT across both timer blocks.
5. Pumice: either move to `SCHED_CORE = BANK_PICK` on the board (the owner designated pumice FR-FCFS as research), or, if FR-FCFS stays, (a) register the 1b shadows, (b) move hit / same-row-behind / sibling flags into the CAM as registered per-entry bits, (c) make `col_sel/row_sel/QoS` build-time. (a) alone is what 100 MHz needs; (b)+(c) are the ~3k-LUT savings.
