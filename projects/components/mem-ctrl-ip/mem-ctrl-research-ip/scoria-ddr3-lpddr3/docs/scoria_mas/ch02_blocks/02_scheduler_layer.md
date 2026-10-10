<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Scheduler Layer (`scoria_scheduler_layer`)

**Module:** `scoria_scheduler_layer.sv` / **Location:** `rtl/macro/` / **Category:** command scheduling / **Parent:** `scoria_core` / **Status:** complete and sim-verified.

---

## Purpose

The scheduler layer is the command brain. It wires the init sequencer, mode-register shadow, refresh and ZQ controllers, write-leveling interface, per-bank timers, global timers, page-policy engine, and command arbiter into one macro that emits a single abstract DRAM command per cycle to the DFI layer. All JEDEC spacing is enforced here; the DFI layer downstream is never allowed to stall.

> **HISTORICAL NOTE — MC-001 rename:** older docs, including some andesite pages, call the host layer `scoria_axi4_ifc` and this layer `scoria_mem_cmd_scheduler`. The landed RTL names are `scoria_axi4_layer` and `scoria_scheduler_layer`. The modules are the same logic.

## Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| `NUM_RANKS` | int | 1 | DRAM ranks |
| `CMD_HISTORY_EN` | int | 0 | Optional issued-command history scoreboard |
| `HIST_T_RCD` ... `HIST_T_RTW` | int | 0/8 | History-checker JEDEC windows |
| `NUM_BANKS` | int | 8 | DRAM banks |
| `ROW_WIDTH` | int | 14 | Row address width |
| `COL_WIDTH` | int | 10 | Column address width |
| `AXI_ID_WIDTH` | int | 8 | AXI ID width |
| `NUM_ENTRIES` | int | 8 | CAM scheduling-window entries |
| `AGE_WIDTH` | int | 16 | Age-counter width |
| `CMD_FIFO_DEPTH` | int | 16 | Output command FIFO depth |
| `CMD_DELAY` | int | 6 | Fixed release delay in `aclk` cycles |
| `N_LU` | int | `NUM_BANKS` | Internal lookup width |
| `NUM_CS` | int | `NUM_RANKS` | Chip-select count |

: Table 2.2.1: Scheduler layer parameters

## Interface

### Timing, mode, and maintenance configuration ports

| Signal group | Signals | Width notes |
|---|---|---|
| Page policy | `page_policy_i` | `page_policy_e` |
| Core timings | `t_rcd_i`, `t_rp_i`, `t_ras_i`, `t_rc_i`, `t_wr_i`, `t_rtp_i`, `t_faw_i`, `t_rrd_i`, `t_wtr_i`, `t_rtw_i`, `t_ccd_i` | 8 each |
| Refresh timing | `t_refi_i`, `refi_reload_i`, `t_rfc_i`, `refresh_burst_i`, `ref_postpone_i`, `ref_pullin_i`, `ref_mode_i`, `ref_trefi_pb_i`, `ref_trfc_pb_i` | 16, 1, 16, 4, 4, 4, 2, 16, 8 |
| Init timing | `t_init_wait_i`, `t_dll_wait_i`, `t_mrd_wait_i`, `t_rp_wait_i`, `t_rfc_wait_i`, `t_xpr_wait_i`, `t_zqinit_wait_i` | 16, 16, 8, 8, 8, 16, 16 |
| Mode registers | `mr0_i` ... `mr3_i`, `init_restart_i` | 16 x 4, 1 |
| TASK-001 scheduler | `sched_order_mode_i`, `sched_row_sel_i`, `sched_col_sel_i`, `sched_access_pref_i`, `sched_wr_high_wm_i`, `sched_wr_batch_max_i`, `sched_wr_low_wm_i`, `sched_prio_sub_i`, `sched_qos_en_i` | 2, 2, 2, 2, 8, 8, 8, 2, 1 |
| TASK-001 page/refresh | `page_mode_i`, `page_tr_init_i`, `ref_elastic_en_i`, `ref_pullin_idle_streak_i`, `ref_postpone_demand_streak_i`, `ref_tcr_en_i`, `ref_trefi_derate_i` | 3, 8, 1, 8, 7, 1, 2 |
| TASK-001 ZQ | `zq_enable_i`, `zq_interval_i`, `t_zqcs_i`, `zq_placement_i`, `zq_overdue_max_i` | 1, 32, 16, 2, 13 |

: Table 2.2.2: Timing, mode, and maintenance configuration ports

### CAM scheduler/commit/issue ports (from `scoria_axi4_layer`)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `wr_sch_valid_i` | in | `NUM_ENTRIES` | Write CAM per-entry valid |
| `wr_sch_bank_i` | in | `NUM_ENTRIES * BKW` | Write CAM per-entry bank |
| `wr_sch_row_i` | in | `NUM_ENTRIES * ROW_WIDTH` | Write CAM per-entry row |
| `wr_sch_col_i` | in | `NUM_ENTRIES * COL_WIDTH` | Write CAM per-entry column |
| `wr_sch_older_i` | in | `NUM_ENTRIES^2` | Write CAM age-order matrix |
| `wr_sch_age_exceed_i` | in | `NUM_ENTRIES` | Write CAM age-exceed flags |
| `wr_sch_qos_i` | in | `NUM_ENTRIES * 4` | Write CAM per-entry QoS |
| `wr_sch_head_rel_i` | in | 16 | Write CAM head relative age |
| `wr_commit_ready_i` | in | 1 | Write CAM can accept commit |
| `wr_commit_valid_o` | out | 1 | Commit a write entry |
| `wr_commit_slot_o` | out | `PTRW` | Committed write slot |
| `rd_sch_valid_i` | in | `NUM_ENTRIES` | Read CAM per-entry valid |
| `rd_sch_bank_i` | in | `NUM_ENTRIES * BKW` | Read CAM per-entry bank |
| `rd_sch_row_i` | in | `NUM_ENTRIES * ROW_WIDTH` | Read CAM per-entry row |
| `rd_sch_col_i` | in | `NUM_ENTRIES * COL_WIDTH` | Read CAM per-entry column |
| `rd_sch_older_i` | in | `NUM_ENTRIES^2` | Read CAM age-order matrix |
| `rd_sch_age_exceed_i` | in | `NUM_ENTRIES` | Read CAM age-exceed flags |
| `rd_sch_qos_i` | in | `NUM_ENTRIES * 4` | Read CAM per-entry QoS |
| `rd_sch_head_rel_i` | in | 16 | Read CAM head relative age |
| `rd_issue_ready_i` | in | 1 | Read CAM can accept issue |
| `rd_issue_valid_o` | out | 1 | Issue a read entry |
| `rd_issue_slot_o` | out | `PTRW` | Issued read slot |

: Table 2.2.3: CAM scheduler/commit/issue ports

### Output command stream (to `scoria_dfi_layer`)

| Signal | Direction | Width | Description |
|---|---|---|---|
| `cmd_valid_o` | out | 1 | Command valid |
| `cmd_ready_i` | in | 1 | Command ready |
| `cmd_op_o` | out | `dram_op_e` | DRAM opcode |
| `cmd_rank_o` | out | `RKW` | Target rank |
| `cmd_bank_o` | out | `BKW` | Target bank |
| `cmd_row_o` | out | `ROW_WIDTH` | Row address |
| `cmd_col_o` | out | `COL_WIDTH` | Column address |
| `cmd_ap_o` | out | 1 | Auto-precharge flag |

: Table 2.2.4: Output command stream

### Init, PHY, mode-register shadow, and write-leveling ports

| Signal group | Signals | Width notes |
|---|---|---|
| PHY init | `dfi_init_start_o`, `dfi_init_complete_i`, `init_done_o`, `dram_reset_n_o` | 1 each |
| MR shadow | `cl_o`, `cwl_o`, `bl_o`, `mr_wr_o`, `wrlvl_en_o` | 4, 4, 4, 5, 1 |
| WRLVL CSR | `wrlvl_strobe_i`, `wrlvl_cs_sel_i`, `t_wldqsen_i`, `t_wlmrd_i`, `t_wlmrd_max_i`, `t_wlo_i`, `t_wloe_i` | 1, 4, 16, 16, 16, 16, 16 |
| WRLVL PHY | `dfi_phylvl_req_cs_n_o`, `dfi_phylvl_ack_cs_n_i`, `dfi_phy_wrlvl_cs_n_o`, `dfi_wrlvl_strobe_o`, `wrlvl_prime_dq_i` | `NUM_CS`, `NUM_CS`, `NUM_CS`, 1, 1 |
| WRLVL status | `wrlvl_result_valid_o`, `wrlvl_result_o`, `wrlvl_attempts_o`, `wrlvl_flips_o`, `wrlvl_timeout_o`, `wrlvl_ever_done_o`, `wrlvl_state_o` | 1, 1, 16, 16, 1, 1, 3 |

: Table 2.2.5: Init, PHY, mode-register shadow, and write-leveling ports

### Telemetry, stall attribution, and status ports

| Signal group | Signals | Width notes |
|---|---|---|
| Page stats | `stat_page_hit_o`, `stat_row_hit_o[NUM_BANKS]`, `stat_page_miss_o`, `stat_page_empty_o` | 32, 32 x banks, 32, 32 |
| Command stats | `stat_act_o`, `stat_pre_o`, `stat_ref_o`, `stat_ref_busy_o` | 32 each |
| Refresh/ZQ obs | `obs_ref_postpone_events_o`, `obs_ref_pullin_events_o`, `zq_busy_o`, `zq_total_o`, `zq_interval_cnt_o`, `zq_overdue_o` | 16, 16, 1, 16, 32, 1 |
| Stall attribution | `stall_bp_o`, `stall_refresh_o`, `stall_turnaround_o`, `stall_tccd_o`, `stall_actlimit_o`, `stall_banktimer_o`, `stall_noreq_o`, `stall_zq_o` | 32 each |
| Status | `busy_o` | 1 |

: Table 2.2.6: Telemetry, stall attribution, and status ports

## Microarchitecture internals

### Instantiation tree

The scheduler layer instantiates:

- `scoria_init_sequencer` — JEDEC initialization sequence.
- `scoria_mode_register` — MR0-MR3 shadow and latency decode.
- `scoria_refresh_ctrl` — tREFI tracker and REF/REFpb scheduling.
- `scoria_zq_ctrl` — periodic ZQCS maintenance.
- `scoria_wrlvl_ifc` — DFI v3.1 write-leveling handshake.
- `scoria_bank_timers` — one `scoria_bank_timer` per `(rank, bank)`.
- `scoria_global_timers` — rank-global and global spacing windows.
- `scoria_page_policy` — runtime page-policy decisions and telemetry.
- `scoria_cmd_arbiter` — command pick core.
- `gaxi_fifo_sync` — output command FIFO.
- Optional `scoria_cmd_history_checker` — generate-gated audit block.

### Command packing and output FIFO

The arbiter pushes accepted commands into a `gaxi_fifo_sync`. The FIFO data word is packed as:

```text
CMD_W = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1
w_cmd_wr_data = {a_cmd_ap, a_cmd_col, a_cmd_row, a_cmd_bank, a_cmd_rank, a_cmd_op}
```

The downstream DFI layer unpacks this word onto the DFI command bus.

### Fixed-delay release

Every push into the output FIFO also enters a `CMD_DELAY`-stage token shift register. The FIFO head is released only after the token matures, so every command reaches the DFI layer a fixed `CMD_DELAY` `aclk` cycles after arbitration. This keeps write data aligned with its command. Under DFI back-pressure the token counter accumulates matured-but-unpopped tokens.

### busy_o definition

`busy_o` is asserted while any of the following is true:

```text
busy_o = !init_done || refresh_req || w_cmd_rd_valid || (|w_bank_row_active[0])
```

### Refresh and ZQ gating

Refresh is gated on `init_done`. REFpb is enabled only when `ref_mode_i == 2'd2` and `memtype_i == MEMTYPE_LPDDR3`; otherwise REFpb degrades to REFab. ZQCS is run only for DDR3:

```text
w_refpb_en = (ref_mode_i == 2'd2) && (memtype_i == MEMTYPE_LPDDR3)
w_zq_run   = zq_enable_i && init_done && (memtype_i == MEMTYPE_DDR3)
```

### Page-policy tap

`scoria_page_policy` watches the arbiter's accepted command (`a_cmd_valid && a_cmd_ready`), not the FIFO output. Tapping the FIFO output would correlate each command with a stale bank image because the FIFO releases `CMD_DELAY` cycles later.

### Optional command-history checker

When `CMD_HISTORY_EN != 0`, a `scoria_cmd_history_checker` audits the issued command sequence against JEDEC same-bank windows and emits simulation-only `$fatal` assertions. It is generate-gated OFF by default.

## FSM policy

The scheduler layer has no FSM. It is a structural aggregation block. The arbiter is priority logic plus pipeline registers; the timers are decrement counters; refresh and ZQ are credit/state-counter machines. The init sequencer is the only state machine in this layer.

## Timing

The layer operates entirely on `aclk`. The critical path runs from the CAM vectors through bank/global timer checks, FR-FCFS priority selection, and the final safety gate to the FIFO push. The output FIFO and `CMD_DELAY` token shift register add fixed release latency but no new combinational critical path.

## Notes

- `scoria_scheduler_layer` was renamed from `scoria_mem_cmd_scheduler`; older andesite references use the old name.
- `scoria_init_sequencer` outputs `zqcl_req_o` and `init_busy_o` are tied off here.
- `scoria_mode_register` outputs `al_o`, `drv_strength_o`, `odt_o`, and `mr_req_o` are tied off here.
- The command-history checker is audit-only and must not be relied on for functional timing enforcement.
