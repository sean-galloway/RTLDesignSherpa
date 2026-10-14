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

# Command scheduler macro — `mc_scheduler_plane` instantiation

**Module:** `mc_scheduler_plane` (common IP)  
**Location:** `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_scheduler_plane.sv`  
**Category:** Plane-2 macro in `pumice_core`  
**Instance:** `u_sched_plane` (`rtl/top/pumice_core.sv:601-751`)  
**Child FUBs (pumice build):** `mc_xddr2_init_sequencer`, `mc_xddr2_mode_register`, `mc_xddr2_refresh_ctrl`, `mc_page_policy`, `mc_bank_timers` (`mc_bank_timer` per bank), `mc_global_timers`, `mc_cmd_arbiter`, `gaxi_fifo_sync` command FIFO

## Purpose

`pumice_core` instantiates the common `mc_scheduler_plane` directly, on `aclk`, between `u_store_plane` (`mc_storage_plane`) and `u_dfi_plane` (`mc_dfi_2p1_plane`). It owns the pick machinery, the bank and global timers, the DDR2/LPDDR2 bring-up and refresh children, the runtime page-policy engine, and the output command FIFO, and it emits one abstract command `{mrr, ap, col, row, bank, rank, op}` per accepted pick.

Until 2026-10-09 this was a pumice-local plane that bundled all of those functions. The Phase-2 extraction moved the pick machinery and timers into the common `mc_scheduler_plane`, and a thin `pumice_scheduler_plane` wrapper kept the DDR2/LPDDR2 children for one day. On 2026-10-11 those children moved into common-ip as the `mc_xddr2_*` FUBs and `mc_page_policy`, the common plane gained `HAS_*` selectors to compose them, and the wrapper was removed. Pumice now configures the plane purely by parameter and port wiring.

The common scheduler microarchitecture is documented in [Chapter 4 of the common MAS](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md); the family plane-stack and descriptor-seam architecture are defined in the [common HAS](../../../../../common-ip/docs/common_has/common_has_index.md).

## Children built in the pumice configuration

`pumice_core` leaves the `HAS_*` selectors at their defaults, so the plane elaborates:

| Instance | Module | Selector | Role |
|---|---|---|---|
| `u_init` | `mc_xddr2_init_sequencer` | `HAS_INIT_SEQUENCER = 1` | DDR2 + LPDDR2 JEDEC MRS init. Drives `dfi_init_start_o`, issues init commands into the arbiter, writes the MR shadow, and gates traffic until `init_done_o`. |
| `u_mode_reg` | `mc_xddr2_mode_register` | `HAS_MODE_REGISTER = 1` | MR shadow updated by init writes; decodes `cl_o` / `cwl_o` / `bl_o` for the DFI plane. |
| `u_refresh` | `mc_xddr2_refresh_ctrl` | `HAS_REFRESH_CTRL = 1` | `tREFI` down-counter, postpone/pull-in, and REFab/REFpb selection (enabled only after init). |
| `u_page_policy` | `mc_page_policy` | `HAS_PAGE_POLICY = 1` | Runtime page-policy engine producing the auto-precharge / timeout-precharge controls and the page telemetry. |
| `u_bank_timers` | `mc_bank_timers` | always | One FSM-free `mc_bank_timer` per (rank, bank). |
| `u_global_timers` | `mc_global_timers` | always | tFAW / tRRD / tWTR / tRTW / tCCD. |
| `u_arbiter` | `mc_cmd_arbiter` | always | The single command-pick core. |
| `u_cmd_fifo` | `gaxi_fifo_sync` | always | Scheduler-to-DFI command FIFO (`CMD_FIFO_DEPTH`, default 16). |

`HAS_CMD_HISTORY` stays 0, so the scheduler-side `mc_cmd_history_checker` (`u_cmd_history`) is not built in pumice; pumice's `CMD_HISTORY_EN` arms the DFI-wire checker inside `mc_dfi_cmd_path` instead. Because the children are internal, `pumice_core` ties the plane's external child-override inputs off: `init_done_i = 1`, `init_cmd_valid_i = 0`, `refresh_req_i = 0`, `ap_mode_en_i = 0`, `timeout_pre_req_i = 0`, and the rest to zero.

### Maintenance-slot mapping

`mc_training_plane` presents one maintenance request at a time. `pumice_core` wires it onto the plane's generic maintenance slot:

- `maint_req_i`      ← `trn_cmd_req_o` (`w_trn_req`)
- `maint_op_i`       ← `trn_cmd_op_o`
- `maint_bank_i`     ← `trn_cmd_bank_o`
- `maint_row_i`      ← `trn_cmd_row_o`
- `maint_col_i`      ← `'0`
- `maint_extra_i[0]` ← `trn_cmd_mrr_o`
- `maint_busy_i`     ← `cal_busy_o` (`w_cal_busy`)

`maint_grant_o` returns to the training plane as `trn_cmd_grant_i`, and the MRR flag comes back on `cmd_extra_o`, which `pumice_core` packs as `w_cmd_mrr`. The arbiter priority inside `mc_scheduler_plane` is init > refresh > maintenance > demand; see the [training-plane chapter](05_training_plane_macro.md) and the [training interface contracts](../ch04_apb_config/05_training_interface_contracts.md).

### Tie-offs and constants

Because pumice is a DDR2/LPDDR2 single-rank rock, several common features are disabled or tied off in `pumice_core`:

- `NUM_BG = 1` (default); `t_ccd_l_i`, `t_ccd_s_i`, `t_rrd_l_i`, `t_rrd_s_i` are tied to `8'd0`; `cmd_bg_o` is left open.
- `HAS_ZQ = 1'b0` (default): `zq_req_i` is tied to `1'b0`, `t_zqcs_i` to `16'd0`, and `stall_zq_o` / `zq_grant_o` are left open. ZQ calibration is handled by `mc_training_plane`, not the scheduler.
- `MAINT_EXTRA_WIDTH = 1` (default): the single-bit MRR flag is the only maintenance extra payload.
- `t_ccd_i` is driven from `w_t_ccd_eff`, the CSR value floored at `BURST_WORDS` (`pumice_core.sv:281-282`).
- `busy_o`, `bank_row_active_o`, `bank_open_row_o`, `cmd_accept_o` and `cmd_accept_op_o` are left open; the stall counters and page statistics (`stall_*_o`, `stat_*_o`) are routed out to `pumice_top`'s CSR telemetry.

## External boundaries

- **CAM schedulable-entry ports (to `mc_storage_plane`):** per-direction per-entry vectors (`*_sch_valid/bank/row/col/older/age_exceed/qos/head_rel`), write `commit_*` and read `issue_*` handshakes.
- **Command stream out (to `mc_dfi_2p1_plane`):** `cmd_valid/ready` + `{mrr, ap, col, row, bank, rank, op}`.
- **Maintenance channel in (from `mc_training_plane`):** `maint_req` + payload + `maint_grant` back.
- **Mode-register shadow out:** `cl_o` / `cwl_o` / `bl_o` to the DFI plane.
- **Init handshake:** `dfi_init_start_o` out and `dfi_init_complete_i` in (routed through the DFI plane); `init_done_o` status out.
- **Config in:** JEDEC timings, refresh/programming parameters, `page_policy_i`, `page_mode_i`, `page_tr_init_i`, and scheduler knobs — all delivered from the CSR by name.

## Pumice integration details that stay

- **Single controller clock:** the plane runs on `aclk`; the only controller-to-PHY datapath crossing is inside `mc_dfi_2p1_plane`.
- **External CAMs:** the schedulable-entry / commit / issue ports remain external; the CAMs live in `mc_storage_plane`.
- **Training priority and gating:** demand commands are blocked while `maint_busy_i` is asserted and the training request obeys the init > refresh > training > demand priority cone.

## Tests

The common `mc_scheduler_plane` owns the macro-level description of the pick machinery, bank/global timers, and command FIFO; see the [common MAS](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md). In pumice, scheduler behaviour is exercised through `pumice_core` / `pumice_top` (`dv/tests/top/`). The two scheduler-level macro tests, `test_pumice_scheduler_plane.py` and `test_pumice_sched_matrix.py`, still name the removed `pumice_scheduler_plane` wrapper and its filelist, so they must be repointed at `mc_scheduler_plane` before they run again.
