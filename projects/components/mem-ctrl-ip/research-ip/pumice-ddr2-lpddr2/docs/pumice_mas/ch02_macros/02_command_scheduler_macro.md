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

# `pumice_scheduler_layer` (command scheduler macro)

**Module:** `pumice_scheduler_layer.sv`
**Location:** `rtl/macro/`
**Category:** Layer-2 wrapper around the common `mc_scheduler_layer`

## Purpose

The `pumice_scheduler_layer` header comment describes it verbatim:

> Thin pumice wrapper around the common mc_scheduler_layer core. Instantiates the rock-specific init_sequencer, mode_register, refresh_ctrl, page_policy, and command-history checker, and maps the pumice training channel onto the generic maintenance slot.

This macro is no longer the owner of the pick machinery, bank/global timers, refresh controller, init sequencer, mode-register shadow, or output command FIFO. Until 2026-10-09 it was a pumice-local layer that bundled exactly those functions; the Phase-2 extraction moved that logic into the common `mc_scheduler_layer` in `projects/components/mem-ctrl-ip/common-ip/rtl/macro/`. What remains in pumice is the thin wrapper that supplies rock-specific children, adapts the pumice training channel to the common maintenance slot, and ties off unused common features.

The common scheduler microarchitecture is documented in [Chapter 4 of the common MAS](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md); the family layer-stack and descriptor-seam architecture are defined in the [common HAS](../../../../../common-ip/docs/common_has/common_has_index.md).

## What the wrapper adds

### Rock-specific children

| Instance | Module | Key parameters | Role |
|---|---|---|---|
| `u_init` | `init_sequencer` | `NUM_BANKS`, `ROW_WIDTH` | DDR2 + LPDDR2 JEDEC MRS init microprogram. Drives `dfi_init_start_o`, emits init commands into the common core, and writes the MR shadow. Gates traffic until `init_done_o`. |
| `u_mode_reg` | `mode_register` | `NUM_RANKS` | MR shadow updated by init writes; decodes `cl_o` / `cwl_o` / `bl_o` for the DFI layer. |
| `u_refresh` | `refresh_ctrl` | `NUM_BANKS` | `tREFI` down-counter, postpone/pull-in, and per-bank refresh-kind selection (enabled only after init). |
| `u_page_policy` | `pumice_page_policy` | `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH` | Runtime page-policy engine producing `ap_mode_en_o`, `ap_close_o`, `timeout_pre_req_o`, and `timeout_pre_bank_o`. |
| `u_cmd_history` | `pumice_cmd_history_checker` | `NUM_RANKS`, `NUM_BANKS`, timing windows | Optional JEDEC same-bank sequencing audit, generated only when `CMD_HISTORY_EN != 0`. |

### Maintenance-slot mapping

The pumice training layer presents one maintenance request at a time on `{trn_cmd_req_i, trn_cmd_op_i, trn_cmd_bank_i, trn_cmd_row_i, trn_cmd_mrr_i}` plus a `cal_busy_i` gate. The wrapper maps this onto the common `mc_scheduler_layer` generic maintenance slot:

- `maint_req_i`      ← `trn_cmd_req_i`
- `maint_op_i`       ← `trn_cmd_op_i`
- `maint_bank_i`     ← `trn_cmd_bank_i`
- `maint_row_i`      ← `trn_cmd_row_i`
- `maint_col_i`      ← `'0`
- `maint_extra_i[0]` ← `trn_cmd_mrr_i`
- `maint_busy_i`     ← `cal_busy_i`

The common core returns `maint_grant_o`; the wrapper forwards it as `trn_cmd_grant_o` and recovers the MRR flag as `cmd_mrr_o = cmd_extra_o[0]`. The common arbiter priority inside `mc_scheduler_layer` is init > refresh > maintenance > demand; see the [pumice training-layer chapter](05_training_layer_macro.md) and the [training interface contracts](../ch04_apb_config/05_training_interface_contracts.md).

### Tie-offs and constants

Because pumice is a DDR2/LPDDR2 single-rank rock, several common features are disabled or tied off:

- `NUM_BG = 1`; `t_ccd_l_i`, `t_ccd_s_i`, `t_rrd_l_i`, `t_rrd_s_i` are tied to `8'd0`; `cmd_bg_o` is left open.
- `HAS_ZQ = 1'b0`: `zq_req_i` is tied to `1'b0`, `t_zqcs_i` to `16'd0`, and `stall_zq_o` is left open. (ZQ calibration is handled by the pumice training layer, not the scheduler.)
- `MAINT_EXTRA_WIDTH = 1`: the single-bit MRR flag is the only maintenance extra payload.
- Page/policy telemetry is computed by `pumice_page_policy`, so the wrapper ties off the common core's `stat_*` outputs.
- `mode_register` unused rank/ODT/drive-strength outputs and the init sequencer's `zqcl_req_o`/`init_busy_o` are left open with their grant inputs tied low.

## External boundaries

- **CAM sched ports (to `pumice_axi4_layer`):** per-direction `N_LU = NUM_BANKS` lookup buses, `oldest_*` snapshots, and write `commit_*` / read `issue_*` handshakes.
- **Command stream out (to `mc_dfi_2p1_layer`):** `cmd_valid/ready` + `{mrr, ap, col, row, bank, rank, op}`.
- **Maintenance channel in (from `pumice_training_layer`):** `trn_cmd_req` + payload + `trn_cmd_grant` back.
- **Mode-register shadow out:** `cl_o` / `cwl_o` / `bl_o` to the DFI layer.
- **Init handshake:** `dfi_init_start_o` out and `dfi_init_complete_i` in (routed through the DFI layer); `init_done_o` status out.
- **Config in:** JEDEC timings, refresh/programming parameters, `page_policy_i`, `page_mode_i`, `page_tr_init_i`, and scheduler knobs — all delivered from the CSR by name.

`busy_o` is generated by the common core and asserts while not init-done, on a pending refresh, while a command is buffered in the FIFO, or while any bank row is active.

## Pumice integration details that stay

- **Single controller clock:** the wrapper and the common core run on `aclk`; the only controller-to-PHY crossing is inside `mc_dfi_2p1_layer`.
- **External CAMs:** the CAM sched-lookup / oldest / commit / issue ports remain external; the CAMs live in `pumice_axi4_layer`.
- **Training priority and gating:** demand commands are blocked while `cal_busy_i` is asserted and the training request obeys the init > refresh > training > demand priority cone.

## Tests

The common `mc_scheduler_layer` owns the macro-level tests for the pick machinery, bank/global timers, and command FIFO; see the [common MAS](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md). The pumice wrapper is covered by integration tests that exercise the training-channel mapping, init-sequencer handshake, and maintenance-slot priority against the common core.
