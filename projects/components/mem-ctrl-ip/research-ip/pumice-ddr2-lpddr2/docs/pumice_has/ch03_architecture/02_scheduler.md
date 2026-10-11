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

# Command Scheduler

The command-scheduling layer is `pumice_scheduler_layer` (`rtl/macro/pumice_scheduler_layer.sv`). It is a thin pumice wrapper around the common `mc_scheduler_layer` core. It runs on the single controller clock (`aclk`), instantiates the rock-specific bring-up and policy children, and emits one abstract DRAM command stream `{op, rank, bank, row, col, ap, mrr}` into the scheduler-to-DFI command interface.

Until 2026-10-09 this block was a pumice-local layer that contained `pumice_cmd_arbiter`, `pumice_bank_timers`, and `global_timers`; the pick machinery and timing FUBs were extracted into the common core during the Phase-2 common-IP campaign. The wrapper now holds only the DDR2/LPDDR2-specific children and the port mapping that feeds the common core.

The wrapper does not hold the transaction queue. The schedulable-entry vectors (valid, bank, row, col, age, oldest, qos) and the commit/issue handshakes are external because the CAMs live in `mc_storage_layer`; `pumice_axi4_layer` presents the same descriptor seam in the pumice build. The family layer-stack and descriptor-seam contract are in the family HAS ([Layer Stack](../../../../../common-ip/docs/common_has/ch02_architecture/01_layer_stack.md), [Descriptor Seam](../../../../../common-ip/docs/common_has/ch02_architecture/02_descriptor_seam.md)). The common scheduler core is documented in the family MAS ([`mc_scheduler_layer`](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md)); this chapter only describes the pumice wrapper, its rock-specific children, and the measured history that remains pumice-owned.

## Composition

`pumice_scheduler_layer` instantiates:

- `init_sequencer` — JEDEC MRS cold-boot init; gates traffic until done (see `05_init_power.md`).
- `mode_register` — CL / CWL / BL decode shadow, updated by init MRS writes.
- `refresh_ctrl` — tREFI tracking + postpone/pull-in accumulator (see `04_refresh.md`).
- `pumice_page_policy` — runtime auto-precharge engine.
- `pumice_cmd_history_checker` (optional, `CMD_HISTORY_EN != 0`) — command-history scoreboard for simulation.
- `mc_scheduler_layer` — the common core that owns the pick machinery, bank/global timers, maintenance arbitration, and scheduler-to-DFI command FIFO.

The wrapper passes the timing and scheduler CSR inputs straight through to the common core and forwards the page-policy outputs (`ap_mode_en`, `ap_close`, `timeout_pre_req`, `timeout_pre_bank`) to the core's page-policy engine interface.

## Mapping the pumice training channel onto the generic maintenance slot

The common core exposes one generic maintenance slot: `maint_req_i`/`maint_grant_o`, `maint_op_i`, `maint_bank_i`, `maint_row_i`, `maint_col_i`, `maint_extra_i`, `maint_busy_i`. Pumice maps its training-channel signals onto that slot:

| Pumice signal | Common maintenance slot |
|---|---|
| `trn_cmd_req_i` | `maint_req_i` |
| `trn_cmd_grant_o` | `maint_grant_o` (via `w_maint_grant`) |
| `trn_cmd_op_i` | `maint_op_i` |
| `trn_cmd_bank_i` | `maint_bank_i` |
| `trn_cmd_row_i` | `maint_row_i` |
| `trn_cmd_mrr_i` | `maint_extra_i[0]` |
| `cal_busy_i` | `maint_busy_i` |

The single-bit `mrr` flag is carried in `maint_extra_i[0]` and recovered on the command output as `cmd_mrr_o = cmd_extra_o[0]`. No training logic is implemented inside the common core; the slot is a request/grant pipe that the wrapper's `pumice_training_layer` drives (see `09_training.md`).

## Rock-specific children and CSR surface

`init_sequencer`, `mode_register`, and `refresh_ctrl` remain rock-specific because the DDR2/LPDDR2 bring-up sequence, mode-register fields, and refresh policy differ from the other family rocks. `pumice_page_policy` is the pumice runtime page-policy engine; it consumes the `page_mode_i`/`page_tr_init_i` CSRs and produces the auto-precharge controls consumed by the common core.

The static page-policy override `page_policy_i` (OPEN / CLOSE / HAPPY_HYBRID) is still accepted at the wrapper top level; the common core honors it when the runtime engine is disabled. The `HAPPY_HYBRID` enum encoding and the standalone `page_predictor.sv` are retired; the encoding maps to the build default. The adaptive modes `adapt_time` and `adapt_access` were RETIRED 2026-09-27, TASK-014.

## Measured history preserved in the common pick machinery

Pumice does not alter the common `mc_cmd_arbiter` pick core. The following measured bug-history sentences from the merge inventory ([mc_scheduler_knobs.md](../../../../../common-ip/docs/mc_scheduler_knobs.md) §6.4) are preserved verbatim because they govern the fire-stage authority that this wrapper relies on:

- **pumice BUG-021**: dropping an ACT whose only obstacle was the rank-global tFAW/tRRD window regressed close-page throughput from the accepted 30.77% calibration to 28.57%; holding recovered to 30.14%.
- **ISSUE-002**: moving tFAW/tRRD to the classify mask drained the 3-stage pipeline and dropped close-page throughput from 30.77% to ~18%.

The common MAS chapter lists the remaining fire-stage invariants (scoria BUG-001, BUG-002 / tZQCS, the one-cycle blind spot, and the parked-victim PRE guard) and their line-level RTL evidence.

## v1 Scope Notes

The common core is instantiated with `NUM_RANKS = 1` in the pumice wrapper; multi-rank pick remains a future exercise. Write-batch watermarking is now passed through the `sched_wr_high_wm_i`/`sched_wr_batch_max_i`/`sched_wr_low_wm_i` CSRs into the common core. Power-down coordination is not implemented in this wrapper; it is documented as a TODO in `05_init_power.md`.
