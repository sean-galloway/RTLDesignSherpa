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

The command-scheduling plane is the common `mc_scheduler_plane` (`common-ip/rtl/macro/mc_scheduler_plane.sv`), instantiated directly by `pumice_core` as `u_sched_plane` (`rtl/top/pumice_core.sv:601`). It runs on the single controller clock (`aclk`), builds its default DDR2/LPDDR2 bring-up and policy children, and emits one abstract DRAM command stream `{op, rank, bank, row, col, ap, mrr}` into the scheduler-to-DFI command interface.

Until 2026-10-09 this block was a pumice-local plane that contained `pumice_cmd_arbiter`, `pumice_bank_timers`, and `global_timers`; the pick machinery and timing FUBs were extracted into the common core during the Phase-2 common-IP campaign, and a thin `pumice_scheduler_plane` wrapper kept the DDR2/LPDDR2 children. On 2026-10-11 those children moved into common-ip as well and the wrapper was removed. Pumice now selects its scheduler purely by parameter.

The plane does not hold the transaction queue. The schedulable-entry vectors (valid, bank, row, col, age, oldest, qos) and the commit/issue handshakes are external because the CAMs live in `mc_storage_plane`. The family plane-stack and descriptor-seam contract are in the family HAS ([Plane Stack](../../../../../common-ip/docs/common_has/ch02_architecture/01_plane_stack.md), [Descriptor Seam](../../../../../common-ip/docs/common_has/ch02_architecture/02_descriptor_seam.md)). The scheduler plane itself is documented in the family MAS ([`mc_scheduler_plane`](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md)); this chapter only describes how pumice configures and connects it, and the measured history that remains pumice-owned.

## Composition

`pumice_core` leaves the `HAS_*` child selectors at their defaults, so `mc_scheduler_plane` builds:

- `mc_xddr2_init_sequencer` (`HAS_INIT_SEQUENCER = 1`) — JEDEC MRS cold-boot init; gates traffic until done (see `05_init_power.md`).
- `mc_xddr2_mode_register` (`HAS_MODE_REGISTER = 1`) — CL / CWL / BL decode shadow, updated by init MRS writes.
- `mc_xddr2_refresh_ctrl` (`HAS_REFRESH_CTRL = 1`) — tREFI tracking + postpone/pull-in accumulator (see `04_refresh.md`).
- `mc_page_policy` (`HAS_PAGE_POLICY = 1`) — runtime auto-precharge engine.
- `mc_bank_timers`, `mc_global_timers` and `mc_cmd_arbiter` — the pick machinery and JEDEC timers.
- `gaxi_fifo_sync` — the scheduler-to-DFI command FIFO.

`HAS_CMD_HISTORY` is left at 0, so the scheduler-side `mc_cmd_history_checker` is not built in pumice; the `CMD_HISTORY_EN` knob arms the DFI-wire checker inside `mc_dfi_cmd_path` instead (Ch 3.6). Because the children are built in, `pumice_core` ties the plane's external init / refresh / page-policy override inputs off (`init_done_i = 1`, `refresh_req_i = 0`, `ap_mode_en_i = 0`, ...); they exist for products that supply their own children. The timing and scheduler CSR inputs come straight from `pumice_top`'s CSR block.

## Mapping the training channel onto the generic maintenance slot

The scheduler plane exposes one generic maintenance slot: `maint_req_i`/`maint_grant_o`, `maint_op_i`, `maint_bank_i`, `maint_row_i`, `maint_col_i`, `maint_extra_i`, `maint_busy_i`. `pumice_core` wires the `mc_training_plane` command channel onto that slot:

| Training plane signal | Scheduler maintenance slot |
|---|---|
| `trn_cmd_req_o` | `maint_req_i` |
| `trn_cmd_grant_i` | `maint_grant_o` |
| `trn_cmd_op_o` | `maint_op_i` |
| `trn_cmd_bank_o` | `maint_bank_i` |
| `trn_cmd_row_o` | `maint_row_i` |
| (tied `'0`) | `maint_col_i` |
| `trn_cmd_mrr_o` | `maint_extra_i[0]` |
| `cal_busy_o` | `maint_busy_i` |

The single-bit `mrr` flag is carried in `maint_extra_i[0]` and recovered on the command output as `cmd_extra_o`, which `pumice_core` packs into the command word as `w_cmd_mrr`. No training logic is implemented inside the scheduler plane; the slot is a request/grant pipe that `mc_training_plane` drives (see `09_training.md`).

## DDR2/LPDDR2 children and CSR surface

`mc_xddr2_init_sequencer`, `mc_xddr2_mode_register`, and `mc_xddr2_refresh_ctrl` are the DDR2/LPDDR2-generation children (`xddr2`); other family products disable them with the `HAS_*` parameters and supply their own. `mc_page_policy` is the runtime page-policy engine; it consumes the `page_mode_i`/`page_tr_init_i` CSRs and produces the auto-precharge controls consumed by `mc_cmd_arbiter`.

The static page-policy override `page_policy_i` (OPEN / CLOSE / HAPPY_HYBRID) is still accepted at the plane's top level; the arbiter honors it when the runtime engine is disabled. The `HAPPY_HYBRID` enum encoding and the standalone `page_predictor.sv` are retired; the encoding maps to the build default. The adaptive modes `adapt_time` and `adapt_access` were RETIRED 2026-09-27, TASK-014.

## Measured history preserved in the common pick machinery

Pumice does not alter the common `mc_cmd_arbiter` pick core. The following measured bug-history sentences from the merge inventory ([mc_scheduler_knobs.md](../../../../../common-ip/docs/mc_scheduler_knobs.md) §6.4) are preserved verbatim because they govern the fire-stage authority that pumice relies on:

- **pumice BUG-021**: dropping an ACT whose only obstacle was the rank-global tFAW/tRRD window regressed close-page throughput from the accepted 30.77% calibration to 28.57%; holding recovered to 30.14%.
- **ISSUE-002**: moving tFAW/tRRD to the classify mask drained the 3-stage pipeline and dropped close-page throughput from 30.77% to ~18%.

The common MAS chapter lists the remaining fire-stage invariants (scoria BUG-001, BUG-002 / tZQCS, the one-cycle blind spot, and the parked-victim PRE guard) and their line-level RTL evidence.

## v1 Scope Notes

The scheduler plane is built with `pumice_core`'s `NUM_RANKS` (default 1); multi-rank pick remains a future exercise. Write-batch watermarking is passed through the `sched_wr_high_wm_i`/`sched_wr_batch_max_i`/`sched_wr_low_wm_i` CSRs into the plane. Power-down coordination is not implemented; it is documented as a TODO in `05_init_power.md`.
