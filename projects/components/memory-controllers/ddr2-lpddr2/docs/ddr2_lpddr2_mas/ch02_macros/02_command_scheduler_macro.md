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

# `command_scheduler_macro`

**Module:** `command_scheduler_macro.sv`
**Location:** `rtl/macro/`
**Category:** Integration macro (pure structural)
**Parent macro:** `ddr2_lpddr2_core_macro`
**FUBs bundled:** 7

## Purpose

"What command should we issue this cycle?" — bundles all the
decision-making layer of the controller core: scheduler + per-bank /
global timers + refresh + powerdown + mode register + init sequencer.

## FUBs

| FUB                | Role                                                                                                |
|--------------------|-----------------------------------------------------------------------------------------------------|
| `scheduler`        | FR-FCFS-style picker. Closed-page policy (RDA/WRA auto-precharge). Refresh + init priority gating.  |
| `xbank_timers`     | Per-(rank, bank) JEDEC counters (tRCD, tRP, tWR, tRTP, tRC, tRAS). Drives per-bank ready arrays.    |
| `global_timers`    | Cross-bank windows: tFAW (4-ACT), tRRD, tWTR, tRTW. Drives per-rank `_window_ok` flags.             |
| `refresh_ctrl`     | tREFI down-counter + postponed-refresh accumulator (JEDEC max 8). `refresh_pending_o` to scheduler. |
| `powerdown_ctrl`   | Active / APD / SR / DPD FSM; per-rank CKE drive; SR coordination with `refresh_ctrl`.               |
| `mode_register`    | MR0/1/2/3 shadow + live decode → CL / CWL / BL / AL / drv_strength / ODT.                           |
| `init_sequencer`   | Cold-boot microprogram; step table per `MEMTYPE`; drives MR-write strobes into `mode_register`.     |

## External Boundaries

- **Upstream from `axi_frontend_macro`**: CAM query + match buses,
  snap_* metadata.
- **Downstream to `dfi_v21_interface_macro`**: cmd_* channel (op, rank,
  bank, row, col, len, ap_bit).
- **Downstream to `data_path_macro`**: cmd_op + cmd_wr_slot / cmd_rd_slot
  + live MR values (cl, cwl, al).
- **mark-issued back to CAMs**: wr/rd_issued strobes after the scheduler
  issues a column command for that slot.

## Tests

No macro-level integration test exists for this macro yet; each
constituent FUB has its own unit test (98 tests total in
`dv/tests/fub/`).
