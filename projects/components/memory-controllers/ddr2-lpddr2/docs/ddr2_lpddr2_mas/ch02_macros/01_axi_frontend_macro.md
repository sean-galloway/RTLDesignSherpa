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

# `axi_frontend_macro`

**Module:** `axi_frontend_macro.sv`
**Location:** `rtl/macro/`
**Category:** Integration macro (pure structural)
**FUBs bundled:** 5

## Purpose

"Host AXI4 → CAM-cached requests." The single macro the SoC presents to
the AXI master. Sits alongside `ddr2_lpddr2_core_macro` rather than
inside it, so a different DFI-version controller can reuse this macro
unchanged.

## FUBs

| FUB                | Role                                                                                                |
|--------------------|-----------------------------------------------------------------------------------------------------|
| `axi_intake`       | AXI4 slave protocol engine; w_buf for write data; b_fifo for ID-ordered completion; R-emit FSM      |
| `addr_mapper`      | Flat AXI address → (rank, bank, row, col) via the active address-mapping scheme                     |
| `wr_cmd_cam`       | Per-write-op slot bank (rank, bank, row, len, w_buf_ptr, b_complete state)                          |
| `rd_cmd_cam`       | Per-read-op slot bank (rank, bank, row, len, beats remaining)                                       |
| `wr2rd_forward`    | Snarf-and-bypass for AR that hits an in-flight write's staged data                                  |

## External Boundaries

- **Upstream**: AXI4 slave port (the SoC-facing interface).
- **Downstream to `command_scheduler_macro`**: CAM match-query buses
  (wr/rd_match_*), snapshot metadata (q_rank/q_bank/q_row/q_len),
  mark-issued strobes (wr/rd_issued_*).
- **Downstream to `ddr2_lpddr2_core_macro`** *(via the system top)*:
  per-slot snapshot ports including `rd_snap_id_o`, the AR's AXI ID
  echo. The core's `rd_op_id` lookup indexes this with the
  scheduler's `cmd_rd_slot`, so the R-channel response carries the
  originating AR's id. Must not be dropped at the macro boundary —
  see `04_rd_cmd_cam.md` for the consequence of tying it to 0.
- **Downstream to `data_path_macro`**: w_buf pull port (beat_pull_*,
  wbuf_rd_data/strb), rd_inject port (rd_inject_valid/data/last).
- **Internal**: rd_beat_we from `rd_cl_aligner` retires rd CAM slots;
  b_complete from `wr_beat_sequencer` retires wr CAM slots.

## Tests

`dv/tests/macro/test_axi_frontend_macro.py` — 11 integration scenarios
covering smoke, streaming reads/writes, snarf paths, ID ordering,
CAM-full backpressure, lifecycle, and multi-rank.
