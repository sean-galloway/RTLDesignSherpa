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

# `data_path_macro`

**Module:** `data_path_macro.sv`
**Location:** `rtl/macro/`
**Category:** Integration macro (pure structural)
**Parent macro:** `ddr2_lpddr2_core_macro`
**FUBs bundled:** 2

## Purpose

"Move bytes between the host AXI buffers and the DFI data lanes."
Bundles the write-side beat sequencer and the read-side CL aligner.

## FUBs

| FUB                  | Role                                                                                                         |
|----------------------|--------------------------------------------------------------------------------------------------------------|
| `wr_beat_sequencer`  | Pull W beats from `axi_intake.w_buf` via beat_pull; pack DFI_RATE DRAM beats per DFI cycle; drive dfi_wrdata |
| `rd_cl_aligner`      | Drive dfi_rddata_en at t_rddata_en after RD; capture rddata; stream DRAM beats out as rd_inject handshakes   |

## External Boundaries

- **Host-AXI side**:
  - Consumes `w_buf` (beat_pull_*, wbuf_rd_data/strb)
  - Drives `b_complete` back to `wr_cmd_cam`
  - Drives `rd_inject_*` back to `axi_intake.R-emit`
  - Drives `rd_beat_we` back to `rd_cmd_cam` per accepted beat
- **Scheduler side**: op handshakes (wr_op_valid/ready/slot/len,
  rd_op_valid/ready/slot/id/len), live MR values (cl, cwl, al).
- **DFI side**: drives pre-pack `dfi_wrdata` / `dfi_wrdata_en` /
  `dfi_wrdata_mask` and `dfi_rddata_en`; receives `dfi_rddata` /
  `dfi_rddata_valid` from the PHY.

## Key Behavior

- **AXI ↔ DFI mask polarity**: AXI `wstrb=1` means write that byte; DFI
  `mask=1` means mask (do not write). `wr_beat_sequencer` inverts:
  `dfi_wrdata_mask = ~wstrb`.
- **CWL window**: `wr_beat_sequencer` aligns `dfi_wrdata_en` to be
  asserted `t_phy_wrlat` cycles after the WR command.
- **CL window**: `rd_cl_aligner` asserts `dfi_rddata_en` for the
  expected burst window, then waits for `dfi_rddata_valid` from the
  PHY.

## Tests

No macro-level test yet; each FUB has its own unit test
(`test_wr_beat_sequencer.py` 9 scenarios, `test_rd_cl_aligner.py` 10
scenarios).
