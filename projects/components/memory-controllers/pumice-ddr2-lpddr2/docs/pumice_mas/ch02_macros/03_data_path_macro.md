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

# Data Path (no standalone macro)

**Category:** Distributed across `pumice_axi4_ifc` and `pumice_dfi_layer`
**Status:** the old `data_path_macro` (`wr_beat_sequencer` + `rd_cl_aligner`) is
retired -- there is no `data_path_macro.sv` in the live tree.

## Purpose

"Move bytes between the host AXI buffers and the DFI data lanes." In the
rearchitected core this is **not a separate macro**. The data path is split
across two of the three core layers:

- The **burst buffers** live in the two CAMs inside `pumice_axi4_ifc`
  (section 2.1). Write data is buffered in `pumice_wr_data_cam`'s SRAM; read
  return data is buffered in `pumice_rd_cmd_cam`'s SRAM. Both use de-FSM'd
  streaming read engines rather than a beat-sequencer FSM.
- The **DFI-clock serialize / align** stages live in `pumice_dfi_layer`
  (section 2.4): `pumice_dfi_wr_serializer` presents write data on
  `dfi_wrdata` at `t_phy_wrlat`, and `pumice_dfi_rd_aligner` captures
  `dfi_rddata` at `t_rddata_en` and reassembles DFI words.

The controller-to-PHY data crossing is carried as whole DFI words through the
single CDC in `pumice_dfi_layer` (section 1.3), so there is no separate
data-path clock boundary to describe.

## Write Path (host -> DRAM)

1. `pumice_wr_intake` streams W beats (DFI-word granular `{data, strb, last}`)
   into `pumice_wr_data_cam`'s SRAM; `r_fdone` marks the burst fully filled.
2. When the scheduler commits the write slot, the CAM's **commit-drain mover**
   streams the burst out on the `wr_cm_rd_*` port (`data/strb/last`) into the
   DFI layer's write FIFO.
3. `pumice_dfi_wr_serializer` (on `dfi_clk`) drives `dfi_wrdata` /
   `dfi_wrdata_en` / `dfi_wrdata_mask` at `t_phy_wrlat` after the WR fire strobe
   from the command path. AXI `wstrb = 1` (write this byte) maps to the DFI mask
   as-carried by the CAM strobe payload.

The write CAM's SRAM is also the **snarf source** (read-your-write forwarding):
`pumice_rd_intake` probes it and, on a hit, streams the R response straight from
the write SRAM without a DRAM round-trip.

## Read Path (DRAM -> host)

1. When the scheduler issues the read slot, `pumice_dfi_rd_aligner` (on
   `dfi_clk`) drives `dfi_rddata_en` at `t_rddata_en` after the RD fire strobe,
   captures `dfi_rddata` when `dfi_rddata_valid` asserts, and packs whole DFI
   words (`{data, resp, last}`) into the read FIFO.
2. The FIFO crosses to `aclk` (the single CDC) and lands as the `dfi_ret_*`
   stream into `pumice_rd_cmd_cam`'s **return-fill mover**, which writes the
   read SRAM.
3. The CAM's **drain mover** streams the buffered burst out oldest-first,
   gated on data-ready, back through `pumice_rd_intake` to the AXI R channel.

## Why No Beat-Sequencer FSM

The old `wr_beat_sequencer` / `rd_cl_aligner` FUBs carried an active/slot state
latch and per-beat control FSM. The live CAMs replace that with FIFO-fed /
oldest-pick beat counters and a `r_fdone` fill flag -- fewer control-path
hazards and a cleaner streaming shape. The only genuinely PHY-timed logic
(`t_phy_wrlat` / `t_rddata_en` alignment) is the small serializer / aligner pair
in the DFI layer.

## Tests

Covered by the CAM FUB tests and the DFI-layer FUB tests
(`pumice_dfi_wr_serializer`, `pumice_dfi_rd_aligner`) in `dv/tests/fub/`, plus
the `pumice_axi4_ifc` wrapper test for the end-to-end buffered data flow.
