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

# Data path macro — `mc_storage_plane` instantiation

**Module:** `mc_storage_plane` (common IP)  
**Location:** `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_storage_plane.sv`  
**Category:** Plane-1b macro in `pumice_core`  
**Instance:** `u_store_plane` (`rtl/top/pumice_core.sv:504-596`)  
**Child FUBs:** `mc_wr_data_cam`, `mc_rd_cmd_cam`, `mc_addr_mapper`

## Purpose

"Schedulable entry pools and data buffers for writes and reads." `pumice_core` instantiates the common `mc_storage_plane` on `aclk` between `u_axi_plane` (`mc_axi4_plane`) and `u_sched_plane` (`pumice_scheduler_plane`). It holds the write-data CAM / write buffer and the read-command scheduling window, exposes the per-entry scheduler vectors, and streams committed write data toward the DFI plane.

Until 2026-10-09 the write-data and read-command CAMs lived inside the pumice-local `pumice_axi4_plane` and were documented as part of the AXI front-end macro; Phase-2 moved them into the common `mc_storage_plane`, and the old `data_path_macro` (`wr_beat_sequencer` + `rd_cl_aligner`) is retired.

## Parameter map in `pumice_core`

| Parameter | Bound value in `pumice_core` | Notes |
|-----------|------------------------------|-------|
| `AXI_ID_WIDTH` | `IW` | `IW = AXI_ID_WIDTH` (`pumice_core.sv:97`) |
| `AXI_DATA_WIDTH` | `DW` | `DW = DFI_DATA_WIDTH` (`pumice_core.sv:95`) |
| `NUM_RANKS` | `NUM_RANKS` | Passed through from core |
| `NUM_BANKS` | `NUM_BANKS` | Passed through from core |
| `ROW_WIDTH` | `ROW_WIDTH` | Passed through from core |
| `COL_WIDTH` | `COL_WIDTH` | Passed through from core |
| `AXI_BEATS_PER_BURST` | `BURST_WORDS` | DFI words per burst group (`pumice_core.sv:511`) |
| `NUM_ENTRIES` | `NUM_ENTRIES` | CAM / scheduling-window depth |
| `N_SRAM_SLOTS` | `N_SRAM_SLOTS` | Write-data SRAM slots |
| `N_SCHED_LU` | `N_LU` | `N_LU = NUM_BANKS` (`pumice_core.sv:103`) |
| `AGE_WIDTH` | `AGE_WIDTH` | Age-counter width |
| `RD_RET_DEPTH` | `RD_RET_DEPTH` | Return-ring depth / ticket space |

## External boundaries

- **From `mc_axi4_plane` (`u_axi_plane`):** the storage seam — `aw_push_*` + `wd_*` for writes, `snarf_probe_*` for read-your-write probes, `ar_push_*` for reads, and the return-ring ticket handshake (`rt_alloc_*`, `rd_iss_*`, `rd_cam_ins_ready_*`).
- **To `pumice_scheduler_plane` (`u_sched_plane`):** per-entry scheduling vectors (`wr_sch_*`, `rd_sch_*`), plus the write `commit` and read `issue` handshakes.
- **To `mc_dfi_2p1_plane` (`u_dfi_plane`):** committed write-data stream `wr_cm_rd_*` (`valid/ready/data/strb/last`).
- **Status:** `busy_o` is left unconnected in `pumice_core` (`pumice_core.sv:595`).

## Pumice-specific integration notes

**Gearing wrapper.** The storage plane operates on whole DFI words. `AXI_BEATS_PER_BURST` is bound to `BURST_WORDS`, so one AXI burst maps to one buffered CAM entry. Runtime sub-DFI-word packing (`N_SUBCMD > 1`) and the PHY serialization timing are handled in `mc_dfi_2p1_plane`; the CAMs see only the `BURST_WORDS` framing.

**Observed buses.** The buses visible at this plane are the storage-seam nets from `mc_axi4_plane`, the scheduler vectors / commit/issue ports, and the `wr_cm_rd_*` commit-data stream to the DFI plane. Returned read data enters through `mc_axi4_plane`'s `rd_dfi_ret_*` port, not directly through the storage plane.

**Backpressure thresholds.** Write commit data is staged so that it reaches the PHY before its command. The effective command-release delay is computed in `pumice_core` as

```systemverilog
localparam int CMD_DELAY_EFF = (CMD_DELAY == 0) ? (5 + 2 * BURST_WORDS) : CMD_DELAY;
```

Measured: BL8/4-word bursts held up to 6 cycles at `CMD_DELAY=6 -> 13`; BL4 x16 (1 word) needs 7 (`pumice_core.sv:273-275`). The DFI write-data FIFO is sized to 32 entries (`WD_FIFO_DEPTH = 32`, `pumice_core.sv:788`) to absorb that staging without stalling the CAM drain. The read-return FIFO is sized to `RD_RET_DEPTH * BURST_WORDS` entries (`pumice_core.sv:784`). Inside the common write-data CAM, `WR_DRAIN_AHEAD = 2` bounds how far the command stream can run ahead of the data drain; the common_mas chapter records that the old FIFO-room gate allowed a command to run ~20 `aclk` ahead and produced a measured 29373-cycle DFI hold.

`tCCD` is clamped to at least `BURST_WORDS` in `pumice_core` (`w_t_ccd_eff = (t_ccd_i < 8'(BURST_WORDS)) ? 8'(BURST_WORDS) : t_ccd_i`; `pumice_core.sv:281-282`) because the DFI command path no longer paces columns.

## Common-plane reference

For the common storage-plane architecture, CAM internals, address-mapper behavior, scheduling-vector layout, and complete port list, see [common_mas chapter 3: `mc_storage_plane`](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md).

## Tests

The common CAM FUB tests and the `mc_dfi_2p1_plane` FUB tests cover the datapath building blocks; `pumice_core` wrapper-level tests exercise the end-to-end buffered write and read data flow through the common planes.
