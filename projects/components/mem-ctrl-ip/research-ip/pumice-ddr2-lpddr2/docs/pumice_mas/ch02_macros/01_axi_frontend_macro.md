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

# AXI front-end macro — `mc_axi4_plane` instantiation

**Module:** `mc_axi4_plane` (common IP)  
**Location:** `projects/components/mem-ctrl-ip/common-ip/rtl/macro/mc_axi4_plane.sv`  
**Category:** Plane-1 macro in `pumice_core`  
**Instance:** `u_axi_plane` (`rtl/top/pumice_core.sv:376-499`)  
**Child FUBs:** `mc_wr_splitter`, `mc_axi_burst_chopper`, `mc_wr_intake`, `mc_rd_intake`, `mc_rd_return_ring`

## Purpose

"Host AXI4 to storage-plane descriptors and the read-return ring." `pumice_core` instantiates the common `mc_axi4_plane` on `aclk` as the SoC-facing AXI4 slave boundary. It splits host bursts into DFI-word-sized sub-commands, pushes write and read descriptors to `mc_storage_plane`, sources read-your-write snarf data from the write-data CAM, and forwards the DFI read-return stream to the read path.

Until 2026-10-09 the pumice MAS described a pumice-local `pumice_axi4_plane` macro (`rtl/macro/pumice_axi4_plane.sv`) that bundled the splitters, intakes, write-data CAM, and read-command CAM; Phase-2 extracted the shared logic into the common `mc_axi4_plane` and `mc_storage_plane`, and the pumice-local module no longer exists.

## Parameter map in `pumice_core`

| Parameter | Bound value in `pumice_core` | Notes |
|-----------|------------------------------|-------|
| `AXI_ID_WIDTH` | `IW` | `IW = AXI_ID_WIDTH` (`pumice_core.sv:97`) |
| `AXI_ADDR_WIDTH` | `AW` | `AW = AXI_ADDR_WIDTH` (`pumice_core.sv:98`) |
| `AXI_DATA_WIDTH` | `DW` | `DW = DFI_DATA_WIDTH` (`pumice_core.sv:95`); one AXI beat == one DFI word |
| `AXI_USER_WIDTH` | `UW` | `UW = 1` (`pumice_core.sv:99`) |
| `DRAM_BEAT_WIDTH` | `DW` | Intentionally set to the AXI/DFI word width, not the physical DRAM beat width (`pumice_core.sv:385`) |
| `NUM_RANKS` | `NUM_RANKS` | Passed through from core |
| `NUM_BANKS` | `NUM_BANKS` | Passed through from core |
| `ROW_WIDTH` | `ROW_WIDTH` | Passed through from core |
| `COL_WIDTH` | `COL_WIDTH` | Passed through from core |
| `BYTE_OFFSET_WIDTH` | `BYTE_OFFSET_WIDTH` | Passed to the common address mapper |
| `AXI_BEATS_PER_BURST` | `BURST_WORDS` | DFI words per burst group (`pumice_core.sv:391`); sub-DFI-word expansion is handled downstream |
| `NUM_ENTRIES` | `NUM_ENTRIES` | Scheduler/storage entry count |
| `N_SRAM_SLOTS` | `N_SRAM_SLOTS` | `= NUM_ENTRIES` by default |
| `RD_RET_DEPTH` | `RD_RET_DEPTH` | In-flight read count (return-ring depth) |
| `N_SCHED_LU` | `N_LU` | `N_LU = NUM_BANKS` (`pumice_core.sv:103`) |
| `AGE_WIDTH` | `AGE_WIDTH` | Free-running age width |

## External boundaries

- **Upstream:** the host AXI4 slave port (`s_axi_*`), the only SoC-facing interface.
- **To `mc_storage_plane` (`u_store_plane`):** the storage seam — `aw_push_*` + `wd_*` for writes, `snarf_probe_*` / `snarf_rd_*` for read-your-write, `ar_push_*` for reads, and the return-ring ticket ports (`rt_alloc_*`, `rd_iss_*`, `rd_cam_ins_ready_*`).
- **From `mc_dfi_2p1_plane` (`u_dfi_plane`):** the read-return stream `rd_dfi_ret_*` (`valid/ready/data/resp/last`).
- **Status:** `busy_o` is left unconnected in `pumice_core` (`pumice_core.sv:498`).

## Pumice-specific integration notes

**Gearing wrapper.** The AXI4 plane is built for the compile-time maximum DFI word width and does not know `gear_i` or `bl_i` directly. It frames one AXI beat per DFI word and passes `AXI_BEATS_PER_BURST = BURST_WORDS`. Runtime sub-DFI-word burst packing (`N_SUBCMD > 1`) is expanded later in `mc_dfi_2p1_plane` (`pumice_core.sv:803-873`).

**Observed buses.** The signals observed at this plane are the host AXI4 channels, the `mc_storage_plane` storage-seam nets, and the `rd_dfi_ret_*` stream from the DFI plane. No pumice-local CAM or datapath buses exist here anymore.

**Backpressure thresholds.** Write and read acceptance is gated by `mc_storage_plane` ready signals, not by local FIFOs. Read allocation is additionally gated by the return ring (`ar_push_ready_o = rd_cam_ins_ready_o && rt_alloc_ready_i` inside `mc_storage_plane`; see the common plane documentation). The DFI-side read-return FIFO is sized in `mc_dfi_2p1_plane` as `RD_RET_DEPTH * BURST_WORDS` entries (`pumice_core.sv:821`).

## Common-plane reference

For the common plane architecture, child-instance map, burst-chop/split semantics, read-return-ring ordering contract, and complete port list, see [common_mas chapter 2: `mc_axi4_plane`](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md).

## Tests

Wrapper-level tests drive `pumice_core` through the AXI4 BFMs (`AXI4MasterWrite` / `AXI4MasterRead` + `AXI4Sequence`). The underlying `mc_axi4_plane` FUBs are covered by the common unit tests referenced in the common_mas chapter.
