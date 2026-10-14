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

# Pumice DFI v2.1 interface (`mc_dfi_2p1_plane`)

**Module:** `mc_dfi_2p1_plane` (common IP)
**Location:** `common-ip/rtl/macro/`
**Category:** Plane-3 PHY-facing plane, instantiated directly in `pumice_core`

## Purpose

`pumice_core` consumes the common `mc_dfi_2p1_plane` directly; there is no pumice-specific DFI wrapper. The common plane translates the controller-clock command, write-data, and read-data streams into DFI v2.1 pins and holds the single controller-to-PHY clock-domain crossing.

Until 2026-10-09 pumice used a local `mc_dfi_cmd_path` / `mc_dfi_cdc` / `mc_dfi_wr_serializer` / `mc_dfi_rd_aligner` stack, corresponding to the old `dfi_v21_interface_macro`; the Phase-2 extraction moved that logic into `mc_dfi_2p1_plane`.

The common DFI 2.1 microarchitecture is documented in [Chapter 7 of the common MAS](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md); the family plane-stack and descriptor-seam architecture are defined in the [common HAS](../../../../../common-ip/docs/common_has/common_has_index.md).

## Pumice integration details

### Instantiation in `pumice_core`

`pumice_core` instantiates `mc_dfi_2p1_plane` as `u_dfi_plane` (`rtl/top/pumice_core.sv:803-873`). The parameters pumice supplies are:

| Parameter | Pumice value / source | Purpose |
|---|---|---|
| `NUM_RANKS` | `NUM_RANKS` | CS/rank fan-out |
| `NUM_BANKS` | `NUM_BANKS` | Bank count |
| `ROW_WIDTH` / `COL_WIDTH` | top-level params | Address widths |
| `DFI_RATE` | top-level param | Compile-time phase count |
| `DRAM_BEAT_WIDTH` | top-level param | One DRAM beat data width |
| `DFI_BEATS_PER_BURST` | `BL_PUMICE` | DRAM beats mapped to one DFI word |
| `N_SUBCMD` | derived | Sub-column commands packed per DFI word |
| `SUB_COL_STRIDE` | `DRAM_BL` | Column stride between packed sub-bursts |
| `SUB_PHASE_STRIDE` | derived | Phase stride between packed sub-bursts |
| `SUBW_MAX` | derived | Width holding `N_SUBCMD` |
| `BURST_WORDS` | derived | DFI words per burst group |
| `RD_MAX_OUTSTANDING` | `RD_RET_DEPTH` | Aligner outstanding-read depth |
| `RD_FIFO_DEPTH` | `RD_RET_DEPTH * BURST_WORDS` | Read-return CDC FIFO depth |
| `WD_FIFO_DEPTH` | `32` | Write-data CDC FIFO depth |
| `CMD_HISTORY_EN` / `HIST_T_*` | top-level params | DFI-wire command-history audit |

The controller-side clock and reset are wired to `aclk` and `aresetn`; the PHY side uses `dfi_clk` and `dfi_rstn`. The abstract command stream comes from `mc_scheduler_plane`; write data comes from the write CAM in `mc_storage_plane`, and read returns go to the return ring in `mc_axi4_plane`.

### Generation FUBs inside the plane

The common `mc_dfi_cmd_path` instantiates `mc_xddr2_cmd_formatter` (`common-ip/rtl/fub/mc_xddr2_cmd_formatter.sv`), the DDR2/LPDDR2-generation formatter that used to be pumice's `dfi_cmd_formatter`, to place the JEDEC command on the selected DFI phase. Its registered outputs drive the pins directly; the legacy `dfi_signal_pack` relatch stage was removed on 2026-10-11.

### PHY timing programming

The PHY-integration knobs are programmed through the `PHY_TIMING` and `DFI_PHASE` CSRs:

| Knob | CSR / bits | Measured pumice value |
|---|---|---|
| `t_phy_wrlat_i` | `PHY_TIMING` 7:0 | 1 on Nexys A7 a7ddrphy ([CSR map](../ch04_apb_config/02_csr_map.md)) |
| `t_rddata_en_i` | `PHY_TIMING` 15:8 | 6 on Nexys A7 a7ddrphy ([CSR map](../ch04_apb_config/02_csr_map.md)) |
| `rd_phase_i` / `wr_phase_i` | `DFI_PHASE` | 0 / 0 on Nexys A7 ([error-handling chapter](../ch05_programming/04_error_handling.md)) |

These are not datapath constants; pumice is the measured customer (Nexys A7, 66.67 / 75 MHz). The board-validated tuple (2026-07-21) is `rd_phase=0`, `t_rddata_en=6`, `t_phy_wrlat=1`, plus harness `DFI_TUNING.rddata_delay=7` ([runtime overrides](../ch04_apb_config/03_runtime_overrides.md)).

### CDC clocking

The single controller↔PHY crossing is inside `mc_dfi_2p1_plane` and uses async `gaxi_fifo_async` FIFOs for command, write-data, and read-data, plus token crossings for `init_start` and `init_complete`. `pumice_core` does not add a second crossing.

## Tests

Unit tests for the common CDC, command path, write serializer, and read aligner live in `common-ip`; the pumice integration is exercised by the `pumice_core` plane-level test against the DFI slave BFM.
