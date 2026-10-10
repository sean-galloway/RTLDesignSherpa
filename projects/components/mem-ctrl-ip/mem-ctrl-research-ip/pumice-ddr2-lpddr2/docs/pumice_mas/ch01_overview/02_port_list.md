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

# Top-Level Port List

This chapter is the **wire-level** port list of the `pumice_top` module
(`rtl/top/pumice_top.sv`) -- the exact signal names, directions, widths, and
parameter dependencies that the integration script and SoC top-level use. The
optional host-width wrapper `pumice_top_geared` re-exports the same set with a
free `HOST_AXI_DATA_WIDTH` on the AXI slave face; see
`docs/AXI_DRAM_GEARING_SCOPE.md`.

## Parameters

`pumice_top` is fully parameterized -- there is no `MEMTYPE`/`N_PHASES` string
build any more; memory type is a runtime CSR field (`PHY_TIMING.memtype`) and
the phase count is the integer `DFI_RATE`.

```systemverilog
module pumice_top #(
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int BL              = 8,   // DRAM beats per burst
    parameter int NUM_ENTRIES     = 8,   // CAM depth
    parameter int N_SRAM_SLOTS    = 8,   // per-CAM burst-data SRAM slots
    parameter int CSR_ADDR_W      = 12
);
```

## Parameter-Dependent Widths

Derived locally in the module (see `rtl/top/pumice_top.sv`):

- `DW`              = `DRAM_BEAT_WIDTH * DFI_RATE`  (host AXI data width == DFI word)
- `SW`              = `DW/8`
- `IW`              = `AXI_ID_WIDTH`
- `AW`              = `AXI_ADDR_WIDTH`
- `PHW`             = `(DFI_RATE > 1) ? $clog2(DFI_RATE) : 1`
- `DFI_DATA_WIDTH`  = `DW`
- `DFI_STRB_WIDTH`  = `DW/8`
- `DFI_EN_WIDTH`    = `DFI_RATE`
- `DFI_VALID_WIDTH` = `DFI_RATE`
- `DFI_ADDR_BUS_W`  = `ROW_WIDTH * DFI_RATE`
- `DFI_BANK_BUS_W`  = `$clog2(NUM_BANKS) * DFI_RATE`
- `DFI_CTRL_BUS_W`  = `1 * DFI_RATE`
- `DFI_CS_BUS_W`    = `NUM_RANKS * DFI_RATE`

## Clocks and Reset

Two clocks, two active-low resets. There is no APB CSR clock -- the register
block runs on `aclk` via a passthrough cpuif.

| Port        | Dir | Width | Domain    | Notes                             |
|-------------|-----|-------|-----------|-----------------------------------|
| `aclk`      | in  | 1     | `aclk`    | Host AXI + CAMs + scheduler       |
| `aresetn`   | in  | 1     | `aclk`    | Active-low async reset            |
| `dfi_clk`   | in  | 1     | `dfi_clk` | DFI datapath + PHY pin bus        |
| `dfi_rstn`  | in  | 1     | `dfi_clk` | Active-low async reset            |
| `init_done_o` | out | 1   | `aclk`    | Init sequencer done (STATUS)      |

## Register cpuif (PeakRDL passthrough)

The register block `pumice_csr` is generated from `rtl/macro/pumice_csr.rdl`
(via `bin/peakrdl_generate.py`). The top presents the raw PeakRDL passthrough
cpuif -- an SoC bridges its APB/AXI-Lite onto these signals.

| Port                    | Dir | Width          |
|-------------------------|-----|----------------|
| `s_cpuif_req`           | in  | 1              |
| `s_cpuif_req_is_wr`     | in  | 1              |
| `s_cpuif_addr`          | in  | `CSR_ADDR_W`   |
| `s_cpuif_wr_data`       | in  | 32             |
| `s_cpuif_wr_biten`      | in  | 32             |
| `s_cpuif_req_stall_wr`  | out | 1              |
| `s_cpuif_req_stall_rd`  | out | 1              |
| `s_cpuif_rd_ack`        | out | 1              |
| `s_cpuif_rd_err`        | out | 1              |
| `s_cpuif_rd_data`       | out | 32             |
| `s_cpuif_wr_ack`        | out | 1              |
| `s_cpuif_wr_err`        | out | 1              |

All config (timings, DFI phases, page policy, address map) is programmed
through this bus by name via the generated `dv/tbclasses/pumice_regmap.py`;
`pumice_top` fans `hwif_out.*` into `pumice_core`'s config ports. See section 4
of this MAS (or the RDL) for the register map.

## AXI4 Slave Port List

Standard AXI4 slave, single ID width `IW`, data width `DW` (= DFI word). All
five channels are present (AW/W/B/AR/R) with the usual side-band
(`awcache`/`awprot`/`awqos`/`awregion`/`awlock`/`awuser` and the AR
equivalents). `s_axi_awuser` / `s_axi_aruser` / `s_axi_wuser` are single-bit at
the top. Widths:

- Address: `s_axi_awaddr` / `s_axi_araddr` = `AW`
- Data: `s_axi_wdata` / `s_axi_rdata` = `DW`; `s_axi_wstrb` = `SW`
- ID: `s_axi_awid` / `s_axi_bid` / `s_axi_arid` / `s_axi_rid` = `IW`

The exact per-signal declaration is the AW/W/B/AR/R block in
`rtl/top/pumice_top.sv`. AXI side-band `awqos`/`arqos`/`awregion`/`arregion` are
carried through the burst splitters but do not drive scheduler priority.

## DFI 2.1 Master Port List

The DFI pin bus is the wide (per-phase x `DFI_RATE`) form. Command control
strobes are 1-bit-per-phase; address/bank are `ROW_WIDTH`/`$clog2(NUM_BANKS)`
per phase.

| Port                   | Dir | Width               |
|------------------------|-----|---------------------|
| `dfi_address_o`        | out | `DFI_ADDR_BUS_W`    |
| `dfi_bank_o`           | out | `DFI_BANK_BUS_W`    |
| `dfi_cas_n_o`          | out | `DFI_CTRL_BUS_W`    |
| `dfi_ras_n_o`          | out | `DFI_CTRL_BUS_W`    |
| `dfi_we_n_o`           | out | `DFI_CTRL_BUS_W`    |
| `dfi_cs_n_o`           | out | `DFI_CS_BUS_W`      |
| `dfi_odt_o`            | out | `DFI_CS_BUS_W`      |
| `dfi_wrdata_o`         | out | `DFI_DATA_WIDTH`    |
| `dfi_wrdata_en_o`      | out | `DFI_EN_WIDTH`      |
| `dfi_wrdata_mask_o`    | out | `DFI_STRB_WIDTH`    |
| `dfi_rddata_en_o`      | out | `DFI_EN_WIDTH`      |
| `dfi_rddata_i`         | in  | `DFI_DATA_WIDTH`    |
| `dfi_rddata_valid_i`   | in  | `DFI_VALID_WIDTH`   |
| `dfi_init_start_o`     | out | 1                   |
| `dfi_init_complete_i`  | in  | 1                   |

Notes:

- The DDR2 `ras/cas/we` strobes are present in all builds. For LPDDR2
  (`PHY_TIMING.memtype = 1`) the command rides the CA bus packed onto
  `dfi_address_o` and these strobes idle; the `memtype` is a runtime field, so
  the same SV header serves both flavors.
- The DFI bus is driven in the `dfi_clk` domain. `a7ddrphy` (LiteDRAM's Xilinx
  7-series PHY, the board target) handles the internal DFI-to-DRAM gearing; the
  controller does not drive per-phase read gearing beyond `rd_phase`.

## SystemVerilog Header Snippet

The canonical source is `rtl/top/pumice_top.sv` -- the module declaration there
is authoritative. The parameter block above and the port groups (cpuif, AXI4,
DFI 2.1) are a human-readable mirror of that file.
