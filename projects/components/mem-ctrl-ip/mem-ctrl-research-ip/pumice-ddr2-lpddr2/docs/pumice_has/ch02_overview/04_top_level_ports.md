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

# Top-Level Interfaces

This section is the integrator's quick-reference for the controller's top-level module port list. Detailed protocol semantics for each interface are in Chapter 4 (Interfaces); this is the **wire-level** view — names, directions, widths, parameter dependencies.

The top module is `pumice_top` and has four external interfaces:

1. AXI4 slave (host request path), signals prefixed `s_axi_*`
2. DFI v2.1 master (DRAM PHY path), signals suffixed `_o` / `_i`
3. CSR register cpuif (configuration and observation) — a PeakRDL passthrough bus, **not** APB
4. Clocks and resets (two domains) plus `init_done_o`

All four are exposed at the top level as flat per-signal ports. SystemVerilog interfaces are **not** used at the top boundary because the framework's interface convention (see CocoTBFramework BFM components) drives flat-port pin-level handshakes. Internal sub-blocks use interface objects, but the top-of-design is flat for synthesis and BFM compatibility.

An optional outer wrapper, `pumice_top_geared`, adds a `HOST_AXI_DATA_WIDTH` parameter and inserts formally-verified AXI data-width converters ahead of `pumice_top`; when `HOST_AXI_DATA_WIDTH == DW` the converters are bypassed and the build is bit-identical. This section describes `pumice_top` itself.

## Parameter-Dependent Widths

The core data width is fixed by the DFI geometry: `DW = DRAM_BEAT_WIDTH * DFI_RATE`. There is no separate `AXI_DATA_WIDTH` parameter on `pumice_top` — the host AXI data width equals `DW`. Throughout this section:

- `AW` = `AXI_ADDR_WIDTH` (default 32)
- `DFI_RATE` = DFI phase count / frequency ratio (default 2)
- `DRAM_BEAT_WIDTH` = per-beat DRAM data width (default 64)
- `DW` = `DRAM_BEAT_WIDTH * DFI_RATE` (host AXI + DFI word width; default 128)
- `SW` = `DW/8` (byte-strobe width)
- `IW` = `AXI_ID_WIDTH` (default 8)
- `NR` = `NUM_RANKS` (default 1)
- `NB` = `NUM_BANKS` (default 8)
- `RW` = `ROW_WIDTH` (default 14)
- `CW` = `COL_WIDTH` (default 10)
- `BKW` = `$clog2(NUM_BANKS)`
- `CSR_ADDR_W` = CSR address width (default 12)

## 1. AXI4 Slave (Host-side)

All host AXI ports carry the `s_axi_` prefix.

### Write Address Channel (AW)

| Signal            | Direction | Width  | Description                          |
|-------------------|-----------|--------|--------------------------------------|
| `s_axi_awid`      | input     | `IW`   | Write transaction ID                 |
| `s_axi_awaddr`    | input     | `AW`   | Write start address                  |
| `s_axi_awlen`     | input     | 8      | Burst length – 1                     |
| `s_axi_awsize`    | input     | 3      | Beat size encoding                   |
| `s_axi_awburst`   | input     | 2      | Burst type (INCR mandatory; FIXED / WRAP optional) |
| `s_axi_awlock`    | input     | 1      | Lock (ignored — exclusives not supported) |
| `s_axi_awcache`   | input     | 4      | Cache hint (observed; no behavior)   |
| `s_axi_awprot`    | input     | 3      | Protection bits (observed)           |
| `s_axi_awqos`     | input     | 4      | QoS hint (boosts scheduler priority — see §3.2) |
| `s_axi_awregion`  | input     | 4      | Region (observed)                    |
| `s_axi_awuser`    | input     | 1      | User sideband (observed)             |
| `s_axi_awvalid`   | input     | 1      | Address-valid                        |
| `s_axi_awready`   | output    | 1      | Address-ready                        |

### Write Data Channel (W)

| Signal           | Direction | Width  | Description                |
|------------------|-----------|--------|----------------------------|
| `s_axi_wdata`    | input     | `DW`   | Write data                 |
| `s_axi_wstrb`    | input     | `SW`   | Byte enables               |
| `s_axi_wlast`    | input     | 1      | Last beat of burst         |
| `s_axi_wuser`    | input     | 1      | User sideband              |
| `s_axi_wvalid`   | input     | 1      | Data-valid                 |
| `s_axi_wready`   | output    | 1      | Data-ready                 |

### Write Response Channel (B)

| Signal           | Direction | Width  | Description                    |
|------------------|-----------|--------|--------------------------------|
| `s_axi_bid`      | output    | `IW`   | Response ID                    |
| `s_axi_bresp`    | output    | 2      | Response code (OKAY / SLVERR)  |
| `s_axi_buser`    | output    | 1      | User sideband                  |
| `s_axi_bvalid`   | output    | 1      | Response-valid                 |
| `s_axi_bready`   | input     | 1      | Response-ready                 |

### Read Address Channel (AR)

| Signal            | Direction | Width  | Description                          |
|-------------------|-----------|--------|--------------------------------------|
| `s_axi_arid`      | input     | `IW`   | Read transaction ID                  |
| `s_axi_araddr`    | input     | `AW`   | Read start address                   |
| `s_axi_arlen`     | input     | 8      | Burst length – 1                     |
| `s_axi_arsize`    | input     | 3      | Beat size encoding                   |
| `s_axi_arburst`   | input     | 2      | Burst type                           |
| `s_axi_arlock`    | input     | 1      | Lock (ignored)                       |
| `s_axi_arcache`   | input     | 4      | Cache hint                           |
| `s_axi_arprot`    | input     | 3      | Protection                           |
| `s_axi_arqos`     | input     | 4      | QoS hint                             |
| `s_axi_arregion`  | input     | 4      | Region                               |
| `s_axi_aruser`    | input     | 1      | User sideband                        |
| `s_axi_arvalid`   | input     | 1      | Address-valid                        |
| `s_axi_arready`   | output    | 1      | Address-ready                        |

### Read Data Channel (R)

| Signal           | Direction | Width  | Description                  |
|------------------|-----------|--------|------------------------------|
| `s_axi_rid`      | output    | `IW`   | Read data ID                 |
| `s_axi_rdata`    | output    | `DW`   | Read data                    |
| `s_axi_rresp`    | output    | 2      | Response code                |
| `s_axi_rlast`    | output    | 1      | Last beat                    |
| `s_axi_ruser`    | output    | 1      | User sideband                |
| `s_axi_rvalid`   | output    | 1      | Data-valid                   |
| `s_axi_rready`   | input     | 1      | Data-ready                   |

## 2. DFI v2.1 Master (PHY-side)

The DFI v2.1 sub-interfaces present on this controller are limited to **command**, **write-data**, **read-data**, and the **init handshake**. Training, frequency-change, low-power, update, and CRC sub-interfaces are not driven — see §2.1 Out of Scope.

The DFI ports are flat, per-phase-packed buses (the `DFI_RATE` phases are concatenated into one vector) rather than SystemVerilog arrays. All DFI ports carry the `_o` (output) or `_i` (input) suffix. Command formatting runs on `dfi_clk`, past the single CDC in `pumice_dfi_layer`.

### DFI Command Bus

| Signal            | Direction | Width                     | Description                                         |
|-------------------|-----------|---------------------------|-----------------------------------------------------|
| `dfi_address_o`   | output    | `RW * DFI_RATE`           | Address operand (row / column); LPDDR2 CA-bus command is packed here |
| `dfi_bank_o`      | output    | `BKW * DFI_RATE`          | Bank operand                                        |
| `dfi_cs_n_o`      | output    | `NR * DFI_RATE`           | Active-low chip-select, per rank per phase          |
| `dfi_ras_n_o`     | output    | `DFI_RATE`                | RAS strobe per phase (DDR2; idle for LPDDR2)        |
| `dfi_cas_n_o`     | output    | `DFI_RATE`                | CAS strobe per phase (DDR2; idle for LPDDR2)        |
| `dfi_we_n_o`      | output    | `DFI_RATE`                | WE strobe per phase (DDR2; idle for LPDDR2)         |
| `dfi_odt_o`       | output    | `NR * DFI_RATE`           | ODT, per rank per phase                             |

### DFI Write-Data Bus

| Signal                | Direction | Width       | Description                          |
|-----------------------|-----------|-------------|--------------------------------------|
| `dfi_wrdata_o`        | output    | `DW`        | Write data (all phases packed; = one DFI word) |
| `dfi_wrdata_en_o`     | output    | `DFI_RATE`  | Per-phase write-data enable          |
| `dfi_wrdata_mask_o`   | output    | `SW`        | Per-byte write mask (DFI polarity: 1 = do-not-write) |

### DFI Read-Data Bus

| Signal                | Direction | Width       | Description                          |
|-----------------------|-----------|-------------|--------------------------------------|
| `dfi_rddata_en_o`     | output    | `DFI_RATE`  | Per-phase read-data enable           |
| `dfi_rddata_i`        | input     | `DW`        | Read data (all phases packed)        |
| `dfi_rddata_valid_i`  | input     | `DFI_RATE`  | Per-phase read-data valid            |

### DFI Init Handshake

| Signal                  | Direction | Width | Description                              |
|-------------------------|-----------|-------|------------------------------------------|
| `dfi_init_start_o`      | output    | 1     | Init handshake — start of DRAM init      |
| `dfi_init_complete_i`   | input     | 1     | PHY signals init complete                |

## 3. CSR Register Interface (Configuration / Observation)

Configuration is driven by name from a PeakRDL-generated register block (`pumice_csr`) via a passthrough **cpuif** request bus (not APB). Address width is `CSR_ADDR_W` (default 12). Detailed register map in §6.3.

| Signal                    | Direction | Width          | Description                    |
|---------------------------|-----------|----------------|--------------------------------|
| `s_cpuif_req`             | input     | 1              | Request valid                  |
| `s_cpuif_req_is_wr`       | input     | 1              | 1 = write, 0 = read            |
| `s_cpuif_addr`            | input     | `CSR_ADDR_W`   | Register address               |
| `s_cpuif_wr_data`         | input     | 32             | Write data                     |
| `s_cpuif_wr_biten`        | input     | 32             | Per-bit write enable           |
| `s_cpuif_req_stall_wr`    | output    | 1              | Write back-pressure            |
| `s_cpuif_req_stall_rd`    | output    | 1              | Read back-pressure             |
| `s_cpuif_rd_ack`          | output    | 1              | Read data valid                |
| `s_cpuif_rd_err`          | output    | 1              | Read error                     |
| `s_cpuif_rd_data`         | output    | 32             | Read data                      |
| `s_cpuif_wr_ack`          | output    | 1              | Write accepted                 |
| `s_cpuif_wr_err`          | output    | 1              | Write error                    |

## 4. Clocks, Resets, and Status

The design has two clock domains — the controller/AXI domain (`aclk`) and the DFI/PHY domain (`dfi_clk`) — with the single crossing inside `pumice_dfi_layer`.

| Signal          | Direction | Width  | Description                                          |
|-----------------|-----------|--------|-----------------------------------------------------|
| `aclk`          | input     | 1      | Controller clock (host AXI, CAMs, scheduler)        |
| `aresetn`       | input     | 1      | Controller reset, active low                        |
| `dfi_clk`       | input     | 1      | DFI/PHY clock                                        |
| `dfi_rstn`      | input     | 1      | DFI reset, active low                               |
| `init_done_o`   | output    | 1      | Asserted when DRAM init completes                   |

## Hierarchical Top-Level View

The top-level pinout in shorthand:

```
pumice_top
    ├── AXI4 slave        (host)         s_axi_awid, s_axi_awaddr, ..., s_axi_rvalid, s_axi_rready, ...
    ├── DFI v2.1 master   (PHY)          dfi_address_o, dfi_bank_o, dfi_cs_n_o, ..., dfi_rddata_i, ...
    ├── CSR cpuif         (config)       s_cpuif_req, s_cpuif_addr, ..., s_cpuif_rd_data, ...
    └── Clocks + status                  aclk, aresetn, dfi_clk, dfi_rstn, init_done_o
```

The canonical SystemVerilog port list is `rtl/top/pumice_top.sv`. This section is the **integrator's overview**, not the build-time canonical list.
