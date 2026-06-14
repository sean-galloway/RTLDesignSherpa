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

The top module is `ddr2_lpddr2_ctrl` and has four external interfaces:

1. AXI4 slave (host request path)
2. DFI v2.1 master (DRAM PHY path)
3. APB CSR slave (configuration and observation)
4. Clocks, resets, and miscellaneous (interrupts, debug, scan)

All four are exposed at the top level as flat per-signal ports. SystemVerilog interfaces are **not** used at the top boundary because the framework's interface convention (see CocoTBFramework BFM components) drives flat-port pin-level handshakes. Internal sub-blocks use interface objects, but the top-of-design is flat for synthesis and BFM compatibility.

## Parameter-Dependent Widths

Several port widths depend on top-level parameters. Throughout this section:

- `AW` = `AXI_ADDR_WIDTH` (default 32)
- `DW` = `AXI_DATA_WIDTH` (default 64)
- `SW` = `DW/8` (byte-strobe width)
- `IDW` = `AXI_ID_WIDTH` (default 4)
- `DFI_DW` = `DFI_DATA_WIDTH` (per-phase; default 32)
- `DFI_AW` = `DFI_ADDR_WIDTH` (default 14 for DDR2, 20 for LPDDR2)
- `NP` = `N_PHASES` (default 4)
- `NR` = `NUM_RANKS` (default 1)
- `NB` = `NUM_BANKS` (default 8)
- `BA` = `$clog2(NUM_BANKS)`

## 1. AXI4 Slave (Host-side)

### Write Address Channel (AW)

| Signal      | Direction | Width    | Description                          |
|-------------|-----------|----------|--------------------------------------|
| `awid`      | input     | `IDW`    | Write transaction ID                 |
| `awaddr`    | input     | `AW`     | Write start address                  |
| `awlen`     | input     | 8        | Burst length – 1                     |
| `awsize`    | input     | 3        | Beat size encoding                   |
| `awburst`   | input     | 2        | Burst type (INCR mandatory; FIXED / WRAP optional) |
| `awlock`    | input     | 1        | Lock (ignored — exclusives not supported) |
| `awcache`   | input     | 4        | Cache hint (observed; no behavior)   |
| `awprot`    | input     | 3        | Protection bits (observed)           |
| `awqos`     | input     | 4        | QoS hint (boosts scheduler priority — see §3.2) |
| `awregion`  | input     | 4        | Region (observed)                    |
| `awvalid`   | input     | 1        | Address-valid                        |
| `awready`   | output    | 1        | Address-ready                        |

### Write Data Channel (W)

| Signal     | Direction | Width  | Description                |
|------------|-----------|--------|----------------------------|
| `wdata`    | input     | `DW`   | Write data                 |
| `wstrb`    | input     | `SW`   | Byte enables               |
| `wlast`    | input     | 1      | Last beat of burst         |
| `wvalid`   | input     | 1      | Data-valid                 |
| `wready`   | output    | 1      | Data-ready                 |

### Write Response Channel (B)

| Signal     | Direction | Width   | Description                    |
|------------|-----------|---------|--------------------------------|
| `bid`      | output    | `IDW`   | Response ID                    |
| `bresp`    | output    | 2       | Response code (OKAY / SLVERR)  |
| `bvalid`   | output    | 1       | Response-valid                 |
| `bready`   | input     | 1       | Response-ready                 |

### Read Address Channel (AR)

| Signal      | Direction | Width   | Description                          |
|-------------|-----------|---------|--------------------------------------|
| `arid`      | input     | `IDW`   | Read transaction ID                  |
| `araddr`    | input     | `AW`    | Read start address                   |
| `arlen`     | input     | 8       | Burst length – 1                     |
| `arsize`    | input     | 3       | Beat size encoding                   |
| `arburst`   | input     | 2       | Burst type                           |
| `arlock`    | input     | 1       | Lock (ignored)                       |
| `arcache`   | input     | 4       | Cache hint                           |
| `arprot`    | input     | 3       | Protection                           |
| `arqos`     | input     | 4       | QoS hint                             |
| `arregion`  | input     | 4       | Region                               |
| `arvalid`   | input     | 1       | Address-valid                        |
| `arready`   | output    | 1       | Address-ready                        |

### Read Data Channel (R)

| Signal     | Direction | Width   | Description                  |
|------------|-----------|---------|------------------------------|
| `rid`      | output    | `IDW`   | Read data ID                 |
| `rdata`    | output    | `DW`    | Read data                    |
| `rresp`    | output    | 2       | Response code                |
| `rlast`    | output    | 1       | Last beat                    |
| `rvalid`   | output    | 1       | Data-valid                   |
| `rready`   | input     | 1       | Data-ready                   |

## 2. DFI v2.1 Master (PHY-side)

The DFI v2.1 sub-interfaces present on this controller are limited to **command**, **write-data**, **read-data**, **status**, and **update**. Training, frequency-change, low-power, and CRC sub-interfaces are not driven — see §2.1 Out of Scope.

### DFI Command Sub-Interface (Per-Phase)

The command bus is replicated `N_PHASES` times. Each per-phase index `p ∈ {0 .. NP−1}` carries its own command operand set; the gear logic in `gear_dfi` aligns them within the MC clock cycle.

| Signal            | Direction | Width   | Per-Phase | Description                          |
|-------------------|-----------|---------|-----------|--------------------------------------|
| `dfi_address`     | output    | `DFI_AW`| ×`NP`     | Address operand (row, column, or CA-bus)            |
| `dfi_bank`        | output    | `BA`    | ×`NP`     | Bank operand (per-rank bank, see `dfi_cs_n` for rank) |
| `dfi_cs_n[r]`     | output    | 1       | ×`NP` × `NR` | Active-low chip-select, one per rank          |
| `dfi_ras_n`       | output    | 1       | ×`NP`     | RAS strobe (DDR2 only; tied / unused for LPDDR2)    |
| `dfi_cas_n`       | output    | 1       | ×`NP`     | CAS strobe (DDR2 only)                              |
| `dfi_we_n`        | output    | 1       | ×`NP`     | WE strobe (DDR2 only)                               |
| `dfi_cke[r]`      | output    | 1       | ×`NR`     | Clock-enable, one per rank (cross-phase; held)      |
| `dfi_odt[r]`      | output    | 1       | ×`NR`     | ODT, one per rank (cross-phase; driven by `odt_ctrl`) |
| `dfi_reset_n`     | output    | 1       |           | DRAM reset (init engine)                            |

### DFI Write-Data Sub-Interface

| Signal                | Direction | Width             | Description                          |
|-----------------------|-----------|-------------------|--------------------------------------|
| `dfi_wrdata_en`       | output    | `NP`              | Per-phase write-data valid           |
| `dfi_wrdata`          | output    | `NP × DFI_DW`     | Concatenated per-phase write data    |
| `dfi_wrdata_mask`     | output    | `NP × DFI_DW/8`   | Per-byte write mask                  |
| `dfi_wrdata_cs_n[r]`  | output    | `NP × NR`         | Per-rank, per-phase data-bus chip-select; the encoder asserts the matching rank when issuing a write |

### DFI Read-Data Sub-Interface

| Signal               | Direction | Width            | Description                          |
|----------------------|-----------|------------------|--------------------------------------|
| `dfi_rddata_en`      | output    | `NP`             | Per-phase read-data enable           |
| `dfi_rddata`         | input     | `NP × DFI_DW`    | Per-phase read data                  |
| `dfi_rddata_valid`   | input     | `NP`             | Per-phase read data valid            |
| `dfi_rddata_cs_n[r]` | output    | `NP × NR`        | Per-rank, per-phase data-bus chip-select; the encoder asserts the matching rank when issuing a read |

### DFI Status and Update Sub-Interface

| Signal                  | Direction | Width | Description                              |
|-------------------------|-----------|-------|------------------------------------------|
| `dfi_init_start`        | output    | 1     | Init handshake — start of DRAM init      |
| `dfi_init_complete`     | input     | 1     | PHY signals init complete                |
| `dfi_dram_clk_disable`  | output    | 1     | PHY clock disable during power-down      |
| `dfi_ctrlupd_req`       | output    | 1     | Controller-update request                |
| `dfi_ctrlupd_ack`       | input     | 1     | Controller-update acknowledge            |
| `dfi_phyupd_req`        | input     | 1     | PHY-initiated update request             |
| `dfi_phyupd_ack`        | output    | 1     | PHY-update acknowledge                   |
| `dfi_phyupd_type`       | input     | 2     | Update type (training vs. ctrl-recal)    |

## 3. APB CSR Slave (Configuration / Observation)

Single APB3 slave (4 KB region; 12-bit `paddr`). Detailed register map in §6.3.

| Signal     | Direction | Width | Description                |
|------------|-----------|-------|----------------------------|
| `psel`     | input     | 1     | Slave select               |
| `penable`  | input     | 1     | Enable strobe              |
| `pwrite`   | input     | 1     | Write enable               |
| `paddr`    | input     | 12    | Address                    |
| `pwdata`   | input     | 32    | Write data                 |
| `pstrb`    | input     | 4     | Byte strobe (APB4 only)    |
| `pready`   | output    | 1     | Slave-ready                |
| `prdata`   | output    | 32    | Read data                  |
| `pslverr`  | output    | 1     | Slave error                |

## 4. Clocks, Resets, Interrupts, Debug

| Signal            | Direction | Width  | Description                                       |
|-------------------|-----------|--------|---------------------------------------------------|
| `mc_clk`          | input     | 1      | MC clock (drives core, DFI command, scheduler)    |
| `mc_rst_n`        | input     | 1      | MC asynchronous reset, active low                 |
| `apb_pclk`        | input     | 1      | APB clock (independent of `mc_clk` for CDC)       |
| `apb_presetn`     | input     | 1      | APB reset, active low                             |
| `irq_init_done`   | output    | 1      | One-cycle pulse when DRAM init completes          |
| `irq_init_error`  | output    | 1      | Latched on init failure (cleared by CSR write)    |
| `irq_overflow`    | output    | 1      | AXI queue overflow / refresh-deadline miss        |
| `dbg_state`       | output    | 4      | Encoded power-state for board-level probe         |
| `dbg_refresh`     | output    | 1      | Asserted during any refresh sequence              |

The interrupts are wired to a downstream interrupt controller; the dbg outputs are typically routed to a test header or chipset SignalTap / ILA.

## Hierarchical Top-Level View

The top-level pinout in shorthand:

```
ddr2_lpddr2_ctrl
    ├── AXI4 slave        (host)         awid, awaddr, ..., bvalid, bready, ...
    │                                    arid, araddr, ..., rvalid, rready, ...
    ├── DFI v2.1 master   (PHY)          dfi_address, dfi_cs_n[r], ..., dfi_cke[r], dfi_odt[r], ...
    ├── APB CSR slave     (config)       psel, penable, paddr, ..., prdata, pslverr
    └── Clocks + IRQs                    mc_clk, mc_rst_n, apb_pclk, apb_presetn, irq_*, dbg_*
```

The full SystemVerilog port list — with every parameter substituted — is generated by the build system into `regs/ddr2_lpddr2_ctrl_ports.svh` and is the canonical source. This section is the **integrator's overview**, not the build-time canonical list.
