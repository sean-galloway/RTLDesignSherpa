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

This chapter is the **wire-level** port list of the `ddr2_lpddr2_ctrl` top module — the exact signal names, directions, widths, and parameter dependencies that the integration script and SoC top-level use.

The implementation-level signal list is the same as the HAS overview view (HAS §2.4); this chapter restates it in the SystemVerilog-derivable form, with notes on bit-ordering, default tie-offs, and synthesis attributes where they matter.

The canonical machine-generated source is `regs/ddr2_lpddr2_ctrl_ports.svh` — what follows is the human-readable mirror.

## Parameter-Dependent Widths (re-stated)

- `AW`     = `AXI_ADDR_WIDTH`
- `DW`     = `AXI_DATA_WIDTH`
- `SW`     = `DW/8`
- `IDW`    = `AXI_ID_WIDTH`
- `DFI_DW` = `DFI_DATA_WIDTH`
- `DFI_AW` = `DFI_ADDR_WIDTH`
- `NP`     = `N_PHASES`
- `NR`     = `NUM_RANKS`
- `NB`     = `NUM_BANKS`
- `BA`     = `$clog2(NUM_BANKS)`

## AXI4 Slave Port List

> See HAS §2.4 §1 for the table. The MAS adds nothing beyond what the HAS already published; the SystemVerilog declaration uses the same field names directly. AXI side-band signals (`awqos`, `awregion`, `arqos`, `arregion`) are observed but do not currently drive scheduler priority in v1; the wiring exists for the v2 QoS feature.

## DFI v2.1 Master Port List

> See HAS §2.4 §2. Additional MAS-level notes:
>
> - The `dfi_cs_n[NR]` packed dimension is **outer-most** in SV declaration: `output [NP-1:0][NR-1:0] dfi_cs_n;`
> - Per-rank `dfi_cke[NR]` is **outer-most**: `output [NR-1:0] dfi_cke;`
> - The DDR2 ras/cas/we strobes are present even in LPDDR2 builds (driven all-1s, tied off by synthesis); the elaboration-time `MEMTYPE` parameter does *not* remove them from the port list, so the same SV header is usable for both flavors.

## APB CSR Slave Port List

> See HAS §2.4 §3. The APB clock and reset (`apb_pclk`, `apb_presetn`) are in the misc port group below; only the protocol signals are in this APB block.

## Clocks, Resets, IRQs, Debug

> See HAS §2.4 §4.
>
> Additional MAS notes:
>
> - `mc_rst_n` is asynchronous-assert, synchronous-deassert inside the controller (the deassert synchronizer lives in `power_state_fub`'s reset domain).
> - `apb_presetn` is independently synchronized in `csr_apb_fub`.
> - `irq_*` outputs are asserted in the `mc_clk` domain; the SoC's interrupt controller is responsible for re-synchronizing if it runs on a different clock.

## SystemVerilog Header Snippet

The first 30 lines of the generated port header — the rest is per the tables above:

```systemverilog
module ddr2_lpddr2_ctrl #(
    parameter string MEMTYPE          = "DDR2",
    parameter int    N_PHASES         = 4,
    parameter int    NUM_RANKS        = 1,
    parameter int    NUM_BANKS        = 8,
    parameter int    AXI_DATA_WIDTH   = 64,
    parameter int    AXI_ID_WIDTH     = 4,
    parameter int    AXI_ADDR_WIDTH   = 32,
    parameter int    ROW_WIDTH        = 14,
    parameter int    COL_WIDTH        = 10,
    parameter int    DFI_DATA_WIDTH   = 32,
    parameter int    DFI_ADDR_WIDTH   = 14,
    parameter int    WRPHASE          = 0,
    parameter int    RDPHASE          = 0,
    parameter int    TXN_QUEUE_DEPTH  = 16,
    parameter string SCHEDULER_MODE   = "OOO",
    parameter int    LOOKAHEAD_DEPTH_MAX = 4,
    parameter string PAGE_POLICY      = "HAPPY_HYBRID",
    parameter int    PAGE_PREDICTOR_TABLE_BITS = 12,
    parameter int    AGE_MAX          = 256,
    parameter int    REFRESH_DEFER_MAX = 8,
    parameter string REFPB_POLICY     = "DARP",
    parameter string ODT_RULE_MULTIRANK = "JEDEC_DDR2",
    parameter int    SIM_INIT_SCALE   = 1
) (
    // Clocks and resets
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,
    input  logic                       apb_pclk,
    input  logic                       apb_presetn,

    // AXI4 slave, DFI master, APB slave, IRQs, debug — see chapter tables.

    // ...
);
```

The full module declaration is in `regs/ddr2_lpddr2_ctrl_ports.svh` (machine-generated).
