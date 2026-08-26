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

# AXI4 Slave Read Interface (Clock-Gated)

**Module:** `axi4_slave_rd_cg.sv`
**Base Module:** [axi4_slave_rd](./axi4_slave_rd.md)
**Location:** `rtl/amba/axi4/`
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [axi4_slave_rd](./axi4_slave_rd.md) — same elastic buffer, with activity-based clock gating wrapped around it for power.

For complete clock-gating documentation, usage examples, and configuration guidelines, see the **[Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**.

What the wrapper buys you:

- **Same Functionality:** 100% equivalent to base module
- **Power Savings:** traffic-dependent; unmeasured in this repo -- treat any percentage as a placeholder until characterized
- **Configurable at runtime:** `cfg_cg_enable` / `cfg_cg_idle_count` inputs
- **Zero Overhead When Disabled:** `cfg_cg_enable=0` bypasses the gate

---

## Parameters

In addition to all [axi4_slave_rd](./axi4_slave_rd.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown, sizing `cfg_cg_idle_count` |

The gating controls are RUNTIME INPUTS, not parameters: `cfg_cg_enable`
and `cfg_cg_idle_count`; status outputs `cg_gating` / `cg_idle`. One
`amba_clock_gate_ctrl` gates the whole module -- no per-domain gates. The
base module's `busy` output is NOT re-exported (consumed internally as a
wake term). (The ENABLE_CLOCK_GATING / CG_IDLE_CYCLES / CG_GATE_*
interface this page once documented never existed.)

---

## Usage Example

```systemverilog
axi4_slave_rd_cg #(
    // Base module parameters (see axi4_slave_rd.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd8),
    .cg_gating(), .cg_idle(),
    // ... all other ports same as axi4_slave_rd (except busy)
);
```

---

## Related Modules

- **Base Module Functionality:** [axi4_slave_rd.md](./axi4_slave_rd.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb4/apb4_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXI4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
