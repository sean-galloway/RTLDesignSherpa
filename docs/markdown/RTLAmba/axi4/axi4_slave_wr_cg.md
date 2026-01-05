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

# AXI4 Slave Write Interface (Clock-Gated)

**Module:** `axi4_slave_wr_cg.sv`
**Base Module:** [axi4_slave_wr](./axi4_slave_wr.md)
**Location:** `rtl/amba/axi4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axi4_slave_wr](./axi4_slave_wr.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**

---

## Summary

The `axi4_slave_wr_cg` module adds power optimization to `axi4_slave_wr` through activity-based clock gating:

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Power Savings:** 25-70% depending on traffic utilization
- ✅ **Configurable:** Idle threshold, gating domains, enable/disable
- ✅ **Zero Overhead When Disabled:** `ENABLE_CLOCK_GATING=0` → identical to base

---

## Common Parameters

In addition to all [axi4_slave_wr](./axi4_slave_wr.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
| `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
| `CG_GATE_*` | 1 | Domain-specific gating enables |

---

## Quick Usage

```systemverilog
axi4_slave_wr_cg #(
    // Base module parameters (see axi4_slave_wr.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating (see CG guide for details)
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... all other ports same as axi4_slave_wr
);
```

---

## Documentation

- **Base Module Functionality:** [axi4_slave_wr.md](./axi4_slave_wr.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXI4 Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
