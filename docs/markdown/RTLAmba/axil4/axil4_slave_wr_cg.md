# AXIL4 Slave Write Interface (Clock-Gated)

**Module:** `axil4_slave_wr_cg.sv`
**Base Module:** [axil4_slave_wr](./axil4_slave_wr.md)
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axil4_slave_wr](./axil4_slave_wr.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)**

---

## Summary

The `axil4_slave_wr_cg` module adds power optimization to `axil4_slave_wr` through activity-based clock gating:

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Power Savings:** 25-70% depending on traffic utilization
- ✅ **Configurable:** Idle threshold, gating domains, enable/disable
- ✅ **Zero Overhead When Disabled:** `ENABLE_CLOCK_GATING=0` → identical to base

---

## Common Parameters

In addition to all [axil4_slave_wr](./axil4_slave_wr.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ENABLE_CLOCK_GATING` | 1 | Master enable (0=disable, identical to base) |
| `CG_IDLE_CYCLES` | 8 | Cycles before clock gating activates |
| `CG_GATE_*` | 1 | Domain-specific gating enables |

---

## Quick Usage

```systemverilog
axil4_slave_wr_cg #(
    // Base module parameters (see axil4_slave_wr.md)
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),

    // Clock gating (see CG guide for details)
    .ENABLE_CLOCK_GATING(1),
    .CG_IDLE_CYCLES(8)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),
    // ... all other ports same as axil4_slave_wr
);
```

---

## Documentation

- **Base Module Functionality:** [axil4_slave_wr.md](./axil4_slave_wr.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXIL4 Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
