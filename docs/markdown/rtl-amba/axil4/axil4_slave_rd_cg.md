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

# AXIL4 Slave Read Interface (Clock-Gated)

**Module:** `axil4_slave_rd_cg.sv`
**Base Module:** [axil4_slave_rd](./axil4_slave_rd.md)
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axil4_slave_rd](./axil4_slave_rd.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [AXIL4 Clock-Gated Variants Guide](./axil4_clock_gating_guide.md)** (AXIL4-specific)

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)** (cross-protocol overview)

---

## Summary

The `axil4_slave_rd_cg` module adds power optimization to `axil4_slave_rd` through activity-based clock gating:

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Power Savings:** dynamic clock power in the gated block scales with idle
  fraction; see the [AXIL4 Clock-Gated Variants Guide](./axil4_clock_gating_guide.md)
  for the estimate table and its caveats
- ✅ **Configurable:** idle threshold and enable, both at **runtime** via
  `cfg_cg_idle_count` / `cfg_cg_enable`
- ✅ **Zero Overhead When Disabled:** `cfg_cg_enable = 0` holds the clock
  free-running, making behavior identical to the base module

---

## Common Parameters

In addition to all [axil4_slave_rd](./axil4_slave_rd.md) parameters:

The `_cg` wrapper adds exactly **one** parameter. Gating is enabled and tuned
at runtime through ports, not through parameters — there is no
`ENABLE_CLOCK_GATING` parameter, no `CG_IDLE_CYCLES` parameter, and no
per-domain `CG_GATE_*` parameters on this module.

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle counter; max idle count = 2^N - 1 |

### Additional Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating (0 = clock always running) |
| `cfg_cg_idle_count` | Input | CG_IDLE_COUNT_WIDTH | Idle cycles before gating |
| `cg_gating` | Output | 1 | Clock currently gated |
| `cg_idle` | Output | 1 | No activity on the previous cycle |

The base module's `busy` output is **not** exposed on the `_cg` wrapper; it is
consumed internally as a wakeup term. All other ports are identical to
`axil4_slave_rd`.

---

## Quick Usage

```systemverilog
axil4_slave_rd_cg #(
    // Base module parameters (see axil4_slave_rd.md)
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),

    // Clock gating (see CG guide for details)
    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),

    // Clock gating control (runtime, not parameters)
    .cfg_cg_enable(1'b1),
    .cfg_cg_idle_count(4'd5),

    // ... all other ports same as axil4_slave_rd, except `busy`,
    // which is replaced by cg_gating / cg_idle
    .cg_gating(clk_gated),
    .cg_idle(if_idle)
);
```

---

## Documentation

- **Base Module Functionality:** [axil4_slave_rd.md](./axil4_slave_rd.md)
- **AXIL4 Clock Gating Guide:** [axil4_clock_gating_guide.md](./axil4_clock_gating_guide.md)
- **Cross-Protocol Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](../apb/apb4_slave_cg.md) (APB interface)

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[← Back to AXIL4 Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
