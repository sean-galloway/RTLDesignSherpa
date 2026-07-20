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

# AXIS Master Interface (Clock-Gated)

**Module:** `axis_master_cg.sv`
**Base Module:** [axis_master](./axis_master.md)
**Location:** `rtl/amba/axis4/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [axis_master](./axis_master.md).

**For complete clock-gating documentation, usage examples, and configuration guidelines, see:**

**→ [AXIS4 Clock-Gated Variants Guide](./axis_clock_gating_guide.md)**

---

## Summary

The `axis_master_cg` module adds power optimization to `axis_master` through activity-based clock gating:

- **Same Data Functionality:** Identical to the base module once the clock is running
- **Power Savings:** Estimated 25-70% depending on stream duty cycle (planning figure, not measured)
- **Configurable:** Runtime idle threshold and enable via `cfg_cg_*` inputs
- **Bypass When Disabled:** `cfg_cg_enable = 0` holds the clock permanently enabled, making the wrapper functionally identical to the base module

---

## Common Parameters

In addition to all [axis_master](./axis_master.md) parameters:

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | 4 | Width of the idle countdown counter (max idle = 2^N - 1 cycles) |

This is the **only** additional parameter. Gating enable and the idle threshold are
**runtime inputs**, not parameters:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | Input | 1 | Enable clock gating (0 = clock always running) |
| `cfg_cg_idle_count` | Input | `CG_IDLE_COUNT_WIDTH` | Idle cycles before gating engages |
| `cg_gating` | Output | 1 | Clock currently gated |
| `cg_idle` | Output | 1 | No activity observed in the previous cycle |

> There is no `ENABLE_CLOCK_GATING` parameter, no `CG_IDLE_CYCLES` parameter, and no
> `CG_GATE_*` domain-enable family. There is a single gating domain covering the whole
> module. The `_cg` wrapper also **does not expose the base module's `busy` output** — it is
> consumed internally as a wakeup term.

---

## Quick Usage

```systemverilog
axis_master_cg #(
    // Base module parameters (see axis_master.md)
    .SKID_DEPTH(4),
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(1),

    // Clock gating (see CG guide for details)
    .CG_IDLE_COUNT_WIDTH(4)
) u_cg (
    .aclk(clk),
    .aresetn(rst_n),

    // Clock gating control (runtime inputs)
    .cfg_cg_enable(cg_enable),
    .cfg_cg_idle_count(4'd8),

    // ... all AXI4-Stream ports same as axis_master ...

    // Clock gating status (replaces the base module's `busy` output)
    .cg_gating(clk_is_gated),
    .cg_idle(stream_idle)
);
```

> The base module's parameters are `SKID_DEPTH`, `AXIS_DATA_WIDTH`, `AXIS_ID_WIDTH`,
> `AXIS_DEST_WIDTH` and `AXIS_USER_WIDTH`. AXI4-Stream has no address channel, so there is
> no `AXI_ADDR_WIDTH`.

---

## Documentation

- **Base Module Functionality:** [axis_master.md](./axis_master.md)
- **Clock Gating Guide:** [axis_clock_gating_guide.md](./axis_clock_gating_guide.md) (AXIS4-specific)
- **Generic CG Architecture:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../monitor/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../monitor/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to AXIS4 Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
