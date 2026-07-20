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

# APB Slave with CDC (Clock-Gated)

**Module:** `apb_slave_cdc_cg.sv`
**Base Module:** [apb_slave_cdc](./apb_slave_cdc.md)
**Location:** `rtl/amba/apb/`
**Status:** ✅ Production Ready

---

## Quick Reference

This is the **clock-gated variant** of [apb_slave_cdc](./apb_slave_cdc.md).

**For the clock-gating architecture and the underlying gate cell, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)** and
**→ [amba_clock_gate_ctrl](../shared/amba_clock_gate_ctrl.md)**

Both live in the Shared book, which is published as a separate PDF. Take the
parameter and port names for this module from the tables below, not from the
generic guide.

---

## Summary

The `apb_slave_cdc_cg` module adds power optimization to `apb_slave_cdc` through
activity-based clock gating. **Both clock domains are gated independently** -- the
module instantiates two `amba_clock_gate_ctrl` blocks, one on `pclk` and one on
`aclk`, sharing the same configuration inputs.

Structurally it is a sibling of `apb_slave_cdc` rather than a wrapper around it:
it re-instantiates the same `apb_slave` plus the same pair of `gaxi_fifo_async`
CDC FIFOs, but drives them from the gated clocks. The CDC behaviour described in
[apb_slave_cdc.md](./apb_slave_cdc.md) -- gray pointers, `N_FLOP_CROSS=2`,
independent-reset safety, no maximum clock ratio -- applies unchanged.

While a domain is gated, that domain's `ready` outputs are forced low so no
handshake can complete against a stopped clock.

- ✅ **Same Functionality:** 100% equivalent to base module
- ✅ **Dual-Domain Gating:** Separate gate cell per clock domain
- ✅ **Runtime Control:** Gating is enabled and tuned by input signals, not parameters
- ✅ **Bypassable:** Tie `cfg_cg_enable = 0` for behaviour identical to the base module

---

## Additional Parameters

In addition to all [apb_slave_cdc](./apb_slave_cdc.md) parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown counter, shared by both domains |

`USE_2_PHASE_CDC` is inherited from the base module and is likewise **deprecated
and ignored**. There is no `ENABLE_CLOCK_GATING` parameter and no per-domain
`CG_GATE_*` parameters.

## Additional Ports

In addition to all [apb_slave_cdc](./apb_slave_cdc.md) ports:

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Global clock-gate enable for both domains. 0 = never gate |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles to count down before gating |
| `pclk_cg_gating` | 1 | Output | Asserted while the `pclk` domain is gated |
| `pclk_cg_idle` | 1 | Output | Asserted while the `pclk` domain buffers are empty |
| `aclk_cg_gating` | 1 | Output | Asserted while the `aclk` domain is gated |
| `aclk_cg_idle` | 1 | Output | Asserted while the `aclk` domain buffers are empty |

---

## Quick Usage

```systemverilog
apb_slave_cdc_cg #(
    // Base module parameters (see apb_slave_cdc.md)
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .DEPTH               (2),

    // Clock gating
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg (
    .pclk              (apb_clk),
    .presetn           (apb_resetn),
    .aclk              (core_clk),
    .aresetn           (core_resetn),

    // Clock gating control (applies to both domains)
    .cfg_cg_enable     (1'b1),
    .cfg_cg_idle_count (4'd8),

    // Per-domain gating status
    .pclk_cg_gating    (pclk_gated),
    .pclk_cg_idle      (pclk_idle),
    .aclk_cg_gating    (aclk_gated),
    .aclk_cg_idle      (aclk_idle),

    // ... all other ports same as apb_slave_cdc
);
```

**Simulation note:** set `cfg_cg_enable = 0` when debugging CDC waveforms. Two
independently gated clocks make cross-domain timing very hard to read.

---

## Documentation

- **Base Module Functionality:** [apb_slave_cdc.md](./apb_slave_cdc.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../monitor/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../monitor/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to APB Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
