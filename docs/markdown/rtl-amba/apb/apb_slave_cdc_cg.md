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

Structurally it's a sibling of `apb_slave_cdc`, not a wrapper around it: it
re-instantiates the same `apb_slave` plus the same pair of `gaxi_fifo_async`
CDC FIFOs, but drives them from the gated clocks. The CDC behaviour described in
[apb_slave_cdc.md](./apb_slave_cdc.md) -- gray pointers, `N_FLOP_CROSS=2`,
no maximum clock ratio -- applies unchanged. That includes the reset rule: a
one-sided reset is NOT safe here either, for the same reason (the crossed
pointer copy is a live synchronizer, not a snapshot).

While a domain is gated, that domain's `ready` outputs are forced low, so no
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
| `pclk_cg_idle` | 1 | Output | Asserted one cycle after the `pclk`-domain activity terms go low. **Not an occupancy flag** -- see below |
| `aclk_cg_gating` | 1 | Output | Asserted while the `aclk` domain is gated |
| `aclk_cg_idle` | 1 | Output | Asserted one cycle after the `aclk`-domain activity terms go low. **Not an occupancy flag** -- see below |

> **`*_cg_idle` does not know whether the FIFOs are empty.** `amba_clock_gate_ctrl`
> has no occupancy input at all -- its whole idle logic is
> `r_wakeup <= user_valid || axi_valid;` and `assign idle = ~r_wakeup`. So idle
> asserts one cycle after the activity terms drop, whatever the CDC FIFOs hold.
> Concretely: with the backend stalled and commands sitting unread in the cmd
> FIFO, every `pclk`-side valid is low, so `pclk_cg_idle` reads 1 against a
> non-empty FIFO. The same holds on the `aclk` side for an unconsumed response.
>
> Use it as what it is -- "nothing has been handed to me recently", the input to
> the gating countdown. **Do not use it as a safe-to-reset or safe-to-power-down
> qualifier**; that requires an emptiness check this signal does not perform.


---

## Quick Usage

```systemverilog
apb_slave_cdc_cg #(
    // Base module parameters (see apb_slave_cdc.md)
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .DEPTH               (2),
    .USE_JOHNSON         (0),   // 0 = Gray (default), 1 = Johnson (any depth)

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
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb_slave_cg.md](../apb/apb_slave_cg.md) (APB interface)

---

## Navigation

- **[← Back to APB Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
