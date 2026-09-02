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

# apb4_slave_cdc_cg

**Module:** `apb4_slave_cdc_cg.sv`
**Base Module:** [apb4_slave_cdc](./apb4_slave_cdc.md)
**Location:** `rtl/amba/apb4/`
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [apb4_slave_cdc](./apb4_slave_cdc.md).

**For the clock-gating architecture and the underlying gate cell, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)** and
**→ [amba_clock_gate_ctrl](../shared/amba_clock_gate_ctrl.md)**

Both live in the Shared book, which is published as a separate PDF. Take the
parameter and port names for this module from the tables below, not from the
generic guide.

The `apb4_slave_cdc_cg` module adds power optimization to `apb4_slave_cdc` through
activity-based clock gating. **Both clock domains are gated independently** — the
module instantiates two `amba_clock_gate_ctrl` blocks, one on `pclk` and one on
`aclk`, sharing the same configuration inputs.

Structurally it's a sibling of `apb4_slave_cdc`, not a wrapper around it: it
re-instantiates the same `apb4_slave` plus the same pair of `gaxi_fifo_async`
CDC FIFOs, but drives them from the gated clocks. The CDC behaviour described in
[apb4_slave_cdc.md](./apb4_slave_cdc.md) — gray pointers, `N_FLOP_CROSS=2`,
no maximum clock ratio — applies unchanged. That includes the reset rule: a
one-sided reset is NOT safe here either, for the same reason (the crossed
pointer copy is a live synchronizer, not a snapshot).

While a domain is gated, that domain's `ready` outputs are forced low, so no
handshake can complete against a stopped clock.

- **Same Functionality:** 100% equivalent to base module
- **Dual-Domain Gating:** Separate gate cell per clock domain
- **Runtime Control:** Gating is enabled and tuned by input signals, not parameters
- **Bypassable:** Tie `cfg_cg_enable = 0` for behaviour identical to the base module

---

## Parameters

In addition to all [apb4_slave_cdc](./apb4_slave_cdc.md) parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown counter, shared by both domains |

`USE_2_PHASE_CDC` is inherited from the base module and is likewise **deprecated
and ignored**. There is no `ENABLE_CLOCK_GATING` parameter and no per-domain
`CG_GATE_*` parameters.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `STRB_WIDTH` | `DATA_WIDTH / 8` |
| `DW` | `DATA_WIDTH` |
| `AW` | `ADDR_WIDTH` |
| `SW` | `STRB_WIDTH` |
| `PW` | `PROT_WIDTH` |
| `CPW` | `AW + DW + SW + PW + 1` |
| `RPW` | `DW + 1` |

## Ports

In addition to all [apb4_slave_cdc](./apb4_slave_cdc.md) ports:

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Global clock-gate enable for both domains. 0 = never gate |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles to count down before gating |
| `pclk_cg_gating` | 1 | Output | Asserted while the `pclk` domain is gated |
| `pclk_cg_idle` | 1 | Output | Asserted one cycle after the `pclk`-domain activity terms go low. **Not an occupancy flag** — see below |
| `aclk_cg_gating` | 1 | Output | Asserted while the `aclk` domain is gated |
| `aclk_cg_idle` | 1 | Output | Asserted one cycle after the `aclk`-domain activity terms go low. **Not an occupancy flag** — see below |

> **`*_cg_idle` does not know whether the FIFOs are empty.** `amba_clock_gate_ctrl`
> has no occupancy input at all — its whole idle logic is
> `r_wakeup <= user_valid || axi_valid;` and `assign idle = ~r_wakeup`. So idle
> asserts one cycle after the activity terms drop, whatever the CDC FIFOs hold.
> On this wrapper the activity terms mostly hide occupancy anyway: APB holds
> `s_apb_PSEL` until `PREADY`, and this slave asserts `PREADY` only when the
> response returns, so a stalled backend keeps `pclk_user_valid` high and
> `pclk_cg_idle` low for the whole stall; an unconsumed response likewise
> holds `w_rsp_valid`/`rsp_valid` high. Do not read that as "idle implies
> empty" — it does not, here or anywhere: idle is "nothing has been handed to
> me recently", the input to the gating countdown.
>
> **Do not use it as a safe-to-reset or safe-to-power-down qualifier**; that
> requires an emptiness check this signal does not perform.

---

## Timing Characteristics

This module is **sequential**: it contains 1 `always_ff` block(s),
clocked on `aclk` with active-low asynchronous reset `aresetn`. Outputs derived
in those blocks are registered and therefore appear one clock after the inputs
that produced them.

Per-path cycle counts are not enumerated here; read the block that drives the
signal you care about. No synthesis frequency or area figures are quoted --
none have been measured against a target device.

---

## Usage Examples
```systemverilog
apb4_slave_cdc_cg #(
    // Base module parameters (see apb4_slave_cdc.md)
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .DEPTH               (2),
    .USE_JOHNSON         (0),   // 0 = Gray: DEPTH in {2,3,4,8} (floored max(DEPTH,4) must be pow2); 1 = Johnson: any DEPTH 2..8

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

    // ... all other ports same as apb4_slave_cdc
);
```

**Simulation note:** set `cfg_cg_enable = 0` when debugging CDC waveforms. Two
independently gated clocks make cross-domain timing very hard to read.

---

## Related Modules

- **Base Module Functionality:** [apb4_slave_cdc.md](./apb4_slave_cdc.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](apb4_slave_cg.md) (APB interface)

---

## Testing

`val/amba/test_apb4_slave_cdc_cg.py` exercises this module. It collects 2 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_apb4_slave_cdc_cg.py -v
```

---

## Navigation

- **[← Back to APB Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
