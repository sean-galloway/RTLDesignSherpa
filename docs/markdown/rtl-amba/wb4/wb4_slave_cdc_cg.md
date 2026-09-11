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

# wb4_slave_cdc_cg

## Overview

[wb4_slave_cdc](wb4_slave_cdc.md) with the **Wishbone-side clock gated**,
the combined variant matching `apb4_slave_cdc_cg` / `apb5_slave_cdc_cg`.

Only the Wishbone domain is gated. The FUB domain keeps running, so a
consumer can go on draining commands and posting responses while the bus
sleeps; the async FIFOs make that safe. Gating both would need a second
controller and buys nothing a caller cannot do by gating its own clock.

## Parameters

Every `wb4_slave_cdc` parameter, plus `CG_IDLE_COUNT_WIDTH`:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of the idle countdown; bounds the programmable idle threshold |

## Ports

`wb4_slave_cdc`'s ports plus `cfg_cg_enable`, `cfg_cg_idle_count`,
`cg_gating` and `cg_idle`, all in the `wb_clk` domain:

| Port | Direction | Description |
|---|---|---|
| `cfg_cg_enable` | in | Global clock-gate enable |
| `cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]` | in | Idle clocks before the clock is gated |
| `cg_gating` | out | Clock is gated now |
| `cg_idle` | out | Nothing pending (the controller's idle indicator) |

## Functional Description

### The Wake Term Has to Be Single-Domain

This is the one thing worth reading before changing it. The wake term is
`wb4_slave_cdc`'s `wb_busy` output, which is built **only** from `wb_clk`
signals: a cycle open on the bus, a command waiting to cross, or a
response that has crossed and not yet been driven.

Nothing from the `aclk` side may be used, because sampling it in `wb_clk`
would be an unsynchronised crossing. That is the mistake this wrapper
invites, and the reason `wb_busy` exists rather than the wake term being
assembled here from whatever looked convenient.

For the same reason `cmd_valid` is **not** masked with `cg_gating` the
way [wb4_slave_cg](wb4_slave_cg.md) masks it: `cmd_valid` lives in
`aclk`, and masking it with a `wb_clk`-domain signal would be exactly
that crossing. `s_wb_STALL` **is** held high while gated, for the reason
`wb4_slave_cg` gives: a pipelined accept is `STB && !STALL` in the
master's clock, and a frozen "room" would let a master move on from a
request the slave never sampled.

### Reset Behavior

`wb4_slave_cdc`'s one-sided reset caveat applies unchanged: quiesce the
bus before resetting one side.

## Related Modules

- [wb4_slave_cdc](wb4_slave_cdc.md), [wb4_slave_cg](wb4_slave_cg.md)

## Testing

`val/amba/test_wb4_slave_cdc.py` carries a `cg` dimension that selects
this module in place of `wb4_slave_cdc` and drives the gating
configuration; the same traffic, abort and post-abort phases run at
several clock ratios in both directions.
