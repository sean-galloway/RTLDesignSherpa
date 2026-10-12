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

## References

- Herveille, R. (ed.). *Wishbone B4: WISHBONE System-on-Chip (SoC) Interconnection Architecture for Portable IP Cores*. OpenCores, 2010 -- ch. 3 "WISHBONE Classic Bus Cycles", the protocol of the wrapped Wishbone block.
- Cummings, C.E. "Simulation and Synthesis Techniques for Asynchronous FIFO Design." *SNUG San Jose*, 2002 -- the Gray-pointer async FIFO (`gaxi_fifo_async`) that carries the command and response across the two clocks.
- Ginosar, R. "Metastability and Synchronizers: A Tutorial." *IEEE Design & Test of Computers*, 28(5), Sept./Oct. 2011. DOI: [10.1109/MDT.2011.113](https://doi.org/10.1109/MDT.2011.113) -- synchronizer depth versus MTBF for the pointer crossings.
- Benini, L., Bogliolo, A., De Micheli, G. "A Survey of Design Techniques for System-Level Dynamic Power Management." *IEEE Trans. VLSI Systems*, 8(3), June 2000. DOI: [10.1109/92.845896](https://doi.org/10.1109/92.845896) -- the fixed-timeout policy `amba_clock_gate_ctrl` implements: gate after `cfg_cg_idle_count` idle cycles, wake on activity.
- Benini, L., De Micheli, G. "Automatic Synthesis of Low-Power Gated-Clock Finite-State Machines." *IEEE Trans. CAD*, 15(6), June 1996. DOI: [10.1109/43.503933](https://doi.org/10.1109/43.503933) -- the latch-based gated clock (`icg`) at the bottom of the gating chain.
- Deschamps, J.-P., Sutter, G.D., Cantó, E. *Guide to FPGA Implementation of Arithmetic Functions*, Springer (LNEE 149), 2012, ch. 5 "Electronic Aspects of Digital Design", §5.3.5.3 "Asynchronous FIFO" -- textbook treatment (secondary source).
- Roy, S. *Advanced Digital System Design*, Springer, ch. 15 "Low-Power Digital System Design", §15.5.5 "Logic Level Power Down" -- textbook treatment of clock gating (secondary source).
- Indexed in `rtl/amba/references/README.md` (local PDF: `WishboneB4Spec__OpenCores2010.pdf`, `rtl/cdc/references/AsyncFifoGrayPointers__Cummings2002.pdf`, `rtl/cdc/references/MetastabilitySynchronizers__Ginosar2011.pdf`, `rtl/common/references/DynamicPowerManagementTimeout__Benini2000.pdf`, `rtl/common/references/LatchBasedClockGating__Benini1996.pdf`)
