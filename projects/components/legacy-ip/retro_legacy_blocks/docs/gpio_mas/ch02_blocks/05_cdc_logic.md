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

# APB GPIO - CDC Logic Block

## Overview

When you need the GPIO core on its own clock, asynchronous to the APB bus, `CDC_ENABLE` moves the whole register file across the domain boundary. Everything about the crossing lives in this one block.

### Figure 2.7: CDC Logic Block Diagram

![CDC Logic Block](../assets/mermaid/gpio_cdc_block.png)

## Parameters

### CDC_ENABLE

| Value | Behavior |
|-------|----------|
| 0 | Single clock domain, all logic on pclk |
| 1 | Dual clock domain, GPIO core on gpio_clk |

: Table 2.7: CDC Enable Parameter

## Functional Description

### Clock Domains

#### Figure 2.8: Single Clock Domain (CDC Disabled)

![CDC Disabled](../assets/mermaid/gpio_cdc_disabled.png)

#### Figure 2.9: Dual Clock Domain (CDC Enabled)

![CDC Enabled](../assets/mermaid/gpio_cdc_enabled.png)

### CDC Implementation

When CDC_ENABLE=1 the ENTIRE register file and GPIO core sit in the gpio_clk
domain; no register value is individually synchronized. The only crossing is
the APB command/response stream itself, carried through an `apb4_slave_cdc`
instance at the bus boundary (`apb4_gpio.sv`, `gen_cdc`). An APB access
therefore completes with CDC handshake latency, and once it lands in the
gpio_clk domain every register behaves exactly as in the single-clock
configuration.

### The `irq` Output

`irq` is generated in the core clock domain (`gpio_config_regs.sv`), which
is gpio_clk when CDC_ENABLE=1. `apb4_gpio.sv` (`gen_irq_sync`) then passes it
through a 2-flop synchronizer (`glitch_free_n_dff_arn`, FLOP_COUNT=2) clocked
by pclk, so the output pin is safe to consume in the pclk domain with no
external synchronizer. It is a level, so a plain synchronizer is the right
primitive; there is no handshake and no pulse stretching. The cost is two
pclk cycles of latency. When CDC_ENABLE=0 the synchronizer is bypassed
(`gen_irq_direct`) and `irq` keeps the zero-latency behaviour of the
single-clock configuration.

One contract comes with that choice. For an edge-mode pin the sticky status
bit holds `irq` asserted until software clears it, so the synchronizer
always sees it. For a level-mode pin `irq` is only as wide as the input
level itself, and a level that de-asserts within about two pclk periods
(plus the input synchronizer depth) can pass between the synchronizer's
samples and never reach the pin. The event is not lost -- GPIO_INT_STATUS
still latches it and polling sees it -- but no interrupt fires. Hold
level-mode inputs for at least two pclk periods when CDC_ENABLE=1, or use
edge mode for short pulses. With CDC_ENABLE=0 every core-clock assertion is
visible, so the constraint only exists in the asynchronous configuration.

### Coherency

- No guaranteed atomicity across clock domains
- Software must handle potential inconsistencies
- Interrupt status always reflects gpio_clk domain

### Reset Synchronization

Both resets must be asserted at power-on:
1. Assert both `presetn` and `gpio_rstn`
2. Release `gpio_rstn` first
3. Release `presetn` after gpio_clk domain stable

## Timing

### Latency

| Path | Latency |
|------|---------|
| APB write to gpio_clk-domain register | APB access + apb4_slave_cdc handshake (a few cycles of each clock) |
| APB read of gpio_clk-domain state | Same crossing, in both directions |
| Interrupt detection to IRQ | gpio_clk-domain detection (Chapter 3.3) + 2 pclk cycles through the irq synchronizer |

: Table 2.8: CDC Latency

---

## Navigation

**Back to:** [00_overview.md](00_overview.md) - Block Descriptions Overview

**Next Chapter:** [Chapter 3: Interfaces](../ch03_interfaces/00_overview.md)
