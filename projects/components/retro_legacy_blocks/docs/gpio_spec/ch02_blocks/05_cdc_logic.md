# APB GPIO - CDC Logic Block

## Overview

Optional clock domain crossing logic enables GPIO core to run on a separate clock from the APB interface.

## Block Diagram

![CDC Logic Block](../assets/svg/gpio_cdc.svg)

## Configuration

### Parameter: CDC_ENABLE

| Value | Behavior |
|-------|----------|
| 0 | Single clock domain, all logic on pclk |
| 1 | Dual clock domain, GPIO core on gpio_clk |

## Clock Domains

### When CDC_ENABLE = 0

```
        pclk domain
+---------------------------+
|  APB Interface            |
|  Register File            |
|  GPIO Core                |
|  Interrupt Logic          |
+---------------------------+
```

### When CDC_ENABLE = 1

```
   pclk domain          gpio_clk domain
+---------------+      +------------------+
|  APB Interface|      |  GPIO Core       |
|  Register File|<---->|  Interrupt Logic |
+---------------+ CDC  +------------------+
```

## CDC Implementation

### APB to GPIO Direction

Register values synchronized to gpio_clk domain:
- `gpio_direction`
- `gpio_output`
- `gpio_int_enable`
- `gpio_int_type`
- `gpio_int_polarity`
- `gpio_int_both`

### GPIO to APB Direction

Status values synchronized to pclk domain:
- `gpio_input` (synchronized input values)
- `gpio_int_status` (interrupt status)

## Synchronization Method

### Control Signals
Dual flip-flop synchronizers for single-bit controls.

### Multi-bit Data
Skid buffers with handshake protocol for register transfers.

## Timing Considerations

### Latency

| Path | Latency |
|------|---------|
| Register write to GPIO output | 2-4 gpio_clk cycles |
| GPIO input to register read | 2-4 pclk cycles |
| Interrupt detection to IRQ | 2-4 pclk cycles |

### Coherency

- No guaranteed atomicity across clock domains
- Software must handle potential inconsistencies
- Interrupt status always reflects gpio_clk domain

## Reset Synchronization

Both resets must be asserted at power-on:
1. Assert both `presetn` and `gpio_rstn`
2. Release `gpio_rstn` first
3. Release `presetn` after gpio_clk domain stable

---

**Back to:** [00_overview.md](00_overview.md) - Block Descriptions Overview

**Next Chapter:** [Chapter 3: Interfaces](../ch03_interfaces/00_overview.md)
