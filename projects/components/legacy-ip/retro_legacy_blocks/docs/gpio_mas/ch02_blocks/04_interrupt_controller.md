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

# APB GPIO - Interrupt Controller Block

## Overview

Per-pin interrupt generation with edge or level triggering and one aggregate `irq`. The logic is simple; the enable semantics are where people trip. There are two levels of enable and they don't mean the same thing — read that section twice.

### Figure 2.5: Interrupt Controller Block Diagram

![Interrupt Controller Block](../assets/mermaid/gpio_interrupt_block.png)

## Functional Description

### Interrupt Modes

#### Edge-Triggered Mode
`GPIO_INT_TYPE[i] = 0`

| GPIO_INT_POLARITY | GPIO_INT_BOTH | Trigger Condition |
|-------------------|---------------|-------------------|
| 0 | 0 | Falling edge only |
| 1 | 0 | Rising edge only |
| X | 1 | Both edges |

: Table 2.5: Edge-Triggered Modes

#### Level-Sensitive Mode
`GPIO_INT_TYPE[i] = 1`

| GPIO_INT_POLARITY | Trigger Condition |
|-------------------|-------------------|
| 0 | Active low (interrupt while pin = 0) |
| 1 | Active high (interrupt while pin = 1) |

: Table 2.6: Level-Sensitive Modes

### Edge Detection Logic

#### Figure 2.6: Edge Detection Logic

![Edge Detection Logic](../assets/mermaid/gpio_edge_detection.png)

### Interrupt Status

- Each bit in `GPIO_INT_STATUS` corresponds to one pin
- Set when the interrupt condition is detected on a pin whose
  `GPIO_INT_ENABLE` bit is 1 - events on disabled pins set nothing
  (`sts_int_pending = raw & enable` in `gpio_core.sv`)
- Cleared by writing 1 to the bit (W1C); bits latch in both edge and level
  modes until cleared
- A W1C write and a hardware event in the same cycle merge per bit
  (`next = (value | hw_set) & ~w1c_mask`, `gpio_config_regs.sv`): the event
  survives on every bit the write does not clear

### Interrupt Enable

Two levels of enable exist:

- `GPIO_INT_ENABLE[i] = 1` enables pin i. It is sampled at EVENT time: it
  gates whether a status bit sets, and (for level pins) whether the pin
  drives `irq`. Clearing it after an edge event has latched does NOT mask
  that pending interrupt at `irq`.
- `GPIO_CONTROL[1]` (global INT_ENABLE) gates the final `irq` output and is
  the only control that masks everything. It resets to 0.

### Aggregate IRQ Output

```
per-pin effective status:
  level pin (TYPE=1): raw_detector & GPIO_INT_ENABLE   (live, bypasses STATUS)
  edge  pin (TYPE=0): GPIO_INT_STATUS & GPIO_INT_ENABLE (sticky latch, re-gated)

irq = GPIO_CONTROL[1] && (| effective_status)
```

(`gpio_config_regs.sv`.) One difference from a plain `|(STATUS & ENABLE)`
remains: level pins bypass GPIO_INT_STATUS entirely, so W1C on a level pin
does not deassert `irq` while the level persists. Edge pins re-apply the
current per-pin enable, so clearing GPIO_INT_ENABLE[i] masks an
already-latched edge interrupt on pin i (the status bit stays set until W1C
and `irq` re-asserts if the enable is set again).

### Interrupt Handling Flow

1. Hardware detects condition, sets status bit
2. IRQ asserted to processor
3. Software reads `GPIO_INT_STATUS` to identify source
4. Software handles interrupt
5. Software writes 1 to status bit to clear
6. IRQ deasserts (if no other sources active)

## Design Notes

- Edge detection uses synchronized input
- Level-sensitive interrupts re-trigger if not cleared
- Status bits latch until software clears

---

## Navigation

**Next:** [05_cdc_logic.md](05_cdc_logic.md) - CDC Logic
