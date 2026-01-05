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

# APB GPIO - Clocks and Reset

## Clock Signals

### pclk (APB Clock)
- **Purpose:** Primary APB bus clock
- **Usage:** APB protocol, register access
- **Typical Frequency:** 50-200 MHz

### gpio_clk (GPIO Clock)
- **Purpose:** Optional separate GPIO clock domain
- **Usage:** Only when `CDC_ENABLE=1`
- **Relationship:** Can be asynchronous to pclk

## Reset Signals

### presetn (APB Reset)
- **Type:** Active-low asynchronous reset
- **Scope:** APB interface logic
- **Behavior:** Resets APB state machine, clears pending transactions

### gpio_rstn (GPIO Reset)
- **Type:** Active-low asynchronous reset
- **Scope:** GPIO core logic
- **Usage:** Only when `CDC_ENABLE=1`
- **Behavior:** Resets GPIO outputs, interrupt state

## Reset Behavior

### Register Reset Values

| Register | Reset Value | Notes |
|----------|-------------|-------|
| GPIO_CONTROL | 0x00000000 | GPIO disabled |
| GPIO_DIRECTION | 0x00000000 | All inputs |
| GPIO_OUTPUT | 0x00000000 | Outputs low |
| GPIO_INT_ENABLE | 0x00000000 | No interrupts |
| GPIO_INT_TYPE | 0x00000000 | Edge mode |
| GPIO_INT_POLARITY | 0x00000000 | Falling/low |
| GPIO_INT_BOTH | 0x00000000 | Single edge |
| GPIO_INT_STATUS | 0x00000000 | No pending |

### Output Pin Behavior During Reset

During reset:
- `gpio_out[31:0]` = 0
- `gpio_oe[31:0]` = 0 (all high-Z)
- `irq` = 0

## Clock Domain Crossing

### When CDC_ENABLE = 0
- All logic runs on `pclk`
- `gpio_clk` input is ignored
- Connect `gpio_clk = pclk` for clean design

### When CDC_ENABLE = 1
- APB interface uses `pclk`
- GPIO core uses `gpio_clk`
- Skid buffers handle CDC
- Both resets must be asserted together at power-on

## Input Synchronization

GPIO inputs are always synchronized regardless of CDC setting:

```mermaid
flowchart LR
    A["gpio_in[i]"] --> B["FF1 (clk)"] --> C["FF2 (clk)"] --> D["synchronized_input[i]"]
```

- SYNC_STAGES parameter controls depth (default: 2)
- Prevents metastability from external signal transitions
- Adds latency equal to SYNC_STAGES clock cycles

## Timing Constraints

### Synchronous Mode
- Standard single-clock timing
- All paths constrained to pclk

### Asynchronous Mode
- Set false_path between pclk and gpio_clk domains
- Set max_delay for CDC paths
- Synchronizer FFs should have ASYNC_REG attribute

---

**Next:** [04_acronyms.md](04_acronyms.md) - Acronyms and terminology
