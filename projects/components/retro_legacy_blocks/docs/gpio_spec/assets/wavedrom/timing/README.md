# GPIO Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for GPIO operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `gpio_direction_write.json` | Direction Config | APB write to GPIO_DIRECTION register |
| `gpio_output_write.json` | Output Write | APB write to GPIO_OUTPUT register |
| `gpio_input_read.json` | Input Read | APB read of synchronized GPIO_INPUT |
| `gpio_atomic_operations.json` | Atomic Ops | SET, CLEAR, TOGGLE operations |
| `gpio_input_sync.json` | Input Sync | 2-stage synchronizer pipeline |
| `gpio_rising_edge_interrupt.json` | Rising Edge Int | Edge interrupt on 0->1 transition |
| `gpio_falling_edge_interrupt.json` | Falling Edge Int | Edge interrupt on 1->0 transition |
| `gpio_level_interrupt.json` | Level Int | Level-sensitive interrupt |
| `gpio_interrupt_clear.json` | Int Clear | W1C write to clear interrupt |

## Signal Hierarchy

The diagrams show external-to-internal signal relationships:

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### GPIO Pins (External)
- `gpio_in[n]` - External input pins
- `gpio_out[n]` - External output pins
- `gpio_oe[n]` - Output enable

### GPIO Core (Internal)
- `r_gpio_direction` - Direction register (1=output)
- `r_gpio_output` - Output data register
- `w_gpio_sync` - Synchronized input (after 2-stage sync)
- `r_gpio_sync_d` - Delayed sync for edge detection
- `w_rising_edge`, `w_falling_edge` - Edge detect pulses
- `w_level_int` - Level interrupt match
- `r_raw_int`, `r_int_status` - Interrupt registers
- `irq` - Combined interrupt output

## Rendering to SVG

### Option 1: wavedrom-cli (Recommended)

```bash
# Install wavedrom-cli
npm install -g wavedrom-cli

# Render single file
wavedrom-cli -i gpio_direction_write.json > gpio_direction_write.svg

# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

### Option 2: Online Editor

1. Go to https://wavedrom.com/editor.html
2. Copy JSON content from file
3. Paste into editor
4. Export as SVG

## Usage in Documentation

Reference these diagrams in markdown:

```markdown
### Input Synchronization

![GPIO Input Sync](../assets/wavedrom/timing/gpio_input_sync.svg)

GPIO inputs are synchronized through a 2-stage synchronizer to prevent metastability.
```

## Scenarios Explained

### 1. Direction Write
Shows APB write transaction to GPIO_DIRECTION (0x004).
Configures pins as input (0) or output (1).

### 2. Output Write
Shows APB write transaction to GPIO_OUTPUT (0x008).
Demonstrates how write data flows to output pins when direction=output.

### 3. Input Read
Shows APB read transaction of GPIO_INPUT (0x000).
Synchronized input value returned on PRDATA.

### 4. Atomic Operations
Shows three atomic operations using dedicated registers:
- GPIO_SET: Sets specific bits without read-modify-write
- GPIO_CLEAR: Clears specific bits
- GPIO_TOGGLE: Inverts specific bits

### 5. Input Sync
Shows 2-stage synchronizer pipeline for metastability protection.
External async input -> sync_stage1 -> sync_stage2 (w_gpio_sync).

### 6. Rising Edge Interrupt
Edge mode (type=0), Rising (polarity=1) configuration.
Shows edge detection: sync -> delay -> XOR -> rising edge pulse -> latch.

### 7. Falling Edge Interrupt
Edge mode (type=0), Falling (polarity=0) configuration.
Shows 1->0 transition detection and interrupt assertion.

### 8. Level Interrupt
Level mode (type=1), Active-High (polarity=1) configuration.
IRQ follows input level directly (not latched).

### 9. Interrupt Clear
Shows W1C (Write-1-to-Clear) mechanism for INT_STATUS register.
Writing 1 to bit[n] clears the latched interrupt for pin[n].

## References

- **GPIO RTL:** `rtl/gpio/apb_gpio.sv`
- **GPIO Testbench:** `dv/tbclasses/gpio/gpio_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/gpio.py`
- **Register Layouts:** `../gpio_registers.json`
