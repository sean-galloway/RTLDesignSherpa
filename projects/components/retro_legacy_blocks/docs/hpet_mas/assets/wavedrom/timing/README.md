# HPET Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for HPET operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `hpet_config_write.json` | Config Write | APB write to enable HPET and start counter |
| `hpet_counter_read.json` | Counter Read | APB read of main counter value |
| `hpet_timer_fire_oneshot.json` | One-Shot Fire | Timer fires once when counter reaches comparator |
| `hpet_timer_fire_periodic.json` | Periodic Fire | Timer fires repeatedly with comparator reload |
| `hpet_interrupt_clear.json` | Interrupt Clear | W1C write to clear timer interrupt |
| `hpet_timer_setup.json` | Timer Setup | Back-to-back APB writes to configure timer |
| `hpet_cdc_crossing.json` | CDC Crossing | Clock domain crossing from APB to HPET domain |

## Signal Hierarchy

The diagrams show external-to-internal signal relationships:

### Clock Domains
- **pclk**: APB clock domain (slower, 50-100 MHz typical)
- **hpet_clk**: HPET clock domain (faster, 100-500 MHz typical)

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### HPET Core (Internal)
- `hpet_enable` - Global enable from config register
- `r_main_counter` - 64-bit free-running counter
- `timer_enable[i]`, `timer_type[i]` - Per-timer configuration
- `r_timer_comparator[i]` - Timer comparator value
- `w_timer_match[i]`, `w_timer_fire[i]` - Comparator logic
- `r_interrupt_status[i]`, `timer_irq[i]` - Interrupt outputs

## Rendering to SVG

### Option 1: wavedrom-cli (Recommended)

```bash
# Install wavedrom-cli
npm install -g wavedrom-cli

# Render single file
wavedrom-cli -i hpet_config_write.json -o hpet_config_write.svg

# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" -o "${f%.json}.svg"
done
```

### Option 2: Online Editor

1. Go to https://wavedrom.com/editor.html
2. Copy JSON content from file
3. Paste into editor
4. Export as SVG

### Option 3: mermaid-cli with puppeteer

```bash
# For systems with puppeteer configured
PUPPETEER_EXECUTABLE_PATH=/usr/bin/chromium mmdc -i hpet_config_write.json -o hpet_config_write.svg
```

## Usage in Documentation

Reference these diagrams in markdown:

```markdown
### Timer Fire Timing

![One-Shot Timer Fire](../assets/wavedrom/timing/hpet_timer_fire_oneshot.svg)

The one-shot timer fires once when the main counter reaches the comparator value.
```

## Scenarios Explained

### 1. Config Write
Shows APB write transaction to HPET_CONFIG (0x004) enabling the HPET.
Demonstrates CDC delay from APB domain to HPET domain before counter starts.

### 2. Counter Read
Shows APB read transaction of HPET_COUNTER_LO (0x010).
Counter value is captured and returned on PRDATA.

### 3. One-Shot Timer Fire
Timer configured for one-shot mode (timer_type=0).
Shows counter approaching comparator, match detection, fire pulse, and interrupt assertion.

### 4. Periodic Timer Fire
Timer configured for periodic mode (timer_type=1).
Shows multiple fire events with automatic comparator advancement by period value.

### 5. Interrupt Clear
Shows W1C (Write-1-to-Clear) mechanism for HPET_STATUS register.
Writing 1 to bit[0] clears Timer0 interrupt.

### 6. Timer Setup
Shows three consecutive APB writes to configure a timer:
1. TIMER_CONFIG (0x100) - enable, int_enable, type
2. TIMER_COMPARATOR_LO (0x104) - lower 32 bits
3. TIMER_COMPARATOR_HI (0x108) - upper 32 bits

### 7. CDC Crossing
Shows 2-stage synchronizer for APB-to-HPET clock domain crossing.
Demonstrates latency between APB write completion and HPET domain effect.

## References

- **HPET RTL:** `rtl/hpet/hpet_core.sv`
- **HPET Testbench:** `dv/tbclasses/hpet/hpet_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/hpet.py`
- **Register Layouts:** `../hpet_registers.json`
