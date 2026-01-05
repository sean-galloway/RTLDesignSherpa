# PIT 8254 Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for PIT 8254 (Programmable Interval Timer) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `pit_mode0_terminal_count.json` | Mode 0 | Terminal count - one-shot interrupt |
| `pit_mode2_rate_generator.json` | Mode 2 | Rate generator - divide-by-N |
| `pit_mode3_square_wave.json` | Mode 3 | Square wave generator - 50% duty cycle |
| `pit_gate_control.json` | Gate Control | Gate signal suspends/resumes counting |
| `pit_readback.json` | Readback | Latch counter value while running |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### PIT Pins (External)
- `gate0`, `gate1`, `gate2` - Gate inputs (active high)
- `out0`, `out1`, `out2` - Timer outputs

### PIT Core (Internal)
- **Config:** `cfg_mode`, `cfg_count`, `cfg_rw_mode`, `cfg_bcd`
- **Counters:** `r_counter0`, `r_counter1`, `r_counter2`
- **Control:** `counting`, `reload`, `half_period`
- **Latch:** `count_latched`, `r_latch_value`, `status_latched`, `r_status_latch`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Operating Modes

### Mode 0: Terminal Count (Interrupt on Terminal Count)
- OUT initially low
- Counter counts down from loaded value
- OUT goes high when counter reaches 0
- One-shot behavior, requires reload for next cycle

### Mode 2: Rate Generator (Divide-by-N)
- OUT normally high
- OUT goes low for 1 clock when counter reaches 1
- Counter auto-reloads from initial value
- Produces periodic pulse train

### Mode 3: Square Wave Generator
- 50% duty cycle output
- OUT high for N/2 clocks, low for N/2 clocks
- Counter decrements by 2 each clock
- Auto-reload at terminal count

### Mode 1: Hardware Retriggerable One-Shot
- Similar to Mode 0 but gate rising edge retriggers

### Mode 4: Software Triggered Strobe
- OUT pulses low for 1 clock at terminal count

### Mode 5: Hardware Triggered Strobe
- Like Mode 4 but gate rising edge triggers

## Gate Signal Behavior

| Mode | Gate=0 | Gate Rising | Gate=1 |
|------|--------|-------------|--------|
| 0 | Disable counting | No effect | Enable counting |
| 1 | No effect | Reload and start | No effect |
| 2 | OUT=high, disable | Reload and start | Enable counting |
| 3 | OUT=high, disable | Reload and start | Enable counting |
| 4 | Disable counting | No effect | Enable counting |
| 5 | No effect | Reload and start | No effect |

## Readback Command

The readback command (0xC0-0xFF) latches count and/or status:
- Bit 5: Latch count (0=latch)
- Bit 4: Latch status (0=latch)
- Bits 3-1: Counter select

Status byte format:
- Bit 7: OUT state
- Bit 6: Null count (count not yet loaded)
- Bits 5-4: RW mode
- Bits 3-1: Mode
- Bit 0: BCD mode

## References

- **PIT RTL:** `rtl/pit/apb_pit_8254.sv`
- **PIT Testbench:** `dv/tbclasses/pit/pit_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/pit.py`
