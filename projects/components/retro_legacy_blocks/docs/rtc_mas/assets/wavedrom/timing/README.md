# RTC Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for RTC (Real-Time Clock) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `rtc_time_read.json` | Time Read | APB read of current time registers |
| `rtc_time_increment.json` | Time Increment | 1Hz tick with second/minute/hour/day rollover |
| `rtc_alarm_match.json` | Alarm Match | Time matching alarm setting triggers interrupt |
| `rtc_periodic_interrupt.json` | Periodic Int | Configurable rate periodic interrupt |
| `rtc_update_in_progress.json` | UIP Flag | Update-in-progress flag for safe time reads |

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### Clock Sources (External)
- `rtc_clk_32k` - 32.768 kHz crystal oscillator input
- `rtc_1hz` - 1Hz derived clock for time updates

### RTC Core (Internal)
- **Time Registers:** `r_seconds`, `r_minutes`, `r_hours`, `r_days`
- **Overflow Signals:** `seconds_overflow`, `minutes_overflow`, `hours_overflow`
- **Alarm:** `alarm_seconds`, `alarm_minutes`, `alarm_hours`, `alarm_enable`, `alarm_match`
- **Periodic:** `cfg_periodic_rate`, `cfg_periodic_en`, `r_periodic_counter`, `periodic_tick`
- **Status:** `update_in_progress`, `r_int_flag_pf`, `alarm_int`, `update_ended_int`

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. Time Read
Shows APB read transaction of TIME_LO register returning current seconds value. Simple register access pattern.

### 2. Time Increment with Rollover
Shows complete time cascade on 1Hz tick: seconds overflow triggers minutes increment, minutes overflow triggers hours increment, hours overflow triggers days increment. Demonstrates 23:59:59 to 00:00:00 rollover.

### 3. Alarm Match
Shows alarm comparison logic. When current time (seconds, minutes, hours) all match alarm settings, alarm_match asserts and triggers interrupt if enabled.

### 4. Periodic Interrupt
Shows periodic interrupt generator. Rate register selects frequency divider. Periodic tick generates interrupt pulses at configured rate (e.g., 1024Hz for rate=0x06).

### 5. Update-In-Progress
Shows UIP flag protocol for safe time reads. UIP asserts before time update begins, preventing software from reading inconsistent values. Software polls UIP until clear, then reads time registers.

## Register Reference

| Register | Offset | Description |
|----------|--------|-------------|
| TIME_LO | 0x00 | Seconds (0-59) |
| TIME_MID | 0x04 | Minutes (0-59) |
| TIME_HI | 0x08 | Hours (0-23) |
| DATE_LO | 0x0C | Day of month (1-31) |
| DATE_MID | 0x10 | Month (1-12) |
| DATE_HI | 0x14 | Year (0-99) |
| ALARM_SEC | 0x18 | Alarm seconds |
| ALARM_MIN | 0x1C | Alarm minutes |
| ALARM_HOUR | 0x20 | Alarm hours |
| REG_A | 0x24 | Status A (UIP, rate select) |
| REG_B | 0x28 | Control B (enables) |
| REG_C | 0x2C | Status C (interrupt flags, read-clear) |

## References

- **RTC RTL:** `rtl/rtc/apb_rtc.sv`
- **RTC Testbench:** `dv/tbclasses/rtc/rtc_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/rtc.py`
