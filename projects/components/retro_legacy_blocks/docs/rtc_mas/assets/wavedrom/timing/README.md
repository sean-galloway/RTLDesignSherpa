# RTC Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for RTC (Real-Time Clock)
operational scenarios. Signal names and the register map below follow the RTL
(`rtl/rtc/`), which is authoritative; see `ch05_registers/01_register_map.md`
for the full field definitions.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `rtc_time_read.json` | Time Read | APB read of current time registers |
| `rtc_time_increment.json` | Time Increment | 1 Hz tick with second/minute/hour rollover |
| `rtc_alarm_match.json` | Alarm Match | Time matching alarm setting triggers interrupt |
| `rtc_periodic_interrupt.json` | Second Tick | Fixed 1 Hz second-tick interrupt (no rate select) |

An earlier `rtc_update_in_progress` diagram was removed: this RTC has no UIP
flag or time-latch protocol. Safe reads are done by setting
RTC_CONFIG.time_set_mode (which stops the counter) or by re-reading around a
tick; see `ch04_programming`.

## Signal Hierarchy

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR[11:0]`, `s_apb_PWDATA`, `s_apb_PRDATA`,
  `s_apb_PSTRB`, `s_apb_PPROT` - Data signals

### Clocks and Reset (External)
- `pclk` / `presetn` - APB domain
- `rtc_clk` / `rtc_resetn` - 32.768 kHz crystal domain (a 1 Hz tick is derived
  internally by a fixed divide-by-32768; there is no `rtc_1hz` input)

### RTC Core (Internal)
- **Tick:** `r_divider`, `r_second_tick` (1 Hz, one `rtc_clk` cycle wide)
- **Time counters:** `r_seconds`, `r_minutes`, `r_hours`, `r_day`, `r_month`,
  `r_year` (no day-of-week; rollover cascade seconds -> minutes -> hours ->
  day/month/year)
- **Alarm:** `cfg_alarm_sec/min/hour`, `cfg_alarm_mask`, `r_alarm_match`,
  `r_alarm_flag`
- **Interrupts:** `rtc_alarm_irq = alarm flag AND alarm_int_enable`,
  `rtc_second_irq = second-tick flag AND second_int_enable` (both level,
  cleared by W1C of the RTC_STATUS flag)

## Rendering to SVG/PNG

```bash
# Render one file (both formats)
wavedrom-cli -i rtc_time_read.json -s rtc_time_read.svg -p rtc_time_read.png
```

## Scenarios Explained

### 1. Time Read
APB read transaction of RTC_SECONDS returning the current seconds value.
Simple register access pattern.

### 2. Time Increment with Rollover
Complete time cascade on the 1 Hz tick: seconds overflow increments minutes,
minutes overflow increments hours, demonstrating the 23:59:59 to 00:00:00
rollover (the day/month/year cascade continues the same way).

### 3. Alarm Match
Alarm comparison logic. The fields enabled in RTC_ALARM_MASK (seconds,
minutes, hours) must all match the current time; `r_alarm_match` then sets the
sticky alarm flag, and `rtc_alarm_irq` asserts while the flag is set and the
alarm interrupt is enabled.

### 4. Second-Tick Interrupt
The fixed 1 Hz tick from the divide-by-32768 prescaler sets the second-tick
status flag each second; `rtc_second_irq` asserts while the flag is set and
`second_int_enable` is 1. There is no programmable periodic rate - the file
name is historical.

## Register Reference

Offsets from `rtl/rtc/peakrdl/rtc_regs.rdl` (13 registers, 0x00-0x30; address
bits [5:0] decoded, reads at 0x34+ return 0 with no error):

| Register | Offset | Description |
|----------|--------|-------------|
| RTC_CONFIG | 0x00 | Enable, 12/24-hour, BCD, clock select, time-set mode |
| RTC_CONTROL | 0x04 | Alarm and interrupt enables |
| RTC_STATUS | 0x08 | Status flags (W1C: alarm, second tick) |
| RTC_SECONDS | 0x0C | Seconds (0-59) |
| RTC_MINUTES | 0x10 | Minutes (0-59) |
| RTC_HOURS | 0x14 | Hours (0-23, or 1-12 + PM in 12-hour mode) |
| RTC_DAY | 0x18 | Day of month (1-31) |
| RTC_MONTH | 0x1C | Month (1-12) |
| RTC_YEAR | 0x20 | Year (0-99, base 2000) |
| RTC_ALARM_SEC | 0x24 | Alarm seconds match value |
| RTC_ALARM_MIN | 0x28 | Alarm minutes match value |
| RTC_ALARM_HOUR | 0x2C | Alarm hours match value |
| RTC_ALARM_MASK | 0x30 | Alarm field match enables |

## References

- **RTC RTL:** `rtl/rtc/apb4_rtc.sv`, `rtl/rtc/rtc_core.sv`
- **Register source:** `rtl/rtc/peakrdl/rtc_regs.rdl`
- **RTC Testbench:** `dv/tbclasses/rtc/rtc_tb.py`
