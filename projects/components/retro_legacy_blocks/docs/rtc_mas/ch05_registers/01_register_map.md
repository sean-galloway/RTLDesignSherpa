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

# APB RTC - Register Map

The register block occupies 0x34 bytes (13 registers). Only PADDR[5:0] is
decoded, so the 13-register image REPEATS every 0x40 bytes across the 4 KB
window (0x40 aliases RTC_CONFIG, 0x4C aliases RTC_SECONDS, ...); within
each image, 0x34-0x3F reads 0 / ignores writes with no error. Aliased
WRITES are out of contract: the time-set and W1C strobes compare the full
12-bit address, so an aliased time write never loads the counters and an
aliased W1C clears only the register mirror.

Behavioral notes: the alarm compare runs on the PRE-increment counters
at the tick, so when alarm_flag sets, the time registers already read
alarm+1s. The prescaler keeps running in time_set_mode, so second_tick
status keeps setting during time-set. The alarm compare is also NOT gated
by time_set_mode -- a stopped counter matching the alarm sets alarm_flag
mid-programming (#56). With clock_select=1 (test mode)
the tick rate is pclk/100, not 1 Hz.
Two W1C hazards (#56): (1) the set sources (r_second_tick,
r_alarm_match) are registered on the COUNTER clock, so in 32.768 kHz
mode each set pulse is ~30.5 us wide -- a W1C issued inside that window
is silently undone one pclk later and the interrupt re-fires (an ISR
clearing promptly after the tick gets re-interrupted; invisible in
clock_select=1 where pulses are one pclk). (2) Independently, the
register mirror echoes the still-set core flag for one pclk after any
W1C before the registered clear lands -- a read two cycles after the
clear can still see the flag as 1.

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | RTC_CONFIG | RW | 0x00000000 | Global configuration (enable, hour/BCD/clock mode, time-set) |
| 0x04 | RTC_CONTROL | RW | 0x00000000 | Alarm and interrupt enables |
| 0x08 | RTC_STATUS | RO/W1C | 0x00000000 | Status flags and indicators |
| 0x0C | RTC_SECONDS | RW | 0x00 | Seconds (0-59) |
| 0x10 | RTC_MINUTES | RW | 0x00 | Minutes (0-59) |
| 0x14 | RTC_HOURS | RW | 0x00 | Hours (0-23, or 1-12 + PM in 12-hour mode) |
| 0x18 | RTC_DAY | RW | 0x01 | Day of month (1-31) |
| 0x1C | RTC_MONTH | RW | 0x01 | Month (1-12) |
| 0x20 | RTC_YEAR | RW | 0x00 | Year (0-99, base 2000) |
| 0x24 | RTC_ALARM_SEC | RW | 0x00 | Alarm seconds match value |
| 0x28 | RTC_ALARM_MIN | RW | 0x00 | Alarm minutes match value |
| 0x2C | RTC_ALARM_HOUR | RW | 0x00 | Alarm hours match value |
| 0x30 | RTC_ALARM_MASK | RW | 0x00 | Alarm field match enables |

All registers are 32 bits wide. In each register only the low bits listed below
are implemented; the remaining bits are reserved (read as 0).

---

## RTC_CONFIG (0x00)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | rtc_enable | RW | 0 | Master enable for the RTC (0=disabled, 1=enabled) |
| 1 | hour_mode_12 | RW | 0 | Hour format: 0=24-hour, 1=12-hour (AM/PM) |
| 2 | bcd_mode | RW | 0 | Time format: 0=binary, 1=BCD |
| 3 | clock_select | RW | 0 | Time-counter clock: 0=32.768 kHz, 1=system clock (test) |
| 4 | time_set_mode | RW | 0 | 1=allow time setting (stops the counter), 0=normal operation |
| 31:5 | Reserved | RO | 0 | Reserved |

Note that `hour_mode_12` and the format/clock controls live here, not in
RTC_CONTROL. Out of reset the counters run in **binary** mode; BCD is optional
and is selected by setting `bcd_mode`.

### Setting the time (time_set_mode protocol)

Time registers are mirrors of the internal counters: a plain write to
RTC_SECONDS..RTC_YEAR is reloaded from the counter on the next cycle unless the
time-set protocol is used. To set the time:

1. Write RTC_CONFIG with `rtc_enable = 1` and `time_set_mode = 1` (both are
   required; the load path is gated on the RTC being enabled). Also select the
   desired `hour_mode_12` and `bcd_mode`. While `time_set_mode = 1` the counter
   is stopped.
2. Write the new values to RTC_SECONDS, RTC_MINUTES, RTC_HOURS, RTC_DAY,
   RTC_MONTH, and RTC_YEAR. A write to any time register (0x0C-0x20) latches the
   full set into the counters and sets `time_valid`.
3. Write RTC_CONFIG again with `time_set_mode = 0` to resume counting.

**Known RTL deviation (#56): this protocol only works with
clock_select=1 (test mode).** The load strobe is one pclk cycle wide and
is sampled by the counter clock -- with clock_select=0 the 32.768 kHz
domain captures it with probability ~1/3000 per write, so in the
production configuration the counters effectively never load and the
RTC cannot be set (it free-runs from 2000-01-01). Until fixed, set the
time in test mode, then switch clock_select back to 0.

---

## RTC_CONTROL (0x04)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | alarm_enable | RW | 0 | Enable alarm comparison |
| 1 | alarm_int_enable | RW | 0 | Enable interrupt on alarm match |
| 2 | second_int_enable | RW | 0 | Enable interrupt every second (1 Hz tick) |
| 31:3 | Reserved | RO | 0 | Reserved |

---

## RTC_STATUS (0x08)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | alarm_flag | W1C | 0 | Alarm triggered; write 1 to clear |
| 1 | second_tick | W1C | 0 | 1 Hz tick occurred; write 1 to clear |
| 2 | time_valid | RO | 0 | Set after a time-set load, and ALSO by the first second-tick even if the time was never programmed (reads 'valid' one second after enable, showing the reset default 2000-01-01) |
| 3 | pm_indicator | RO | 0 | 12-hour mode: 0=AM, 1=PM (BCD 12-hour mode only) |
| 31:4 | Reserved | RO | 0 | Reserved |

---

## RTC_ALARM_MASK (0x30)

| Bit | Name | Access | Reset | Description |
|-----|------|--------|-------|-------------|
| 0 | sec_match_en | RW | 0 | 1=compare seconds for alarm, 0=don't care |
| 1 | min_match_en | RW | 0 | 1=compare minutes for alarm, 0=don't care |
| 2 | hour_match_en | RW | 0 | 1=compare hours for alarm, 0=don't care |
| 31:3 | Reserved | RO | 0 | Reserved |

The mask bits are active-high *match enables*, not "ignore" bits. Out of reset
all three are 0, so every field is a don't-care and an enabled alarm matches
every second. Set the relevant `*_match_en` bits for the fields that must match.

---

## Time Format

Time/date values are stored in binary by default. When `bcd_mode` (RTC_CONFIG
bit 2) is set, the same fields are stored in BCD:

| Field | Binary | BCD |
|-------|--------|-----|
| Seconds | 0-59 | 0x00-0x59 |
| Minutes | 0-59 | 0x00-0x59 |
| Hours (24-hour) | 0-23 | 0x00-0x23 |
| Hours (12-hour) | 1-12 | 0x01-0x12 |
| Day of month | 1-31 | 0x01-0x31 |
| Month | 1-12 | 0x01-0x12 |
| Year | 0-99 | 0x00-0x99 |

In 12-hour BCD mode, RTC_HOURS bit 7 carries the PM indicator.

**Known RTL deviations (issue #56) -- only binary 24-hour mode keeps a
correct calendar in the current RTL:**

- **BCD mode calendar is broken**: a width truncation in days_in_month
  reduces every month length to its ones digit (31 -> 1, 30 -> 0, 29 -> 9,
  28 -> 8), so BCD dates roll the month after at most day 9. BCD
  seconds/minutes/hours count correctly; the DATE cascade does not.
- **12-hour BCD**: AM/PM toggles and the day carries at 12:59:59 -> 1:00
  instead of 11:59:59 -> 12:00 -- pm_indicator reads inverted for one hour
  in twelve and the date changes an hour after midnight.
- **12-hour binary**: the day carries on EVERY pass through 11 -> 12 (twice
  per day) and no AM/PM state exists at all.

---

**Back to:** [RTC Specification Index](../rtc_mas_index.md)
