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

# RTC PeakRDL Register Specification

This directory contains the SystemRDL specification for the Real-Time Clock (RTC) configuration registers.

## Files

- `rtc_regs.rdl` - SystemRDL register specification

## Generated Files

The following files are generated from the RDL specification using PeakRDL tools and are placed in the parent directory:

- `../rtc_regs.sv` - SystemVerilog register implementation
- `../rtc_regs_pkg.sv` - SystemVerilog package with register addresses and field definitions

## Generation Command

To generate the SystemVerilog files from the RDL specification:

```bash
cd $REPO_ROOT/projects/components/retro_legacy_blocks/rtl/rtc
peakrdl regblock peakrdl/rtc_regs.rdl -o rtc_regs.sv --cpuif apb4-flat
```

## Register Map Overview

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000  | RTC_CONFIG | RW | Global configuration (enable, modes) |
| 0x004  | RTC_CONTROL | RW | Control (alarm, interrupt enables) |
| 0x008  | RTC_STATUS | RW | Status flags |
| 0x00C  | RTC_SECONDS | RW | Current seconds (0-59) |
| 0x010  | RTC_MINUTES | RW | Current minutes (0-59) |
| 0x014  | RTC_HOURS | RW | Current hours (0-23 or 1-12) |
| 0x018  | RTC_DAY | RW | Current day (1-31) |
| 0x01C  | RTC_MONTH | RW | Current month (1-12) |
| 0x020  | RTC_YEAR | RW | Current year (0-99, base 2000) |
| 0x024  | RTC_ALARM_SEC | RW | Alarm seconds match |
| 0x028  | RTC_ALARM_MIN | RW | Alarm minutes match |
| 0x02C  | RTC_ALARM_HOUR | RW | Alarm hours match |
| 0x030  | RTC_ALARM_MASK | RW | Alarm field enables |

## Key Features

- **Time Tracking**: Seconds, minutes, hours, day, month, year
- **Formats**: Binary or BCD (Binary Coded Decimal)
- **Hour Modes**: 24-hour or 12-hour with AM/PM
- **Clock Sources**: 32.768 kHz crystal or system clock (for testing)
- **Alarm**: Programmable alarm with field masking
- **Interrupts**: Alarm and per-second tick interrupts
- **Leap Year**: Automatic handling (2000-2099)

## Usage Notes

1. **Time Setting**: Set `time_set_mode=1` to stop the counter before writing time values
2. **BCD Format**: In BCD mode, values like 59 are encoded as 0x59 (not 0x3B)
3. **12-Hour Mode**: In BCD 12-hour mode, bit[7] of hours register indicates PM
4. **Alarm Masking**: Use ALARM_MASK to enable/disable field comparisons

## Integration Pattern

This RTC follows the standard 3-layer architecture:

```
Layer 1: apb_rtc.sv           (APB4 interface)
         ↓
Layer 2: rtc_config_regs.sv   (Register wrapper + edge detection)
         ↓
Layer 3: rtc_core.sv          (Time counting logic)
```

The generated PeakRDL files are instantiated in `rtc_config_regs.sv`.
