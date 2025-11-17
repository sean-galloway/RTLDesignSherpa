# Real-Time Clock (RTC)

**Status:** ✅ Implemented and Ready for Testing
**Priority:** Medium
**Address:** `0x4000_3000 - 0x4000_3FFF` (4KB window)

---

## Overview

Real-Time Clock with APB interface for system time-of-day tracking. Fully implemented with comprehensive testing infrastructure.

## Implemented Features

✅ 32.768 kHz clock input support (typical RTC crystal frequency)
✅ Seconds, minutes, hours, day, month, year tracking
✅ Alarm functionality with field masking
✅ BCD and binary counting modes
✅ 24-hour or 12-hour (AM/PM) mode
✅ Leap year handling (2000-2099)
✅ Clock source selection (32.768 kHz or system clock for testing)
✅ Second tick and alarm interrupts
✅ APB4 register interface
✅ Complete CocoTB test infrastructure

## Applications

- System time-of-day tracking
- Wake-on-alarm functionality
- Timestamp generation
- Power-aware applications
- Low-power sleep/wake systems
- Real-time operating system time base

## Files

### RTL Files
- `apb_rtc.sv` - Top-level wrapper with APB4 interface
- `rtc_core.sv` - Core RTC logic with time counting and alarm
- `rtc_config_regs.sv` - Register wrapper (PeakRDL integration)
- `rtc_regs.sv` - PeakRDL generated registers (auto-generated)
- `rtc_regs_pkg.sv` - PeakRDL generated package (auto-generated)

### Configuration Files
- `peakrdl/rtc_regs.rdl` - SystemRDL register specification
- `filelists/apb_rtc.f` - Complete compilation filelist

### Helper Scripts
- `rtc_helper.py` - Human-readable register programming helper
- `rtc_regmap.py` - Python register map (auto-generated)

### Test Infrastructure
- `../../dv/tbclasses/rtc/rtc_tb.py` - Main testbench class
- `../../dv/tbclasses/rtc/rtc_tests_basic.py` - Basic test suite
- `../../dv/tests/rtc/test_apb_rtc.py` - pytest test runner

## Architecture

The RTC follows the standard 3-layer architecture:

```
Layer 1: apb_rtc.sv           (APB4 interface)
         ↓
Layer 2: rtc_config_regs.sv   (Register wrapper + edge detection)
         ↓
Layer 3: rtc_core.sv          (Time counting logic)
```

## Register Map

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

## Usage Example

### Using RTCHelper Class

```python
from rtc_helper import RTCHelper

# Initialize
rtc = RTCHelper('rtc_regmap.py', 32, 16, 0x0, log)

# Configure for testing (binary mode, 24-hour, system clock)
rtc.configure_for_testing(start_time_seconds=0)

# Set time to 14:30:45 on 2025-06-15
rtc.set_time(hours=14, minutes=30, seconds=45, day=15, month=6, year=25)

# Configure alarm for 14:35:00
rtc.set_alarm(hours=14, minutes=35, seconds=0)
rtc.enable_alarm(True, enable_interrupt=True)

# Generate APB transactions
apb_cycles = rtc.generate_apb_cycles()
```

### Direct Register Access

```python
from rtc_tb import RTCTB

# In testbench
await tb.enable_rtc(enable=True, use_sys_clock=True)
await tb.set_time(seconds=0, minutes=0, hours=12, day=1, month=1, year=25)
time = await tb.read_time()
```

## Running Tests

```bash
# Navigate to test directory
cd projects/components/retro_legacy_blocks/dv/tests/rtc

# Run basic tests
pytest test_apb_rtc.py -v -s

# Run with waveforms
WAVES=1 pytest test_apb_rtc.py -v -s

# Run specific test
pytest test_apb_rtc.py::test_rtc_basic -v -s
```

## Development Status

- [x] SystemRDL register specification
- [x] Time counter logic implementation
- [x] Alarm logic implementation
- [x] Core RTC logic implementation
- [x] APB wrapper
- [x] Register map generation
- [x] Helper script creation
- [x] Basic testbench
- [x] Test infrastructure
- [x] Documentation

## Technical Details

### Time Keeping
- Clock divider generates 1 Hz tick from input clock
- Supports 32.768 kHz (real hardware) or system clock (testing)
- Automatic carry propagation through time fields
- Proper handling of month boundaries (28/29/30/31 days)

### Leap Year Logic
- Automatic detection for years 2000-2099
- Divisibility by 4 rule (2000 is leap year, divisible by 400)
- February automatically adjusts between 28 and 29 days

### Alarm Functionality
- Programmable match fields (seconds, minutes, hours)
- Individual field enable/disable via ALARM_MASK
- Generates interrupt when enabled and matched
- Write-1-to-clear status flag

### Counting Modes
- **Binary mode**: Standard binary counting (0-59 for seconds/minutes)
- **BCD mode**: Binary Coded Decimal (0x00-0x59)
- **24-hour mode**: Hours 0-23
- **12-hour mode**: Hours 1-12 with AM/PM flag (bit 7 in BCD mode)

## Future Enhancements

- [ ] Battery backup power domain support
- [ ] Additional alarm channels
- [ ] Day of week tracking
- [ ] Century rollover (beyond 2099)
- [ ] Precise clock calibration registers

---

**Last Updated:** 2025-11-15
**Implementation:** Complete
**Test Status:** Ready for validation
