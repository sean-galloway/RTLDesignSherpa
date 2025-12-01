# APB RTC - Overview

## Introduction

The APB RTC is a Real-Time Clock controller with an APB slave interface. It maintains time and date with battery backup support and provides alarm and periodic interrupt capabilities.

## Key Features

### Time Keeping
- Seconds, minutes, hours (12/24-hour mode)
- Day of week, date, month, year
- Century support (2000-2099)
- Leap year calculation
- BCD format storage

### Alarm Function
- Configurable alarm time
- Second, minute, hour, date match
- Daily or specific date alarm

### Interrupt Support
- Alarm match interrupt
- Periodic interrupt (1 Hz)
- Update-ended interrupt

### Power Management
- Low-power 32.768 kHz oscillator
- Battery backup domain support
- RAM retention (optional)

## Applications

- System timekeeping
- Scheduled wake-up
- Event timestamping
- Calendar functions
- Alarm clock

## Block Diagram

![RTC Block Diagram](../assets/svg/rtc_top.svg)

## Register Summary

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x00 | RTC_SECONDS | RW | Seconds (0-59) |
| 0x04 | RTC_MINUTES | RW | Minutes (0-59) |
| 0x08 | RTC_HOURS | RW | Hours (0-23 or 1-12) |
| 0x0C | RTC_DAY | RW | Day of week (1-7) |
| 0x10 | RTC_DATE | RW | Day of month (1-31) |
| 0x14 | RTC_MONTH | RW | Month (1-12) |
| 0x18 | RTC_YEAR | RW | Year (0-99) |
| 0x1C | RTC_CENTURY | RW | Century (20-29) |
| 0x20 | RTC_ALARM_SEC | RW | Alarm seconds |
| 0x24 | RTC_ALARM_MIN | RW | Alarm minutes |
| 0x28 | RTC_ALARM_HOUR | RW | Alarm hours |
| 0x2C | RTC_ALARM_DATE | RW | Alarm date |
| 0x30 | RTC_CONTROL | RW | Control register |
| 0x34 | RTC_STATUS | RO/W1C | Status register |

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| CDC_ENABLE | 0 | Clock domain crossing |

---

**Next:** [02_architecture.md](02_architecture.md) - Architecture details
