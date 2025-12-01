# APB RTC - Architecture

## High-Level Block Diagram

![RTC Architecture](../assets/svg/rtc_top.svg)

## Module Hierarchy

```
apb_rtc (Top Level)
+-- apb_slave
+-- rtc_config_regs (Register Wrapper)
|   +-- rtc_regs (PeakRDL Generated)
|
+-- rtc_core
    +-- Time Counter (seconds to century)
    +-- Alarm Comparator
    +-- Interrupt Generator
    +-- BCD Logic
```

## Data Flow

### Time Update Flow

```
32.768 kHz Clock
      |
      v
  +--------+
  | Divider |---> 1 Hz pulse
  +--------+
      |
      v
  +--------+
  | Seconds|---> Carry
  +--------+
      |
      v
  +--------+
  | Minutes|---> Carry
  +--------+
      |
      v
  [Hours, Date, Month, Year...]
```

### Alarm Match Flow

```
Time Registers --> Comparator <-- Alarm Registers
                       |
                       v
                  Match Signal --> IRQ (if enabled)
```

## Clock Domains

- APB domain (pclk): Register access
- RTC domain (32.768 kHz): Time counting
- CDC when clocks are asynchronous

---

**Next:** [03_clocks_and_reset.md](03_clocks_and_reset.md)
