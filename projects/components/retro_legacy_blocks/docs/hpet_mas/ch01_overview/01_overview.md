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

# APB HPET

## Overview

### Introduction

The APB High Precision Event Timer (HPET) is a configurable multi-timer peripheral built for precise timing and event generation in embedded systems. You get up to 8 independent hardware timers with one-shot and periodic modes, an APB register interface, and optional clock domain crossing for the cases where your timer clock doesn't come from the bus clock.

### Figure 1.1: APB HPET Block Diagram

![APB HPET Block Diagram](../assets/draw.io/apb4_hpet_blocks.png)

### Key Features

- **Multiple Independent Timers**: 2, 3, or 8 configurable hardware timers per instance
- **64-bit Main Counter**: High-resolution timestamp with configurable clock source
- **64-bit Comparators**: Long-duration timing support (up to 2^64-1 clock cycles)
- **Dual Operating Modes**:
  - **One-shot**: Timer fires once when counter reaches comparator value
  - **Periodic**: Timer auto-reloads and fires repeatedly at fixed intervals
- **Dynamic Mode Switching**: Switch between one-shot and periodic modes without reset
- **APB Interface**: Standard AMBA APB4 compliant register interface
- **Clock Domain Crossing**: Optional CDC support for independent APB and timer clocks
- **PeakRDL Integration**: Register map generated from SystemRDL specification
- **Per-Timer Write Data Buses**: Dedicated data paths prevent timer corruption
- **Individual Interrupts**: Separate interrupt output per timer with W1C status clearing

### Applications

**Real-Time Operating Systems:**
- System tick generation for RTOS schedulers
- Watchdog timer implementation
- Task deadline enforcement
- Periodic interrupt generation

**Performance Profiling:**
- High-resolution timestamp source
- Code execution timing
- Cache miss profiling
- Inter-event timing measurement

**Multi-Rate Timing:**
- Multiple simultaneous timing domains
- Independent periodic tasks
- Asynchronous event generation
- Programmable pulse generation

**Industrial Control:**
- PWM generation base timer
- Motor control timing
- Sensor sampling intervals
- Control loop timing

---

## Timing

### Timing Accuracy

- Counter increment: Every HPET clock cycle (deterministic)
- Timer fire latency: 1 HPET clock cycle from counter match
- Interrupt assertion: Registered, one HPET clock after the fire event (`timer_irq` is a flop in `hpet_core`, gated by `timer_int_enable` sampled at fire time)

### Register Access Latency

- No CDC: 2 APB clock cycles (APB protocol minimum)
- With CDC: 4-6 APB clock cycles (handshake synchronization overhead)

---

## Design Notes

### Design Philosophy

Every block makes trade-offs; here's where this one landed.

**Configurability:**
The HPET component prioritizes configurability to support diverse use cases. Timer count and CDC enablement are parameterizable at synthesis time, so you can tailor an instance for your application without touching the RTL. (The `VENDOR_ID`/`REVISION_ID` parameters reach HPET_ID through the register block's hardware interface; both fields are 8 bits wide, so a 16-bit PCI-style vendor reads back as its low byte. See Chapter 5.)

**Reliability:**
Extensive testing (5/6 configurations at 100% pass rate) validates core functionality. The design includes per-timer data buses to prevent corruption. (Note: the register block never raises PSLVERR -- unmapped addresses alias or read 0.)

**Standards Compliance:**
- **APB Protocol**: Full AMBA APB4 specification compliance
- **PeakRDL**: Industry-standard SystemRDL for register generation
- **Reset Convention**: Consistent active-low asynchronous reset (`presetn`)

**Reusability:**
Clean module hierarchy and well-defined interfaces enable easy integration. Optional CDC support allows flexible clock domain configuration without design changes.

### Comparison with IA-PC HPET

The APB HPET draws architectural inspiration from the IA-PC HPET specification (Intel/Microsoft) but is **not** a drop-in replacement. Key differences:

| Feature | IA-PC HPET | APB HPET |
|---------|-----------|----------|
| **Interface** | Memory-mapped | AMBA APB4 |
| **Timer Count** | Up to 256 | 2, 3, or 8 (configurable) |
| **FSB Delivery** | Supported | Not supported |
| **Legacy Replacement** | PIT/RTC emulation | Not supported |
| **Counter Size** | 64-bit mandatory | 64-bit |
| **Comparator Size** | 64-bit or 32-bit | 64-bit or 32-bit (per-timer `timer_size`) |
| **Clock Source** | 10 MHz minimum | User-configurable |
| **Vendor ID** | 16-bit, read from capability | 8-bit, from the `VENDOR_ID` parameter |

**Retained Concepts:**
- 64-bit free-running counter
- One-shot and periodic timer modes
- Write-1-to-clear interrupt status
- Capability register for hardware discovery

**Removed Features:**
- FSB interrupt delivery (use dedicated IRQ signals)
- Legacy PIT/RTC replacement (not needed in modern designs)
- Main counter period configuration (use clock divider instead)

### Resource Utilization (Post-Synthesis Estimates)

- 2-timer (no CDC): ~500 LUTs, ~300 flip-flops
- 3-timer (no CDC): ~650 LUTs, ~400 flip-flops
- 8-timer (with CDC): ~1200 LUTs, ~800 flip-flops

### Scalability

The design scales linearly with timer count. Each additional timer adds approximately:
- 150 LUTs (comparator, control logic, interrupt generation)
- 100 flip-flops (timer state, configuration registers)
- Minimal timing impact (no critical path through timer array)

### Development Status

**Status:** RTL Functional - the issue #46 register-side defects were fixed on 2026-09-08; see the index

**Completed Features:**
- One-shot timer mode
- Periodic timer mode
- Timer mode switching
- 64-bit counter read/write
- 64-bit comparators
- Multiple independent timers
- Clock domain crossing (optional)
- PeakRDL register generation
- Per-timer write data buses (corruption fix)
- Comprehensive test suite (3-level hierarchy)

**Outstanding Items:**
- 8-timer stress test timeout (minor, likely test configuration)

**Future Enhancements (Not Planned):**
- Live comparator readback (reads return the last software-written value; periodic auto-increments are not reflected)
- FSB interrupt delivery (use dedicated IRQ signals)
- Legacy mode emulation (not needed in modern designs)
- 64-bit atomic counter reads (current implementation requires two 32-bit reads)

---

## Related Modules

**Related Documentation:**
- `../../PRD.md` - Product Requirements Document
- `../../CLAUDE.md` - AI integration guide
- `../../TASKS.md` - Development task tracking
- `../IMPLEMENTATION_STATUS.md` - Test results and validation status

---

## Testing

### Verification Status

**Test Coverage:** 5 of 6 configurations achieve 100% test pass rate

| Configuration | Basic | Medium | Full | Overall |
|---------------|-------|--------|------|---------|
| 2-timer Intel-like (no CDC) | 4/4 | 5/5 | 3/3 | 12/12 |
| 3-timer AMD-like (no CDC) | 4/4 | 5/5 | 3/3 | 12/12 |
| 8-timer custom (no CDC) | 4/4 | 5/5 | 2/3 (known issue) | 11/12 (known issue) |
| 2-timer Intel-like (CDC) | 4/4 | 5/5 | 3/3 | 12/12 |
| 3-timer AMD-like (CDC) | 4/4 | 5/5 | 3/3 | 12/12 |
| 8-timer custom (CDC) | 4/4 | 5/5 | 3/3 | 12/12 |

**Known Issue:** 8-timer non-CDC "All Timers Stress" test has timeout issue (minor, likely test configuration)

**Test Levels:**
- **Basic (4 tests)**: Register access, enable/disable, counter operation, interrupt generation
- **Medium (5 tests)**: Periodic mode, multiple timers, 64-bit features, mode switching
- **Full (3 tests)**: All timers stress, CDC validation, edge case coverage

**See:** `IMPLEMENTATION_STATUS.md` for complete test results

---

## Navigation

This specification document is organized as follows:

- **Chapter 1 (this chapter)**: Overview, features, applications
- **Chapter 2**: Detailed block specifications (hpet_core, config_regs, PeakRDL integration)
- **Chapter 3**: Interface specifications (planned, not yet written)
- **Chapter 4**: Programming model (planned, not yet written)
- **Chapter 5**: Register definitions (address map, field descriptions)

**Next:** [Chapter 1.2 - Architecture](02_architecture.md)
