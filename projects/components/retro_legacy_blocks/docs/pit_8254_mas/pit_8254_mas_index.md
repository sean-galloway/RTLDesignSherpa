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

# APB PIT 8254 Specification

**Component:** APB Programmable Interval Timer (PIT 8254)
**Version:** 1.1
**Last Updated:** 2026-09-09
**Status:** RTL Functional -- Mode 0 with 8254 GATE pause/resume, count
0 = 65536, the counter-latch command, byte-lane loads and strict address
decode with PSLVERR (issue #52 fixes, 2026-09-09). Modes 1-5 and the
read-back command are not implemented; see Known Limitations below.

---

## Overview

This is the micro architecture specification for the APB PIT 8254, an Intel 8254-compatible timer peripheral with an AMBA APB4 register interface. It's organized into five chapters that walk from "what is this block" down to "which bits do I write." Read the status line above before you read anything else -- Mode 0 is what this RTL does, and it does it the 8254 way; Modes 1-5 and the read-back command are documented here as reference material, not as things this RTL does.

> Status (2026-07-22): Chapter 1, the Chapter 2 overview, the Chapter 3 top-level signal
> list, the Chapter 4 initialization and use-case sections, and the Chapter 5 register map
> exist in this tree today. The remaining sections listed below are planned but not yet
> written; they are shown without links.

### Chapter 1: Overview
**Location:** `ch01_overview/`

- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
**Location:** `ch02_blocks/`

- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- 01_pit_core.md - Core counter logic (3 independent counters) *(planned, not yet written)*
- 02_pit_counter.md - Single counter implementation (Mode 0) *(planned, not yet written)*
- 03_pit_config_regs.md - Configuration register wrapper *(planned, not yet written)*
- 04_pit_regs.md - PeakRDL generated register file *(planned, not yet written)*
- 05_apb_pit_top.md - Top-level integration *(planned, not yet written)*

### Chapter 3: Interfaces
**Location:** `ch03_interfaces/`

- [01_top_level.md](ch03_interfaces/01_top_level.md) - Top-level signal list
- 02_apb_interface_spec.md - APB protocol specification *(planned, not yet written)*
- 03_pit_clock_interface.md - PIT clock domain interface *(planned, not yet written)*
- 04_gate_out_interface.md - GATE inputs and OUT outputs *(planned, not yet written)*

### Chapter 4: Programming Model
**Location:** `ch04_programming/`

- [01_initialization.md](ch04_programming/01_initialization.md) - Software initialization sequence
- [02_use_cases.md](ch04_programming/02_use_cases.md) - Common use case examples
- Counter-configuration and control-word sections *(planned, not yet written)*

### Chapter 5: Registers
**Location:** `ch05_registers/`

- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map and field descriptions

---

## Design Notes

### Document Conventions

**Notation:**
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

**Signal naming:**
- `pclk` - APB clock
- `pit_clk` - PIT timer clock
- `gate_in[N]` - GATE input controls
- `timer_irq[N]` - Timer OUT/interrupt outputs

**Register notation:**
- `PIT_CONFIG` - Register name
- `PIT_CONFIG[0]` - Specific bit field
- `0x000` - Register address (hexadecimal)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-11-08 | RTL Design Sherpa | Initial production release, all tests passing |
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #52 fixes: GATE pauses and resumes Mode 0 counting through a SYNC_STAGES synchronizer, a count of 0 means 65536, counter latch is the RW=00 control-word command (released by the next data read), loads honour PSTRB and the RW byte lanes on both write and read, one glitch-free load per write with a single post-terminal steady state, strict seven-register decode with PSLVERR (no aliases); remaining limitations stated as such |

---

## Testing

### Test Results
- **Suite:** 30 tests across the gate, func and full levels, run in both
  configurations -- 30/30 in all six runs (2026-09-09)
- **Test Configurations:**
  - Standard configuration (NUM_COUNTERS=3, CDC_ENABLE=0)
  - CDC configuration (NUM_COUNTERS=3, CDC_ENABLE=1, pit_clk at 7 ns
    against a 10 ns pclk so the crossing is exercised)
- The GATE pause/resume test samples the counter white-box around the GATE
  edge; an earlier draft measured it through an APB read whose own round
  trip exceeded the bound, which said nothing about the design.

### Passing Tests
1. Register Access - Read/write verification (with PIT disabled)
2. PIT Enable/Disable - Global enable control
3. Control Word Programming - Counter configuration
4. Counter Mode 0 Simple - Basic counting and terminal count
5. Multiple Counters - Concurrent counter operation
6. Status Register - Status readback verification
7. Issue #52 regression - count 0 = 65536, latch command, load at reset
   with RW=00, byte lanes, glitch-free load, no post-terminal oscillation,
   strict address decode, GATE synchronizer

### Supported Features
- 3 independent 16-bit counters
- Mode 0: Interrupt on terminal count
- Binary counting (BCD not yet tested)
- 16-bit, LSB-only and MSB-only data lanes (RW=11, 01, 10), byte-strobe correct
- Counter latch command (control word with RW=00)
- Optional clock domain crossing
- Status readback for each counter
- GATE pause/resume, synchronized through SYNC_STAGES flops

### Known Limitations
These are scope boundaries, not defects:
- Only Mode 0 is implemented. Modes 1-5 are stored and reported by
  PIT_STATUS, but every mode counts like Mode 0
- Read-back command (control word SC=11) is not implemented -- PIT_STATUS
  carries the same information as a plain register
- `PIT_CONFIG.CLOCK_SELECT` is storage only; there is one counting clock and
  no divider behind it
- After terminal count the counter parks at 0 with OUT high instead of
  wrapping the way a real 8254 does (see ch05)

---

## References

- **RTL Implementation:** `../../rtl/pit_8254/`
- **RTL README (status, deviations, test gap):** `../../rtl/pit_8254/README.md`
- **Test Suite:** `../../dv/tests/test_apb4_pit_8254.py`
- **Testbench Classes:** `../../dv/tbclasses/pit_8254/`

---

## Navigation

### For Software Developers
- Start with [Chapter 4: Programming Model](ch04_programming/01_initialization.md)
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)

### For Hardware Integrators
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Reference [Chapter 3: Interfaces](ch03_interfaces/01_top_level.md)

### For Verification Engineers
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- See test results in the [RTL README](../../rtl/pit_8254/README.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Reference [Use Cases](ch04_programming/02_use_cases.md)

---

**Documentation and implementation support by Claude.**
