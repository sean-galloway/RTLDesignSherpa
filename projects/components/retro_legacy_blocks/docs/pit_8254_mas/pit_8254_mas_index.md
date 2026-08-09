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

# APB PIT 8254 Specification - Table of Contents

**Component:** APB Programmable Interval Timer (PIT 8254)
**Version:** 1.0
**Last Updated:** 2025-11-08
**Status:** Production Ready (6/6 tests 100% passing, both configurations)

---

## Document Organization

This specification is organized into five chapters covering all aspects of the APB PIT 8254 component:

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

## Quick Navigation

### For Software Developers
- Start with [Chapter 4: Programming Model](ch04_programming/01_initialization.md)
- Reference [Chapter 5: Registers](ch05_registers/01_register_map.md)

### For Hardware Integrators
- Start with [Chapter 1: Overview](ch01_overview/01_overview.md)
- Reference [Chapter 3: Interfaces](ch03_interfaces/01_top_level.md)

### For Verification Engineers
- Start with [Chapter 2: Blocks](ch02_blocks/00_overview.md)
- See test results in [Implementation Summary](../../rtl/pit_8254/IMPLEMENTATION_SUMMARY.md)

### For System Architects
- Start with [Architecture Overview](ch01_overview/02_architecture.md)
- Reference [Use Cases](ch04_programming/02_use_cases.md)

---

## Document Conventions

### Notation
- **bold** - Important terms, signal names
- `code` - Register names, field names, code examples
- *italic* - Emphasis, notes

### Signal Naming
- `pclk` - APB clock
- `pit_clk` - PIT timer clock
- `gate_in[N]` - GATE input controls
- `timer_irq[N]` - Timer OUT/interrupt outputs

### Register Notation
- `PIT_CONFIG` - Register name
- `PIT_CONFIG[0]` - Specific bit field
- `0x000` - Register address (hexadecimal)

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-11-08 | RTL Design Sherpa | Initial production release, all tests passing |

---

## Implementation Status

### Test Results
- **Basic Tests:** 6/6 passing (100%)
- **Test Configurations:** 2/2 passing (100%)
  - Standard configuration (NUM_COUNTERS=3, CDC_ENABLE=0)
  - CDC configuration (NUM_COUNTERS=3, CDC_ENABLE=1)

### Passing Tests
1. Register Access - Read/write verification (with PIT disabled)
2. PIT Enable/Disable - Global enable control
3. Control Word Programming - Counter configuration
4. Counter Mode 0 Simple - Basic counting and terminal count
5. Multiple Counters - Concurrent counter operation
6. Status Register - Status readback verification

### Supported Features
- 3 independent 16-bit counters
- Mode 0: Interrupt on terminal count
- Binary counting (BCD not yet tested)
- LSB+MSB byte access (RW_MODE=3)
- Optional clock domain crossing
- Status readback for each counter
- Configurable GATE inputs

### Known Limitations
- Only Mode 0 currently implemented and tested
- BCD counting implemented but not yet verified
- Modes 1-5 not implemented
- Counter latching not implemented

---

## Related Documentation

- **RTL Implementation:** `../../rtl/pit_8254/`
- **Implementation Summary:** `../../rtl/pit_8254/IMPLEMENTATION_SUMMARY.md`
- **Test Suite:** `../../dv/tests/test_apb4_pit_8254.py`
- **Testbench Classes:** `../../dv/tbclasses/pit_8254/`

---

**Documentation and implementation support by Claude.**
