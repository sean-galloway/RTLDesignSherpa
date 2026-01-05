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

# APB HPET Micro-Architecture Specification

**Component:** APB High Precision Event Timer (HPET)
**Version:** 1.0
**Last Updated:** 2026-01-04
**Status:** Production Ready

---

## Document Organization

This MAS is organized into five chapters covering the micro-architecture of the APB HPET component:

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- [01_hpet_core.md](ch02_blocks/01_hpet_core.md) - Core timer logic (counter, comparators, FSM)
- [02_hpet_config_regs.md](ch02_blocks/02_hpet_config_regs.md) - Configuration register wrapper
- [03_hpet_regs.md](ch02_blocks/03_hpet_regs.md) - PeakRDL generated register file
- [04_apb_hpet_top.md](ch02_blocks/04_apb_hpet_top.md) - Top-level integration
- [05_fsm_summary.md](ch02_blocks/05_fsm_summary.md) - FSM state summary table

### Chapter 3: Interfaces
- [01_top_level.md](ch03_interfaces/01_top_level.md) - Top-level signal list
- [02_apb_interface_spec.md](ch03_interfaces/02_apb_interface_spec.md) - APB protocol specification
- [03_hpet_clock_interface.md](ch03_interfaces/03_hpet_clock_interface.md) - HPET clock domain interface
- [04_interrupt_interface.md](ch03_interfaces/04_interrupt_interface.md) - Timer interrupt outputs

### Chapter 4: Programming Model
- [01_initialization.md](ch04_programming/01_initialization.md) - Software initialization sequence
- [02_timer_configuration.md](ch04_programming/02_timer_configuration.md) - Configuring timers (one-shot, periodic)
- [03_interrupt_handling.md](ch04_programming/03_interrupt_handling.md) - Interrupt service routines
- [04_use_cases.md](ch04_programming/04_use_cases.md) - Common use case examples

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map and field descriptions

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-04 | RTL Design Sherpa | Initial MAS release |

: Table: Version History
