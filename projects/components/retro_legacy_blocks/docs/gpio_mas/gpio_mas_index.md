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

# APB GPIO Micro-Architecture Specification

**Component:** APB General Purpose I/O (GPIO) Controller
**Version:** 1.0
**Last Updated:** 2026-01-04
**Status:** Production Ready

---

## Document Organization

This MAS is organized into five chapters covering the micro-architecture of the APB GPIO component:

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- [01_apb_interface.md](ch02_blocks/01_apb_interface.md) - APB interface block
- [02_register_file.md](ch02_blocks/02_register_file.md) - PeakRDL register file
- [03_gpio_core.md](ch02_blocks/03_gpio_core.md) - Core GPIO logic (I/O, direction)
- [04_interrupt_controller.md](ch02_blocks/04_interrupt_controller.md) - Interrupt logic
- [05_cdc_logic.md](ch02_blocks/05_cdc_logic.md) - Optional CDC logic

### Chapter 3: Interfaces
- [00_overview.md](ch03_interfaces/00_overview.md) - Interface summary
- [01_apb_slave.md](ch03_interfaces/01_apb_slave.md) - APB protocol specification
- [02_gpio_pins.md](ch03_interfaces/02_gpio_pins.md) - GPIO pin interface
- [03_interrupt.md](ch03_interfaces/03_interrupt.md) - Interrupt output
- [04_system.md](ch03_interfaces/04_system.md) - Clock and reset interface

### Chapter 4: Programming Model
- [00_overview.md](ch04_programming/00_overview.md) - Programming overview
- [01_basic_operations.md](ch04_programming/01_basic_operations.md) - Basic I/O operations
- [02_interrupt_config.md](ch04_programming/02_interrupt_config.md) - Interrupt configuration
- [03_examples.md](ch04_programming/03_examples.md) - Programming examples
- [04_software_notes.md](ch04_programming/04_software_notes.md) - Software considerations

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map and field descriptions

---

## Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-04 | RTL Design Sherpa | Initial MAS release |

: Table: Version History
