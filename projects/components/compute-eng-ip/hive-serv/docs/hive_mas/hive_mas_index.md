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

# HIVE Micro-Architecture Specification Index

**Hierarchical Intelligent Vector Environment**

**Version:** 0.2
**Date:** 2026-10-13
**Purpose:** Block-level micro-architecture specification for the HIVE
distributed control and monitoring subsystem — implementation intent for
the RTL that has not been written yet.

---

## Document Organization

**Note:** All chapters linked below for automated document generation.

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Overview

- [Design Philosophy and Machine Organization](ch01_overview/01_design_philosophy.md)
- [Clocking and Reset](ch01_overview/02_clocking_and_reset.md)

### Chapter 2: Functional Blocks

- [hive_top](ch02_blocks/01_hive_top.md)
- [hive_c_controller](ch02_blocks/02_hive_c_controller.md)
- [serv_monitor](ch02_blocks/03_serv_monitor.md)
- [control_network](ch02_blocks/04_control_network.md)
- [config_manager](ch02_blocks/05_config_manager.md)
- [Common Utilities](ch02_blocks/06_common_utilities.md)

### Chapter 3: Internal Interfaces

- [Packages and Wiring](ch03_interfaces/01_internal_interfaces.md)

### Chapter 4: Micro-Architecture Behavior

- [The Descriptor Injection Cycle](ch04_behavior/01_descriptor_injection_cycle.md)
- [The Monitoring Cycle](ch04_behavior/02_monitoring_cycle.md)
- [The Context Switch Sequence](ch04_behavior/03_context_switch_sequence.md)
- [Reset and Boot Behavior](ch04_behavior/04_reset_and_boot.md)

### Chapter 5: Verification Hooks

- [Verification Hooks and Observability](ch05_verification/01_verification_hooks.md)

### Chapter 6: Configuration

- [Parameters, Defines, and Filelists](ch06_configuration/01_configuration.md)

---

## Related Documentation

- **[HIVE HAS](../hive_has/hive_has_index.md)** - Hardware Architecture Specification (external contract)
- **[HIVE PRD](../../PRD.md)** - Product requirements and roadmap
- **[RAPIDS Beats MAS](../../../../dma-ip/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md)** - the DMA engine's internals HIVE-C drives
- **[Delta MAS](../../../../fabric-gen-ip/delta/docs/delta_mas/delta_mas_index.md)** - router/NI internals HIVE configures and monitors
- **[RISC-V Falcon Suite README](../../../riscv-ip/README.md)** - suite overview (hive-serv moved to the compute-eng-ip family 2026-10-13)

---

**Last Updated:** 2026-10-13
**Maintained By:** RTL Design Sherpa Project
