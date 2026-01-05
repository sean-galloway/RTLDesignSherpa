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

# DELTA Network Specification Index
**Distributed Execution Layer for Tensor Acceleration**
Version 0.3 - Early Proof of Concept (Draft)

---

## Document Organization

This specification describes DELTA, a configurable mesh Network-on-Chip (NoC) that routes four distinct packet types between the RAPIDS DMA engine, HIVE control system, and compute tiles.

---

## Chapter 1: Overview

[01. Executive Summary](ch01_overview/01_executive_summary.md)
[02. System Integration](ch01_overview/02_system_integration.md)
[03. Packet Type Routing](ch01_overview/03_packet_type_routing.md)
[04. Acronyms and References](ch01_overview/04_acronyms.md)

## Chapter 2: Blocks

[00. Block Overview](ch02_blocks/00_block_overview.md)
[01. Router Architecture](ch02_blocks/01_router_architecture.md)
[02. Network Interface](ch02_blocks/02_network_interface.md)
[03. Packet Classifier](ch02_blocks/03_packet_classifier.md)
[04. Virtual Channel Allocator](ch02_blocks/04_virtual_channel_allocator.md)
[05. Crossbar Switch](ch02_blocks/05_crossbar_switch.md)

## Chapter 3: Interfaces

[01. AXIS Interface Specification](ch03_interfaces/01_axis_interface_spec.md)
[02. Packet Format and Framing](ch03_interfaces/02_packet_format.md)
[03. External Entity Integration](ch03_interfaces/03_external_entities.md)

## Chapter 4: Programming Models

[01. Virtual Configuration Contexts](ch04_programming_models/01_virtual_contexts.md)
[02. Context Switching](ch04_programming_models/02_context_switching.md)
[03. Configuration Commands](ch04_programming_models/03_configuration_commands.md)
[04. Complete System Flow](ch04_programming_models/04_system_flow.md)

## Chapter 5: Registers

[01. Configuration Register Bank](ch05_registers/01_config_registers.md)
[02. Router Status Registers](ch05_registers/02_status_registers.md)
[03. Performance Counters](ch05_registers/03_performance_counters.md)

## Appendices

[Appendix A: Tile Coordinate Mapping](appendix_a_coordinates.md)
[Appendix B: Configuration Commands](appendix_b_commands.md)
[Appendix C: Performance Characteristics](appendix_c_performance.md)

---

**Document Version:** 0.3 (Early Draft - Proof of Concept)
**Last Updated:** 2025-10-19
**Status:** Preliminary specification, subject to significant change
**Maintained By:** DELTA Development Team
