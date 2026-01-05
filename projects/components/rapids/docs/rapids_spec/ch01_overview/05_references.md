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

# Chapter 1.5: References

## Internal Specifications

### RAPIDS Project Documentation

**[1]** RAPIDS Product Requirements Document
`projects/components/rapids/PRD.md`
Complete requirements specification for RAPIDS subsystem

**[2]** RAPIDS CLAUDE Guide
`projects/components/rapids/CLAUDE.md`
AI-specific guidance for working with RAPIDS subsystem

**[3]** RAPIDS Implementation Status
`projects/components/rapids/IMPLEMENTATION_STATUS.md`
Current development status and test results

**[4]** RAPIDS Specification Context Document
`projects/components/rapids/docs/rapids_specification_hive_context.md`
Original HIVE/Delta Network integration specification (source for this update)

### Delta Network Documentation

**[5]** Delta Network Specification v0.3
`projects/components/delta/docs/delta_spec/delta_index.md`
Complete specification for Delta Network mesh Network-on-Chip

**[6]** Delta Router Architecture
`projects/components/delta/docs/delta_spec/ch02_blocks/01_router_architecture.md`
Detailed router architecture including XY routing and virtual channels

**[7]** Delta Packet Type Routing
`projects/components/delta/docs/delta_spec/ch01_overview/03_packet_type_routing.md`
Packet type definitions (PKT_DATA, CDA, PKT_CONFIG, PKT_STATUS)

**[8]** Delta External Entities
`projects/components/delta/docs/delta_spec/ch03_interfaces/03_external_entities.md`
Integration specifications for RAPIDS and HIVE-C as virtual tiles

### HIVE-C Documentation

**[9]** HIVE-C System Specification
*(Location TBD - VexRiscv RISC-V control processor specification)*

**[10]** HIVE-C Software Guide
*(Location TBD - Firmware development guide for descriptor generation)*

### RTL Design Sherpa Project

**[11]** RTL Design Sherpa Root PRD
`/PRD.md`
Master product requirements document for repository

**[12]** RTL Design Sherpa CLAUDE Guide
`/CLAUDE.md`
Repository-wide guidance for AI-assisted development

**[13]** AMBA Protocol Documentation
`rtl/amba/PRD.md`
AMBA protocol infrastructure (AXI4, APB, AXIS monitors)

**[14]** Verification Architecture Guide
`docs/VERIFICATION_ARCHITECTURE_GUIDE.md`
Complete testbench architecture patterns and best practices

## External Standards and Specifications

### ARM AMBA Specifications

**[15]** AMBA AXI and ACE Protocol Specification (AXI4)
ARM IHI 0022E, 2013
Complete specification for AXI4 memory-mapped protocol
https://developer.arm.com/documentation/ihi0022/latest

**[16]** AMBA AXI4-Stream Protocol Specification
ARM IHI 0051A, 2010
Specification for packet-oriented streaming protocol (AXIS)
https://developer.arm.com/documentation/ihi0051/latest

**[17]** AMBA APB Protocol Specification v2.0
ARM IHI 0024C, 2010
Specification for Advanced Peripheral Bus (control/status registers)
https://developer.arm.com/documentation/ihi0024/latest

**[18]** AMBA AXI4-Lite Protocol
Subset of AXI4 specification (Chapter E1 of [15])
Simplified protocol for control/status register access

### Memory Specifications

**[19]** DDR2 SDRAM Specification
JESD79-2F, JEDEC Standard
Double Data Rate 2 SDRAM specification

**[20]** DDR3 SDRAM Specification
JESD79-3F, JEDEC Standard
Double Data Rate 3 SDRAM specification (commonly used with RAPIDS)

**[21]** DDR4 SDRAM Specification
JESD79-4C, JEDEC Standard
Double Data Rate 4 SDRAM specification

### RISC-V Architecture

**[22]** The RISC-V Instruction Set Manual, Volume I: User-Level ISA
Version 20191213, RISC-V Foundation
https://riscv.org/technical/specifications/

**[23]** VexRiscv RISC-V CPU Core
GitHub: SpinalHDL/VexRiscv
Open-source RISC-V implementation (used in HIVE-C)
https://github.com/SpinalHDL/VexRiscv

### Verification and Testbench

**[24]** CocoTB Documentation
Coroutine-based cosimulation testbench environment for Python
https://docs.cocotb.org/

**[25]** Verilator Manual
Fast Verilog/SystemVerilog simulator
https://verilator.org/guide/latest/

## Design Patterns and Best Practices

### Network-on-Chip Design

**[26]** Dally, W.J. and Towles, B., "Principles and Practices of Interconnection Networks"
Morgan Kaufmann, 2004
Foundational text for NoC design principles

**[27]** Duato, J., Yalamanchili, S., and Ni, L., "Interconnection Networks: An Engineering Approach"
Morgan Kaufmann, 2002
Deadlock-free routing algorithms (XY routing used in Delta Network)

### DMA and Scatter-Gather

**[28]** PCI Express Base Specification Revision 4.0
PCI-SIG, 2017
Reference for descriptor-based DMA patterns

**[29]** Intel I/O Acceleration Technology (I/OAT) Specification
Intel Corporation
Advanced DMA engine architecture (industry reference)

### Clock Domain Crossing

**[30]** Cummings, C.E., "Clock Domain Crossing (CDC) Design & Verification Techniques Using SystemVerilog"
SNUG 2008
Best practices for CDC FIFO design

**[31]** Cummings, C.E., "Synthesis and Scripting Techniques for Designing Multi-Asynchronous Clock Designs"
SNUG 2001
Gray code counters for async FIFO pointers

## Related Projects

### RTL Design Examples

**[32]** OpenPiton Research Platform
Princeton University
Open-source manycore processor with mesh NoC
https://parallel.princeton.edu/openpiton/

**[33]** LowRISC Ibex Core
lowRISC CIC
Open-source RISC-V processor (similar class to VexRiscv)
https://github.com/lowRISC/ibex

**[34]** Ariane RISC-V CPU
ETH Zurich
High-performance 64-bit RISC-V processor
https://github.com/openhwgroup/cva6

### Verification Frameworks

**[35]** PyUVM
Python implementation of UVM (Universal Verification Methodology)
https://github.com/pyuvm/pyuvm

**[36]** cocotb-coverage
Functional coverage library for CocoTB
https://github.com/mciepluc/cocotb-coverage

## Document Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 0.1 | 2025-10-19 | Documentation Team | Initial creation with HIVE/Delta Network context |

---

**Next:** [Block Overview](../../ch02_blocks/00_overview.md)

**Previous:** [Acronyms](04_acronyms.md)

**Back to:** [Index](../rapids_index.md)
