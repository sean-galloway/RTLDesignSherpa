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

# Purpose and Scope

## Document Purpose

This Hardware Architecture Specification (HAS) defines the high-level architecture of the STREAM (Scatter-gather Transfer Rapid Engine for AXI Memory) subsystem. It serves as the primary reference for:

- **System Integration** - Understanding STREAM's external interfaces and system-level requirements
- **Performance Planning** - Evaluating throughput, latency, and resource characteristics
- **Driver Development** - Programming model and software interface requirements
- **Verification Planning** - System-level test scenarios and coverage requirements

This document complements the STREAM Micro-Architecture Specification (MAS), which provides detailed block-level implementation specifics.

---

## Scope

### In Scope

This specification covers:

1. **System Architecture**
   - Block-level functional partitioning
   - Data flow through the subsystem
   - Multi-channel operation model

2. **External Interfaces**
   - APB configuration slave interface
   - AXI4 master interfaces (descriptor fetch, data read, data write)
   - Monitor bus (MonBus) output interface

3. **Performance Characteristics**
   - Throughput targets and limiting factors
   - Latency breakdown for typical operations
   - Resource estimates for FPGA/ASIC targets

4. **Integration Requirements**
   - Clock and reset requirements
   - System-level constraints
   - Verification strategy overview

### Out of Scope

This specification does not cover:

- **Detailed Micro-Architecture** - See STREAM MAS for block-level implementation
- **RTL Implementation Details** - Register-level timing, pipeline stages
- **Testbench Architecture** - See verification documentation
- **Software Driver Implementation** - See software programming guide

---

## Design Philosophy

### Tutorial-Focused Simplicity

STREAM is intentionally designed as a beginner-friendly DMA engine tutorial. Key simplifications include:

| Aspect | Simplification | Rationale |
|--------|---------------|-----------|
| **Address Alignment** | Aligned addresses only | Eliminates complex fixup logic |
| **Transfer Length** | Specified in beats | Simplifies datapath math |
| **Descriptor Chaining** | Linear chains only | No circular buffer management |
| **Flow Control** | Simple transaction limits | No credit management complexity |

These simplifications make STREAM an ideal learning platform while maintaining production-quality RTL practices.

### Relationship to RAPIDS

STREAM is derived from the RAPIDS (Rapid AXI Programmable In-band Descriptor System) architecture but removes:

- Network interfaces (source/sink paths)
- Address alignment fixup logic
- Credit-based flow control
- Control read/write engines

This creates a pure memory-to-memory DMA engine suitable for understanding core DMA concepts.

---

## Intended Audience

| Audience | Primary Use |
|----------|-------------|
| System Architects | Evaluate STREAM for system integration |
| Hardware Engineers | Plan physical integration and timing closure |
| Software Engineers | Develop drivers and firmware |
| Verification Engineers | Plan system-level test coverage |

---

**Last Updated:** 2026-01-03
