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

# Delta Micro-Architecture Specification Index

**Component:** Delta (AXI4-Stream Crossbar Generator)
**Version:** 1.0
**Date:** 2026-10-12
**Purpose:** Detailed micro-architecture specification for the generated Delta RTL

---

## Overview

Delta is a Python generator that emits a single self-contained SystemVerilog module per configuration — a flat M×N AXI4-Stream crossbar routing `s_axis_*` masters to `m_axis_*` slaves. This is the internals document: the one you open when you need to know what the generated RTL actually does, block by block, rather than what the high-level spec says.

### Key Features

- **Flat crossbar (implemented); mesh cell (implemented):** The checked-in RTL includes both the flat TDEST crossbar and the `delta_mesh_cell` mesh generator mode. The mesh RTL is in `rtl/delta_mesh_cell.sv` and `rtl/delta_mesh_fabric_4x4x1.sv`; the hardware architecture is documented in [Delta HAS](../delta_has/delta_has_index.md), implemented 2026-10-15/16. Tree generation was retired on 2026-10-12. *(Verified 2026-10-19.)*
- **TDEST-based routing:** No address map; the destination slave is taken directly from `s_axis_tdest`.
- **Packet-atomic round-robin arbitration:** A granted master holds the slave until `TLAST`.
- **Combinational data mux:** The grant is the registered stage; payload passes through combinatorially.
- **Optional richness:** `TSTRB` byte qualifiers, and AMBA 5 `TWAKEUP` with the IHI 0051B ch. 5 odd-parity check signals (`TDATACHK` ... `TWAKEUPCHK`), checked at every port with sticky error flags (default off).
- **Optional counters:** Per-master and per-slave packet counters (disable with `--no-counters`).
- **Formal assertions:** `ifdef FORMAL` checks for one-hot grants and in-range TDEST.

### Companion Specifications

- **[Delta HAS](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/delta/docs/delta_has/delta_has_index.md)** - Hardware Architecture Specification (high-level)
- **[PRD.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/PRD.md)** - Product requirements and overview
- **[CLAUDE.md](https://github.com/sean-galloway/RTLDesignSherpa/blob/main/projects/components/fabric-gen-ip/CLAUDE.md)** - AI development guide

---

## Navigation

### Front Matter

- [Document Information](ch00_front_matter/00_document_info.md)

### Chapter 1: Introduction

- [Overview](ch01_introduction/01_overview.md)

### Chapter 2: Block Descriptions

- [Request Decode](ch02_blocks/01_request_decode.md)
- [Per-Slave Round-Robin Arbiter](ch02_blocks/02_arbitration.md)
- [Crossbar Multiplexer](ch02_blocks/03_crossbar_mux.md)
- [TREADY Steering](ch02_blocks/04_backpressure.md)
- [TWAKEUP Steering (AMBA5)](ch02_blocks/05_wakeup.md)
- [Interface Check Signals (AMBA5)](ch02_blocks/08_interface_check.md)
- [Packet Counters](ch02_blocks/06_counters.md)
- [Assertions](ch02_blocks/07_assertions.md)

### Chapter 3: Cycle-Level Behavior

- [Multi-Master Contention](ch03_cycle_behavior/01_arbitration_examples.md)
- [Packet Interleave Prevention](ch03_cycle_behavior/02_interleave_prevention.md)

### Chapter 4: Generated RTL

- [Module Structure](ch04_generated_rtl/01_module_structure.md)
- [Parameters and Logic Implications](ch04_generated_rtl/02_parameters.md)

### Chapter 5: Verification

- [Test Strategy](ch05_verification/01_test_strategy.md)

### Chapter 6: Mesh Cell Microarchitecture

> **IMPLEMENTED:** The `delta_mesh_cell` microarchitecture described in this chapter is now implemented in `rtl/delta_mesh_cell.sv` and `rtl/delta_mesh_fabric_4x4x1.sv`. The hardware architecture is documented in [Delta HAS](../delta_has/delta_has_index.md). *(Verified 2026-10-19.)*

- [Buffers and Virtual Channels](ch06_mesh_cell/01_buffers_and_vcs.md)
- [Pipeline Stages](ch06_mesh_cell/02_pipeline.md)
- [Routing Table](ch06_mesh_cell/03_routing_table.md)
- [Allocators](ch06_mesh_cell/04_allocators.md)
- [QoS Mechanisms](ch06_mesh_cell/05_qos_mechanisms.md)
- [Multicast Path](ch06_mesh_cell/06_multicast_path.md)
- [Observability Counters and DFT](ch06_mesh_cell/07_counters_and_dft.md)
- [Verification Targets](ch06_mesh_cell/08_verification_targets.md)

---

**Last Updated:** 2026-10-19
**Maintained By:** RTL Design Sherpa Project
