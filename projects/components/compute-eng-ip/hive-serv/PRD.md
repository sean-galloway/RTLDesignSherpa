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

# Product Requirements Document (PRD)
## HIVE - Hierarchical Intelligent Vector Environment

**Version:** 0.2
**Date:** 2026-10-12
**Status:** HAS/MAS v0.2 published; Phase 1 RTL in progress (3 of 5 blocks verified, see vault hive-serv TASK-000)
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The Hierarchical Intelligent Vector Environment (HIVE) is a distributed control and monitoring subsystem that coordinates the RAPIDS DMA engine and Delta Network. It demonstrates hierarchical RISC-V processor architecture, distributed monitoring, and dynamic network reconfiguration.

### 1.1 Quick Stats

- **Architecture:** 4 major blocks (HIVE-C, SERV monitors, Control network, Config manager)
- **Processors:** 1 VexRiscv (master) + 16 SERV (monitors) = 17 RISC-V cores
- **Interfaces:** Control Network (internal), AXIS (to Delta Network)
- **Resource Budget:** 6,100 LUTs HIVE control plane (14,100 including the Delta NoC), 30 BRAM on NexysA7 100T
- **Status:** Specification phase; HAS/MAS v0.2 published 2026-10-12

### 1.2 Subsystem Goals

- **Primary:** Demonstrate hierarchical control system design patterns
- **Secondary:** Enable dynamic network reconfiguration and distributed monitoring
- **Tertiary:** Educational reference for RISC-V integration and NoC control

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### HIVE Hardware Architecture Specification (HAS) — external contract
**Location:** `projects/components/compute-eng-ip/hive-serv/docs/hive_has/`

- **[Index](docs/hive_has/hive_has_index.md)** - HAS structure
- System overview, subsystem architecture (4 blocks), interfaces & packet
  formats, programming model, performance targets, integration & verification

### HIVE Micro-Architecture Specification (MAS) — implementation intent
**Location:** `projects/components/compute-eng-ip/hive-serv/docs/hive_mas/`

- **[Index](docs/hive_mas/hive_mas_index.md)** - MAS structure
- Block-level module trees, clocking/reset, internal interfaces, cycle-level
  behavior of the key operations, verification hooks, parameters/filelists

### Other Documentation
- **README** - Quick start and integration guide (to be created)
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem
- **Tasks** - none tracked. The vault area was deleted 2026-09-27: hive has no .sv,
  no tests and no filelists, so its 24 open items described work that had not begun.
  They are in git history at `vault/Tasks/projects/components/compute-eng-ip/hive-serv/`.

> **History note:** the earlier `docs/hive_spec/` + `docs/hive_specification.md`
> drafts (v0.3) were migrated into the HAS/MAS and retired 2026-10-12; they remain
> in git history.

---

## 3. Architecture Overview

### 3.1 Top-Level Block Diagram

```
HIVE System Architecture
┌─────────────────────────────────────────────────────────────┐
│                     HIVE Control Plane                      │
│  ┌────────────────────────────────────────────────────┐    │
│  │   Block 1: HIVE-C Master Controller (VexRiscv)    │    │
│  │   - Global coordination                            │    │
│  │   - Descriptor scheduling                          │    │
│  │   - Performance aggregation                        │    │
│  └──────────────────┬─────────────────────────────────┘    │
│                     │ Block 3: Control Network              │
│          ┌──────────┴──────────┬──────────────┐           │
│          ▼          ▼          ▼              ▼           │
│  ┌──────────┐ ┌──────────┐ ... ┌──────────┐ (16×)        │
│  │ Block 2: │ │ Block 2: │     │ Block 2: │              │
│  │ SERV-0   │ │ SERV-1   │     │ SERV-15  │              │
│  │ Monitor  │ │ Monitor  │     │ Monitor  │              │
│  └────┬─────┘ └────┬─────┘     └────┬─────┘              │
│       │            │                 │                     │
│       │  Block 4: Configuration Manager                    │
│       │  - Virtual context storage                         │
│       │  - Topology switching                              │
│       └────────────┴──────────────────┘                    │
└─────────────────────────────────────────────────────────────┘
         │ AXIS Packets (CDA, PKT_CONFIG, PKT_STATUS)
         ▼
    Delta Network (4×4 Mesh) + RAPIDS DMA Engine
```

**See:** `docs/hive_has/ch02_system_overview/01_system_overview.md` and
`docs/hive_has/ch03_architecture/01_subsystem_architecture.md` for the
architecture; `docs/hive_mas/` for block internals.

### 3.2 Resource Budget (NexysA7 100T)

**FPGA Target:** Xilinx Artix-7 XC7A100T-1CSG324C

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| **Block 1: HIVE-C Controller** | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| **Block 2: SERV Monitors (16×)** | 2,000 | 2,624 | 0 | 16 | 125 LUTs per SERV |
| **Block 3: Control Network** | 1,200 | 800 | 0 | 4 | HIVE-C ↔ SERV comm |
| **Block 4: Configuration Manager** | 1,500 | 1,200 | 0 | 2 | Virtual contexts |
| **HIVE control plane subtotal** | **6,100** | **5,524** | **0** | **30** | 9.6% LUT, 22% BRAM |
| Delta Network 4×4 mesh (16 routers) | 8,000 | 6,000 | 0 | 32 | Delta-owned; see Delta HAS |
| **HIVE + NoC total** | **14,100** | **11,524** | **0** | **62** | 22% LUT, 46% BRAM |
| **Available for Compute/RAPIDS** | 49,300 | 115,276 | 240 | 73 | Remaining resources |
| **Total Budget** | **63,400** | **126,800** | **240** | **135** | 100% |

> **Correction note (2026-10-12):** earlier tables presented 14,100 LUTs as
> the "HIVE subtotal" while omitting the Delta NoC row; the NoC's 8,000 LUTs
> were silently included. The table now separates the HIVE control plane from
> the Delta NoC. The 22%-LUT / 46%-BRAM occupancy figures refer to the
> combined total.

**Key Design Constraints:**
- HIVE consumes **zero DSP blocks** (all 240 DSPs available for compute)
- HIVE's own memory footprint is 30 BRAM blocks (22%); combined with the NoC
  it is 62 (46%)
- HIVE uses **9.6% of LUTs** on its own (22% combined with the NoC)
- Leaves **78% of logic resources** for RAPIDS and Delta Network compute elements

---

## 4. Key Features

### 4.1 Hierarchical RISC-V Architecture

| Feature | Status | Description |
|---------|--------|-------------|
| VexRiscv master (HIVE-C) | note | RV32IM, 5-stage pipeline, 32KB I-mem + 32KB D-mem |
| SERV monitors (16×) | note | RV32I bit-serial, 2KB I-mem + 2KB D-mem each |
| Control network | note | Star topology, round-robin arbitration |
| Independent firmware | note | Separate binaries for HIVE-C and SERV |

### 4.2 Distributed Monitoring

| Feature | Status | Description |
|---------|--------|-------------|
| Per-tile traffic counters | note | Packet counts per direction (N/S/E/W) |
| Buffer occupancy tracking | note | Real-time FIFO fill levels |
| Congestion detection | note | Programmable thresholds, immediate alerts |
| Error detection | note | Parity errors, protocol violations |
| Periodic reporting | note | Configurable interval (default 1000 cycles) |

### 4.3 Network Reconfiguration

| Feature | Status | Description |
|---------|--------|-------------|
| Virtual configuration contexts | note | 4 pre-loaded routing modes |
| Atomic context switching | note | Deterministic latency (<25 cycles) |
| Quiesce protocol | note | Drain in-flight packets before switch |
| Broadcast configuration | note | PKT_CONFIG packets to all tiles |

### 4.4 RAPIDS Integration

| Feature | Status | Description |
|---------|--------|-------------|
| Inband descriptor injection | note | CDA packets via Delta Network to RAPIDS |
| Low-latency delivery | note | ~10-20 cycles vs. 100+ for memory-mapped |
| AXIS master interface | note | Direct injection into Delta Network |
| Completion tracking | note | PKT_STATUS packets from RAPIDS |

---

## 5. Interfaces

### 5.1 External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| **Host Interface** | Slave | 32-bit | UART/AXI4-Lite for host commands |
| **AXIS (HIVE-C TX)** | Master | 256-bit | CDA packet injection to RAPIDS |
| **AXIS (SERV TX, 16×)** | Master | 128-bit | PKT_CONFIG, PKT_STATUS injection |
| **AXIS (HIVE-C RX)** | Slave | 128-bit | PKT_STATUS from network |
| **Control Network** | Internal | 32-bit | HIVE-C ↔ SERV communication |

**See:** `docs/hive_has/ch04_interfaces/` for the complete interface,
packet-format, and register-map specifications.

### 5.2 Virtual Tile Mapping

| Virtual Tile | Entity | Connection |
|--------------|--------|------------|
| **Tile 16** | RAPIDS DMA | Edge-attached to the 4×4 mesh |
| **Tile 17** | HIVE-C Controller | Edge-attached to the 4×4 mesh |

---

## 6. Use Cases

### 6.1 Descriptor Scheduling

**Scenario:** HIVE-C receives high-level transfer command from host

**Flow:**
1. Host sends command via UART/AXI4-Lite to HIVE-C
2. HIVE-C generates 256-bit CDA descriptor
3. HIVE-C injects CDA packet via AXIS master (TUSER=2'b01, TDEST=16)
4. Delta Network routes to RAPIDS (Virtual Tile 16)
5. RAPIDS descriptor engine processes
6. Completion reported via PKT_STATUS to HIVE-C

### 6.2 Congestion Management

**Scenario:** SERV monitor detects buffer congestion on tile 7

**Flow:**
1. SERV-7 monitors router buffer occupancy
2. Threshold exceeded (buffer_occupancy > cfg_threshold)
3. SERV-7 generates PKT_STATUS alert packet
4. Alert routed to HIVE-C (Virtual Tile 17)
5. HIVE-C aggregates alerts, initiates mitigation
6. HIVE-C may trigger network reconfiguration

### 6.3 Network Reconfiguration

**Scenario:** Switch from packet-switched mesh to tree reduction mode

**Flow:**
1. HIVE-C issues CONFIG_PREPARE command via control network
2. All SERV monitors flush in-flight packets
3. Routers enter quiescent state
4. HIVE-C broadcasts SET_ROUTING_MODE (PKT_CONFIG, context=2)
5. All tiles simultaneously update routing mode
6. HIVE-C issues CONFIG_ACTIVATE command
7. Network resumes with tree reduction routing

---

## 7. Test Coverage

### 7.1 Current Status

**Overall:** Phase 1 RTL in progress (2026-10-13)

| Component | Spec Status | Implementation Status |
|-----------|-------------|----------------------|
| HIVE-C Controller | HAS/MAS v0.2 | Phase 1 in progress (descriptor_gen, axis_cda_master verified) |
| SERV Monitors | HAS/MAS v0.2 | Submodules written; top pending (TASK-000) |
| Control Network | HAS/MAS v0.2 | CN-01..03 verified; rotation scenarios blocked (TASK-000) |
| Configuration Manager | HAS/MAS v0.1 | Pending |
| Integration | HAS/MAS v0.2 | Pending |

---

## 8. Performance Targets

### 8.1 Latency Targets

- **Descriptor Injection:** < 30 cycles (HIVE-C → RAPIDS)
- **Command Response:** < 1 µs @ 100 MHz
- **Monitoring Aggregation:** < 100 cycles for all 16 SERV status reads
- **Context Switch:** < 25 cycles (including quiesce)

### 8.2 Monitoring Overhead

- **SERV Monitor Overhead:** < 5% of compute time
- **Congestion Detection Latency:** < 10 cycles
- **Periodic Reporting Interval:** 1000 cycles (configurable)

**See:** `docs/hive_has/ch06_performance/01_performance.md` for the full
target set and the tradeoff tables behind them.

---

## 9. Integration Guidelines

### 9.1 HIVE + RAPIDS + Delta Integration

```systemverilog
// Top-level integration example (architectural port names)
module system_top (
    input  logic        clk_100mhz,
    input  logic        rst_n,
    // Host interface
    input  logic [31:0] host_cmd,
    output logic [31:0] host_resp,
    // External memory (for RAPIDS)
    // ... AXI4 memory interface ...
);

    // HIVE instance
    hive_top u_hive (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .host_cmd       (host_cmd),
        .host_resp      (host_resp),
        .axis_cda_*     (hive_to_delta_cda),
        .axis_status_*  (delta_to_hive_status)
    );

    // Delta Network instance
    delta_network_4x4 u_delta (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .tile16_*       (rapids_interface),  // RAPIDS virtual tile
        .tile17_*       (hive_interface)     // HIVE-C virtual tile
    );

    // RAPIDS instance
    rapids_top u_rapids (
        .aclk           (clk_100mhz),
        .aresetn        (rst_n),
        .axis_cda_*     (rapids_interface),  // From Delta
        .m_axi_*        (memory_interface)   // To external memory
    );

endmodule
```

**See:** `docs/hive_has/ch07_integration/01_integration_and_verification.md`
for the full integration and verification strategy.

---

## 10. Development Status

### 10.1 Current Phase

**Phase: Specification** (HAS/MAS v0.2 complete, 2026-10-12)

- Hardware Architecture Specification: complete (7 chapters)
- Micro-Architecture Specification: complete (6 chapters)
- RTL: pending (roadmap in the HAS, Chapter 7)

**See:** nothing tracked -- the vault area was deleted 2026-09-27 (unstarted); the
former items are in git history.

### 10.2 Roadmap

**Near-Term (Q4 2025):**
- HIVE-C RTL implementation (Phase 1, per HAS ch.7 roadmap)
- SERV monitor wrapper implementation
- Control network implementation

**Long-Term (2026+):**
- Configuration manager implementation
- HIVE-C firmware development
- SERV firmware development
- Integration with RAPIDS and Delta
- FPGA deployment and testing

### 10.3 HIVE-C core strategy — VexRiscv now, falcon-flavored later

HIVE-C's core sits behind the `hive_c_loader` contract (AXIL loader window,
load-then-run); the LDR testplan verifies that contract, not the core. That
deliberate isolation makes the core **swappable by parameter** (`CORE_FLAVOR`,
to be recorded in the MAS): `vexriscv` is the default today, `peregrine` is
the intended successor when falcon rung 3 lands. The swap touches only the
wrapper's core-facing glue (VexRiscv native ibus/dbus cmd/rsp vs peregrine's
caches-behind-AXI4); the loader, firmware, and testplan carry over unchanged.

Two purposes, per the owner (2026-10-13):

1. **System proving ground for the falcon ladder.** Every falcon rung is
   verified in isolation (spike lockstep, riscv-formal, ISA batteries) but
   never *in a system*. HIVE-C is the vehicle: real control firmware, real
   interrupts, a real fabric — the LDR plan becomes peregrine's
   bring-up acceptance test the day its RTL exists.
2. **The "does a more powerful RV make a difference" experiment.** The PoC's
   headline latencies are fabric-bound (a stronger core will not move the
   30-cycle injection target). The differences to measure: interrupt-driven
   firmware architecture (alert-to-action latency vs polling), scheduler
   worst case under load, and headroom at the 64-SERV expansion scale.
   Same firmware, same testplan, measure the deltas — if there is no
   system-level gain, that is a finding about HIVE's workload class, not a
   failed experiment.

---

## 11. Educational Value

HIVE demonstrates:
- Hierarchical processor architecture (master + agents)
- Distributed monitoring and control
- RISC-V processor integration (VexRiscv, SERV)
- Inband control packet injection
- Dynamic network reconfiguration
- Resource budget management
- Control network design patterns

**Target Audience:**
- Advanced RTL designers
- Network-on-chip architects
- Embedded systems engineers
- RISC-V integration specialists

---

## 13. Documentation Generation

### 13.1 Generating PDF/DOCX from the Specifications

**Tool:** `bin/md_to_docx.py` (repo root) via the wrapper scripts:

```bash
cd projects/components/compute-eng-ip/hive-serv/docs
./generate_has_pdf.sh            # HIVE_HAS_v0.2.docx / .pdf
./generate_mas_pdf.sh            # HIVE_MAS_v0.2.docx / .pdf
# Optional revision override:
./generate_has_pdf.sh --rev 0.2
```

The scripts check dependencies (python-docx, PyYAML, pandoc, LibreOffice),
then invoke `md_to_docx.py` with the book's index, styles yaml, title page,
ToC, and page breaks. Built books are checked in alongside their sources.

**Requirements:** Python 3.6+, pandoc, LibreOffice (PDF export), and the
repo's `bin/md_to_docx.py`.

---

## 14. References

### 14.1 Internal Documentation

- **HIVE HAS:** `docs/hive_has/` ← **Primary external-contract reference**
- **HIVE MAS:** `docs/hive_mas/` ← **Primary implementation-intent reference**
- **Master PRD:** `/PRD.md`
- **Repository Guide:** `/CLAUDE.md`

### 14.2 Related Subsystems

- **RAPIDS:** `projects/components/dma-ip/rapids/` - DMA engine controlled by HIVE-C
- **Delta Network:** `projects/components/fabric-gen-ip/delta/` - AXIS fabric generator (the HIVE fabric; owner: same fabric as the archived NoC draft)
- **AMBA/Ocelus:** `rtl/amba/ocelus/` - Monitor infrastructure for observability
- **Common:** `rtl/common/` - Building blocks

### 14.3 External References

- **VexRiscv:** https://github.com/SpinalHDL/VexRiscv
- **SERV:** https://github.com/olofk/serv
- **RISC-V ISA:** https://riscv.org/technical/specifications/
- **AXI4-Stream:** ARM IHI 0051A
- **HIVE Reference Library** (`docs/references.md`) — annotated bibliography
  (NoC/interconnect, network processors, RISC-V, SoC integration, modeling,
  verification, FPGA practice), compiled from the owner calibre library +
  spec-cited papers 2026-10-13

---

**Document Version:** 0.2
**Last Updated:** 2026-10-12
**Review Cycle:** Monthly during active development
**Owner:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** `/PRD.md`
- **Hardware Architecture Specification:** `docs/hive_has/hive_has_index.md`
- **Micro-Architecture Specification:** `docs/hive_mas/hive_mas_index.md`
- **Quick Start:** `README.md` (to be created)
- **AI Guidance:** `CLAUDE.md`
- **Tasks:** none tracked (vault area deleted 2026-09-27, unstarted)
