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

**Version:** 0.3 (2026-11-25 -- one gatling replaces the 16 SERV monitors; four compute engines on a 2x2 Delta mesh)
**Date:** 2026-11-25
**Status:** HAS/MAS updated for v0.3 of this PRD; Phase 1 RTL in progress (3 of 5 blocks verified, see vault hive TASK-000)
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The Hierarchical Intelligent Vector Environment (HIVE) is a distributed control and monitoring subsystem that coordinates the RAPIDS DMA engine and Delta Network. It demonstrates hierarchical RISC-V processor architecture, distributed monitoring, and dynamic network reconfiguration.

### 1.1 Quick Stats

- **Architecture:** 4 major blocks (HIVE-C, engine monitor, Control network, Config manager)
- **Processors:** 1 VexRiscv (master, HIVE-C) + 1 gatling (monitor, four barrel contexts, one per compute engine) = 2 RISC-V cores
- **Compute:** 4 compute engines on a 2x2 Delta mesh (4 routers)
- **Interfaces:** Control Network (internal), AXIS (to Delta Network)
- **Resource Budget:** about 5,100 LUTs HIVE control plane (7,100 including the 2x2 Delta NoC), 16 BRAM on NexysA7 100T (estimates, section 3.2)
- **Status:** Specification phase; HAS/MAS updated 2026-11-25 for the gatling monitor

### 1.2 Subsystem Goals

- **Primary:** Demonstrate hierarchical control system design patterns
- **Secondary:** Enable dynamic network reconfiguration and distributed monitoring
- **Tertiary:** Educational reference for RISC-V integration and NoC control

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### HIVE Hardware Architecture Specification (HAS) — external contract
**Location:** `projects/components/compute-eng-ip/hive/docs/hive_has/`

- **[Index](docs/hive_has/hive_has_index.md)** - HAS structure
- System overview, subsystem architecture (4 blocks), interfaces & packet
  formats, programming model, performance targets, integration & verification

### HIVE Micro-Architecture Specification (MAS) — implementation intent
**Location:** `projects/components/compute-eng-ip/hive/docs/hive_mas/`

- **[Index](docs/hive_mas/hive_mas_index.md)** - MAS structure
- Block-level module trees, clocking/reset, internal interfaces, cycle-level
  behavior of the key operations, verification hooks, parameters/filelists

### Other Documentation
- **README** - Quick start and integration guide (to be created)
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem
- **Tasks** - `vault/tracking/projects/components/compute-eng-ip/hive/` (Phase 1
  RTL is hive TASK-000).

> **History note:** the earlier `docs/hive_spec/` + `docs/hive_specification.md`
> drafts (v0.3) were migrated into the HAS/MAS and retired 2026-10-12; they remain
> in git history.

---

## 3. Architecture Overview

### 3.1 Top-Level Block Diagram

```
HIVE System Architecture
+-------------------------------------------------------------+
|                     HIVE Control Plane                      |
|  +----------------------------------------------------+     |
|  |   Block 1: HIVE-C Master Controller (VexRiscv)     |     |
|  |   - Global coordination                            |     |
|  |   - Descriptor scheduling                          |     |
|  |   - Performance aggregation                        |     |
|  +-------------------------+--------------------------+     |
|                            | Block 3: Control Network       |
|                            | (4 slave ports, one per engine)|
|  +-------------------------v--------------------------+     |
|  |   Block 2: Engine Monitor (one gatling, 4 contexts)|     |
|  |   ctx 0      ctx 1      ctx 2      ctx 3           |     |
|  |   engine 0   engine 1   engine 2   engine 3        |     |
|  |   per engine: traffic_counter, trigger_logic,      |     |
|  |               axis_injector, ctrl_net_slave        |     |
|  +----------------------------------------------------+     |
|   Block 4: Configuration Manager                            |
|   - Virtual context storage, topology switching             |
+-------------------------------------------------------------+
         | AXIS Packets (CDA, PKT_CONFIG, PKT_STATUS)
         v
    Delta Network (2x2 mesh, 4 compute engines) + RAPIDS DMA Engine
```

**See:** `docs/hive_has/ch02_system_overview/01_system_overview.md` and
`docs/hive_has/ch03_architecture/01_subsystem_architecture.md` for the
architecture; `docs/hive_mas/` for block internals.

### 3.2 Resource Budget (NexysA7 100T)

**FPGA Target:** Xilinx Artix-7 XC7A100T-1CSG324C; **clock: 75 MHz** for every HIVE domain (HIVE-C, engine monitor, Delta), owner 2026-11-25

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| **Block 1: HIVE-C Controller** | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| **Block 2: Engine Monitor (1 gatling, 4 contexts)** | 1,900 | 1,750 | 0 | 5 | gatling_core 1,066 + gatling_mem_bram 799 LUTs as measured on gatling's Nexys A7 board build (closed at 100 MHz, above HIVE's 75 MHz); FFs are the whole board top's 1,742, an upper bound; BRAM at 4 KB per context (`MEM_WORDS=1024`, SERV's 2+2 KB): 4 banks + 1 register-file tile. 4 KB is the size for now (owner, 2026-11-25); it is one parameter, and the BRAM column follows it (gatling's 16 KB default is 17 BRAMs). The four per-engine peripheral sets are not in the row (they were not in the SERV row either) |
| **Block 3: Control Network** | 300 | 200 | 0 | 1 | HIVE-C ↔ engine monitor, 4 slave ports; scaled from the 16-slave estimate, not measured |
| **Block 4: Configuration Manager** | 1,500 | 1,200 | 0 | 2 | Virtual contexts |
| **HIVE control plane subtotal** | **5,100** | **4,050** | **0** | **16** | 8.0% LUT, 12% BRAM |
| Delta Network 2x2 mesh (4 routers) | 2,000 | 1,500 | 0 | 8 | Delta-owned; a quarter of the 4x4 estimate, not measured; see Delta HAS |
| **HIVE + NoC total** | **7,100** | **5,550** | **0** | **24** | 11% LUT, 18% BRAM |
| **Available for Compute/RAPIDS** | 56,300 | 121,250 | 240 | 111 | Remaining resources |
| **Total Budget** | **63,400** | **126,800** | **240** | **135** | 100% |

> **Correction note (2026-10-12):** earlier tables presented 14,100 LUTs as
> the "HIVE subtotal" while omitting the Delta NoC row; the NoC's 8,000 LUTs
> were silently included. The table now separates the HIVE control plane from
> the Delta NoC. The 22%-LUT / 46%-BRAM occupancy figures refer to the
> combined total.

**Key Design Constraints:**
- HIVE consumes **zero DSP blocks** (all 240 DSPs available for compute)
- HIVE's own memory footprint is 16 BRAM blocks (12%); combined with the NoC
  it is 24 (18%)
- HIVE uses **8% of LUTs** on its own (11% combined with the NoC)
- Leaves **89% of logic resources** for RAPIDS and the four compute engines
- The v0.3 numbers (2026-11-25) are estimates except the gatling row, which
  is the gatling board build's measured area

---

## 4. Key Features

### 4.1 Hierarchical RISC-V Architecture

| Feature | Status | Description |
|---------|--------|-------------|
| VexRiscv master (HIVE-C) | note | RV32IM, 5-stage pipeline, 32KB I-mem + 32KB D-mem |
| Engine monitor (1 gatling) | note | RV32I barrel, four contexts, one per compute engine; each context retires one instruction every 4 cycles (18.75 MIPS per engine at 75 MHz) from a private 4 KB program/data bank; each context reads a `MON_ID` register ({engine Delta tile ID, gatling ID, context number}) and a `TIME` register from its peripheral window |
| Control network | note | Star topology, 4 slave ports, round-robin arbitration |
| Independent firmware | note | Separate binaries for HIVE-C and the monitor; the four monitor contexts run the same image |

### 4.2 Distributed Monitoring

| Feature | Status | Description |
|---------|--------|-------------|
| Per-engine traffic counters | note | Packet counts per direction (N/S/E/W) at each engine's router |
| Buffer occupancy tracking | note | Real-time FIFO fill levels |
| Congestion detection | note | Programmable thresholds, immediate alerts |
| Error detection | note | Parity errors, protocol violations |
| Periodic reporting | note | Configurable interval (default 1000 cycles), timed from the Ocelus time base (§4.5) |

### 4.3 Network Reconfiguration

| Feature | Status | Description |
|---------|--------|-------------|
| Virtual configuration contexts | note | 4 pre-loaded routing modes |
| Atomic context switching | note | Deterministic latency (<25 cycles) |
| Quiesce protocol | note | Drain in-flight packets before switch |
| Broadcast configuration | note | PKT_CONFIG packets to all four engines |

### 4.4 RAPIDS Integration

| Feature | Status | Description |
|---------|--------|-------------|
| Inband descriptor injection | note | CDA packets via Delta Network to RAPIDS |
| Low-latency delivery | note | ~10-20 cycles vs. 100+ for memory-mapped |
| AXIS master interface | note | Direct injection into Delta Network |
| Completion tracking | note | PKT_STATUS packets from RAPIDS |

### 4.5 Observation and time base (owner, 2026-11-25)

| Feature | Status | Description |
|---------|--------|-------------|
| Ocelus monitor on gatling | note | An Ocelus monitor (`rtl/amba/ocelus/`) watches the engine monitor, as it watches the rest of the system, and reports on MonBus. gatling's own ports are not AMBA; which buses the monitor taps (the four AXIS injectors, the AXIL loader) is a MAS open item |
| Local timer | note | The Ocelus monitor's `axi_monitor_timer`: a frequency-invariant tick (`counter_freq_invariant`) and a 32-bit count. HIVE reads it into the peripheral window's `TIME` register, so firmware times its periodic reports without a cycle counter of its own |
| Global usync timer | note | One system-wide microsecond time base shared by every Ocelus monitor (rtl/amba/monitors TASK-005, open). When it lands, `TIME` reads the usync value, so engine reports and MonBus packets carry the same time |

---

## 5. Interfaces

### 5.1 External Interfaces

| Interface | Type | Width | Purpose |
|-----------|------|-------|---------|
| **Host Interface** | Slave | 32-bit | UART/AXI4-Lite for host commands |
| **AXIS (HIVE-C TX)** | Master | 256-bit | CDA packet injection to RAPIDS |
| **AXIS (monitor TX, 4×)** | Master | 128-bit | PKT_CONFIG, PKT_STATUS injection, one per engine |
| **AXIS (HIVE-C RX)** | Slave | 128-bit | PKT_STATUS from network |
| **Control Network** | Internal | 32-bit | HIVE-C ↔ engine monitor (one slave port per engine) |

**See:** `docs/hive_has/ch04_interfaces/` for the complete interface,
packet-format, and register-map specifications.

### 5.2 Virtual Tile Mapping

| Virtual Tile | Entity | Connection |
|--------------|--------|------------|
| **Tiles 0-3** | Compute engines 0-3 | The 2x2 mesh routers; engine *n* is monitored by gatling context *n* |
| **Tile 16** | RAPIDS DMA | Edge-attached to the 2x2 mesh |
| **Tile 17** | HIVE-C Controller | Edge-attached to the 2x2 mesh |

The virtual tile IDs 16 and 17 are kept from v0.2: `axis4_master.sv` drives
`RAPIDS_VTILE = 8'd16` as a constant, and Delta's virtual IDs sit above the
mesh range whatever its size.

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

**Scenario:** the engine monitor detects buffer congestion at engine 3

**Flow:**
1. Monitor context 3 polls engine 3's router buffer occupancy
   (`trigger_logic` flags it in hardware within the cycle budget)
2. Threshold exceeded (buffer_occupancy > cfg_threshold)
3. Context 3 generates a PKT_STATUS alert packet through engine 3's
   `axis_injector`
4. Alert routed to HIVE-C (Virtual Tile 17)
5. HIVE-C aggregates alerts, initiates mitigation
6. HIVE-C may trigger network reconfiguration

### 6.3 Network Reconfiguration

**Scenario:** Switch from packet-switched mesh to tree reduction mode

**Flow:**
1. HIVE-C issues CONFIG_PREPARE command via control network
2. All four monitor contexts flush in-flight packets
3. Routers enter quiescent state
4. HIVE-C broadcasts SET_ROUTING_MODE (PKT_CONFIG, context=2)
5. All four engines' routers simultaneously update routing mode
6. HIVE-C issues CONFIG_ACTIVATE command
7. Network resumes with tree reduction routing

---

## 7. Test Coverage

### 7.1 Current Status

**Overall:** Phase 1 RTL in progress (2026-10-13)

| Component | Spec Status | Implementation Status |
|-----------|-------------|----------------------|
| HIVE-C Controller | HAS/MAS v0.2 | Phase 1 in progress (descriptor_gen, axis_cda_master verified) |
| Engine Monitor | HAS/MAS v0.2 (updated 2026-11-25) | Per-engine peripherals written (from the SERV design); gatling integration and the monitor top pending (TASK-000) |
| Control Network | HAS/MAS v0.2 | CN-01..03 verified; rotation scenarios blocked (TASK-000) |
| Configuration Manager | HAS/MAS v0.1 | Pending |
| Integration | HAS/MAS v0.2 | Pending |

---

## 8. Performance Targets

### 8.1 Latency Targets

- **Descriptor Injection:** < 30 cycles (HIVE-C → RAPIDS)
- **Command Response:** < 1 µs @ 75 MHz (75 cycles)
- **Monitoring Aggregation:** < 100 cycles for all 4 engine status reads
- **Context Switch:** < 25 cycles (including quiesce)

### 8.2 Monitoring Overhead

- **Monitor Overhead:** < 5% of compute-engine time (the router taps are observation-only)
- **Congestion Detection Latency:** < 10 cycles
- **Periodic Reporting Interval:** 1000 cycles (configurable), measured on the `TIME` register

**See:** `docs/hive_has/ch06_performance/01_performance.md` for the full
target set and the tradeoff tables behind them.

---

## 9. Integration Guidelines

### 9.1 HIVE + RAPIDS + Delta Integration

```systemverilog
// Top-level integration example (architectural port names)
module system_top (
    input  logic        clk_75mhz,
    input  logic        rst_n,
    // Host interface
    input  logic [31:0] host_cmd,
    output logic [31:0] host_resp,
    // External memory (for RAPIDS)
    // ... AXI4 memory interface ...
);

    // HIVE instance
    hive_top u_hive (
        .aclk           (clk_75mhz),
        .aresetn        (rst_n),
        .host_cmd       (host_cmd),
        .host_resp      (host_resp),
        .axis_cda_*     (hive_to_delta_cda),
        .axis_status_*  (delta_to_hive_status)
    );

    // Delta Network instance
    delta_network_2x2 u_delta (
        .aclk           (clk_75mhz),
        .aresetn        (rst_n),
        .tile16_*       (rapids_interface),  // RAPIDS virtual tile
        .tile17_*       (hive_interface)     // HIVE-C virtual tile
    );

    // RAPIDS instance
    rapids_top u_rapids (
        .aclk           (clk_75mhz),
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

**See:** vault hive TASK-000 (Phase 1 RTL).

### 10.2 Roadmap

**Near-Term (Q4 2025):**
- HIVE-C RTL implementation (Phase 1, per HAS ch.7 roadmap)
- Engine monitor top: gatling integration and the per-engine peripheral sets
- Control network implementation

**Long-Term (2026+):**
- Configuration manager implementation
- HIVE-C firmware development
- Engine monitor firmware development (one image, four contexts)
- Integration with RAPIDS and Delta
- FPGA deployment and testing

### 10.3 HIVE-C core strategy — VexRiscv now, falcon-flavored later

HIVE-C's core sits behind the `hive_c_loader` contract (AXIL loader window,
load-then-run); the LDR testplan verifies that contract, not the core. That
deliberate isolation makes the core **swappable by parameter** (`CORE_FLAVOR`,
to be recorded in the MAS): `vexriscv` is the default today, `peregrine` is
the intended successor when falcon rung 3 lands. (peregrine closes at 54.1 MHz, its PRD P14, so as
HIVE-C it would need its own clock or a faster build to meet HIVE's 75 MHz.) The swap touches only the
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
   worst case under load, and headroom as the engine count grows
   (gatling's memory system takes 4 to 16 contexts).
   Same firmware, same testplan, measure the deltas — if there is no
   system-level gain, that is a finding about HIVE's workload class, not a
   failed experiment.

---

## 11. Educational Value

HIVE demonstrates:
- Hierarchical processor architecture (master + agents)
- Distributed monitoring and control
- RISC-V processor integration (VexRiscv, gatling)
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

## 12. History

- 2026-11-25: PRD 0.3. Owner: "in hive I got rid of the serv cores and
  replaced them with a single gatling for four compute engines". Owner
  answers the same day: four compute engines on a smaller Delta network
  (a 2x2 mesh) with RAPIDS and HIVE-C still edge-attached; gatling is a
  monitor like the SERVs (one context per engine: counters, triggers,
  status, alerts); and the component and its tracker area are renamed
  `hive-serv` -> `hive`, `rtl/serv_monitor/` -> `rtl/engine_monitor/`.
  Quick stats, block diagram, resource budget, interfaces, tile map,
  scenarios and performance targets updated. HIVE-C and the §10.3 core
  strategy are unchanged.
- 2026-11-25, later: owner answers to the v0.3 open items. (1) "have a
  gatlin id along with the existing hart id": each context reads `MON_ID`
  in its peripheral window, {engine Delta tile ID, gatling ID, context
  number}; gatling's core is unchanged (its `mhartid` still reads 0). The
  owner notes the engine's Delta unit already has its own unique ID, and
  that is what identifies the engine: `axis_injector` stamps it on every
  packet, so the register is for firmware that labels its reports, not for
  addressing. (2) "there should be an ocelus watching gatlin; with these
  there is a local timer and a global usync timer": §4.5; no HIVE-specific
  timer. (3) 4 KB per context for now, a one-parameter change later.
  (4) "update hive to 75mhz": every HIVE clock domain targets 75 MHz;
  §8.1's command response becomes 75 cycles. §10.3's successor core,
  peregrine, closes at 54.1 MHz (its PRD P14), below this target.
- 2026-10-12: PRD 0.2. HAS/MAS v0.2 published.

## 13. Documentation Generation

### 13.1 Generating PDF/DOCX from the Specifications

**Tool:** `bin/md_to_docx.py` (repo root) via the wrapper scripts:

```bash
cd projects/components/compute-eng-ip/hive/docs
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
- **gatling:** `projects/components/riscv-ip/gatling-rv32i/` (the monitor core)
- **RISC-V ISA:** https://riscv.org/technical/specifications/
- **AXI4-Stream:** ARM IHI 0051A
- **HIVE Reference Library** (`docs/references.md`) — annotated bibliography
  (NoC/interconnect, network processors, RISC-V, SoC integration, modeling,
  verification, FPGA practice), compiled from the owner calibre library +
  spec-cited papers 2026-10-13

---

**Document Version:** 0.3
**Last Updated:** 2026-11-25
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
