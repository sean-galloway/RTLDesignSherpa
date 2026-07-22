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

**Version:** 0.1
**Date:** 2025-10-19
**Status:** Early Specification Phase
**Owner:** RTL Design Sherpa Project
**Parent Document:** `/PRD.md`

---

## 1. Executive Summary

The Hierarchical Intelligent Vector Environment (HIVE) is a distributed control and monitoring subsystem that coordinates the RAPIDS DMA engine and Delta Network. It demonstrates hierarchical RISC-V processor architecture, distributed monitoring, and dynamic network reconfiguration.

### 1.1 Quick Stats

- **Architecture:** 4 major blocks (HIVE-C, SERV monitors, Control network, Config manager)
- **Processors:** 1 VexRiscv (master) + 16 SERV (monitors) = 17 RISC-V cores
- **Interfaces:** Control Network (internal), AXIS (to Delta Network)
- **Resource Budget:** 22% LUTs, 46% BRAM on NexysA7 100T
- **Status:** Early specification phase

### 1.2 Subsystem Goals

- **Primary:** Demonstrate hierarchical control system design patterns
- **Secondary:** Enable dynamic network reconfiguration and distributed monitoring
- **Tertiary:** Educational reference for RISC-V integration and NoC control

---

## 2. Documentation Structure

This PRD provides a high-level overview. **Detailed specifications are maintained separately:**

### 📚 Complete HIVE Specification
**Location:** `projects/components/hive/docs/hive_spec/`

- **[Index](docs/hive_spec/hive_index.md)** - Complete specification structure

#### Chapter 1: Overview
- [Overview](docs/hive_spec/ch01_overview/01_overview.md)
- [Architecture Requirements](docs/hive_spec/ch01_overview/02_architectural_requirements.md)
- [Clocking and Reset](docs/hive_spec/ch01_overview/03_clocks_and_reset.md)
- [Acronyms](docs/hive_spec/ch01_overview/04_acronyms.md)
- [References](docs/hive_spec/ch01_overview/05_references.md)

#### Chapter 2: Block Specifications
- [Blocks Overview](docs/hive_spec/ch02_blocks/00_overview.md)
- HIVE-C Controller (VexRiscv master), SERV Monitor (per-tile monitoring),
  Control Network (HIVE-C ↔ SERV), Configuration Manager (topology switching) -
  chapter files 2.1-2.4 are planned; content currently lives in
  [hive_specification.md](docs/hive_specification.md) sections 2 and 4-6

#### Chapters 3-5: Interfaces, Programming, and Performance
- Chapter files are planned but not yet written; see
  [hive_specification.md](docs/hive_specification.md) sections 2-3 (interfaces),
  6 (programming), and 7 (performance)

### 📖 Other Documentation
- **[README](README.md)** - Quick start and integration guide (to be created)
- **[CLAUDE](CLAUDE.md)** - AI assistance guide for this subsystem
- **[TASKS](TASKS.md)** - Current work items (to be created)

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

**📖 See:** `docs/hive_spec/ch02_blocks/00_overview.md` for detailed architecture

### 3.2 Resource Budget (NexysA7 100T)

**FPGA Target:** Xilinx Artix-7 XC7A100T-1CSG324C

| Component | LUTs | FFs | DSPs | BRAM (36Kb) | Notes |
|-----------|------|-----|------|-------------|-------|
| **Block 1: HIVE-C Controller** | 1,400 | 900 | 0 | 8 | VexRiscv "Small" config |
| **Block 2: SERV Monitors (16×)** | 2,000 | 2,624 | 0 | 16 | 125 LUTs per SERV |
| **Block 3: Control Network** | 1,200 | 800 | 0 | 4 | HIVE-C ↔ SERV comm |
| **Block 4: Configuration Manager** | 1,500 | 1,200 | 0 | 2 | Virtual contexts |
| **HIVE Subtotal** | **14,100** | **11,524** | **0** | **62** | 22% LUT, 46% BRAM |
| **Available for Compute/RAPIDS** | 49,300 | 115,276 | 240 | 73 | Remaining resources |
| **Total Budget** | **63,400** | **126,800** | **240** | **135** | 100% |

**Key Design Constraints:**
- HIVE consumes **zero DSP blocks** (all 240 DSPs available for compute)
- HIVE uses **46% of BRAM** (memory-intensive for instruction/data storage)
- HIVE uses **22% of LUTs** (control logic overhead acceptable)
- Leaves **78% of logic resources** for RAPIDS and Delta Network compute elements

---

## 4. Key Features

### 4.1 Hierarchical RISC-V Architecture

| Feature | Status | Description |
|---------|--------|-------------|
| VexRiscv master (HIVE-C) | 📝 | RV32IM, 5-stage pipeline, 32KB I-mem + 32KB D-mem |
| SERV monitors (16×) | 📝 | RV32I bit-serial, 2KB I-mem + 2KB D-mem each |
| Control network | 📝 | Star topology, round-robin arbitration |
| Independent firmware | 📝 | Separate binaries for HIVE-C and SERV |

### 4.2 Distributed Monitoring

| Feature | Status | Description |
|---------|--------|-------------|
| Per-tile traffic counters | 📝 | Packet counts per direction (N/S/E/W) |
| Buffer occupancy tracking | 📝 | Real-time FIFO fill levels |
| Congestion detection | 📝 | Programmable thresholds, immediate alerts |
| Error detection | 📝 | Parity errors, protocol violations |
| Periodic reporting | 📝 | Configurable interval (default 1000 cycles) |

### 4.3 Network Reconfiguration

| Feature | Status | Description |
|---------|--------|-------------|
| Virtual configuration contexts | 📝 | 4 pre-loaded routing modes |
| Atomic context switching | 📝 | Deterministic latency (<25 cycles) |
| Quiesce protocol | 📝 | Drain in-flight packets before switch |
| Broadcast configuration | 📝 | PKT_CONFIG packets to all tiles |

### 4.4 RAPIDS Integration

| Feature | Status | Description |
|---------|--------|-------------|
| Inband descriptor injection | 📝 | CDA packets via Delta Network to RAPIDS |
| Low-latency delivery | 📝 | ~10-20 cycles vs. 100+ for memory-mapped |
| AXIS master interface | 📝 | Direct injection into Delta Network |
| Completion tracking | 📝 | PKT_STATUS packets from RAPIDS |

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

**📖 See:** `docs/hive_specification.md` sections 2-3 for complete interface specs (the `docs/hive_spec/ch03_interfaces/` chapter files are not yet written)

### 5.2 Virtual Tile Mapping

| Virtual Tile | Entity | Connection |
|--------------|--------|------------|
| **Tile 16** | RAPIDS DMA | Router 12 south port |
| **Tile 17** | HIVE-C Controller | Router 3 north port |

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

**Overall:** Early specification phase - implementation pending

| Component | Spec Status | Implementation Status |
|-----------|-------------|----------------------|
| HIVE-C Controller | ✅ Complete | ⏳ Pending |
| SERV Monitors | ✅ Complete | ⏳ Pending |
| Control Network | ✅ Complete | ⏳ Pending |
| Configuration Manager | ✅ Complete | ⏳ Pending |
| Integration | ⏳ In progress | ⏳ Pending |

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

---

## 9. Integration Guidelines

### 9.1 HIVE + RAPIDS + Delta Integration

```systemverilog
// Top-level integration example
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

---

## 10. Development Status

### 10.1 Current Phase

**Phase: Specification** (In Progress)

- ✅ Chapter 1 (Overview) complete
- ✅ Chapter 2 (Blocks) in progress
- ⏳ Chapter 3 (Interfaces) pending
- ⏳ Chapter 4 (Programming) pending
- ⏳ Chapter 5 (Performance) pending

**📖 See:** `TASKS.md` for detailed work items (to be created)

### 10.2 Roadmap

**Near-Term (Q4 2025):**
- ⏳ Complete specification chapters
- ⏳ HIVE-C RTL implementation
- ⏳ SERV monitor wrapper implementation
- ⏳ Control network implementation

**Long-Term (2026+):**
- Configuration manager implementation
- HIVE-C firmware development
- SERV firmware development
- Integration with RAPIDS and Delta
- FPGA deployment and testing

---

## 11. Educational Value

HIVE demonstrates:
- ✅ Hierarchical processor architecture (master + agents)
- ✅ Distributed monitoring and control
- ✅ RISC-V processor integration (VexRiscv, SERV)
- ✅ Inband control packet injection
- ✅ Dynamic network reconfiguration
- ✅ Resource budget management
- ✅ Control network design patterns

**Target Audience:**
- Advanced RTL designers
- Network-on-chip architects
- Embedded systems engineers
- RISC-V integration specialists

---

## 12. Attribution and Contribution Guidelines

### 12.1 Git Commit Attribution

When creating git commits for HIVE documentation or implementation:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** HIVE documentation and organization receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

## 13. Documentation Generation

### 13.1 Generating PDF/DOCX from Specification

**Tool:** `bin/md_to_docx.py` (repo root)

Use this tool to convert the linked specification index into a single all-inclusive PDF or DOCX file. The preferred entry point is the wrapper script `projects/components/hive/docs/generate_pdf.sh`. Note: no built HIVE_Specification docx/pdf is checked in - generate it on demand.

**Basic Usage:**

```bash
# Preferred: use the wrapper script (from the docs/ directory)
cd projects/components/hive/docs
./generate_pdf.sh --rev 0.25
# Outputs: HIVE_Specification_v0.25.docx and HIVE_Specification_v0.25.pdf

# Direct md_to_docx.py invocation (from repo root)
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o projects/components/hive/docs/HIVE_Specification_v0.25.docx \
    --toc \
    --title-page \
    --pdf
```

**Key Features:**
- **Recursive Collection:** Follows all markdown links in the index file
- **Heading Demotion:** Automatically adjusts heading levels for included files
- **Table of Contents:** `--toc` flag generates automatic ToC
- **Title Page:** `--title-page` flag creates title page from first heading
- **PDF Export:** `--pdf` flag generates both DOCX and PDF
- **Image Support:** Resolves images relative to source directory
- **Template Support:** Optional custom DOCX/DOTX template via `-t` flag

**Common Workflow:**

```bash
# 1. Update version number in index file (hive_index.md)
# 2. Generate documentation (from repo root)
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o projects/components/hive/docs/HIVE_Specification_v0.25.docx \
    --toc --title-page --pdf

# 3. Output files created:
#    - HIVE_Specification_v0.25.docx
#    - HIVE_Specification_v0.25.pdf (if --pdf used)
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/hive/docs/hive_spec/hive_index.md \
    -o output.docx \
    --debug-md

# This creates debug.md showing the complete merged content
```

**Tool Requirements:**
- Python 3.6+
- Pandoc installed and in PATH
- For PDF generation: LaTeX (e.g., texlive) or use Pandoc's built-in PDF writer

**📖 See:** `bin/md_to_docx.py` (repo root) for complete implementation details

---

## 13.2 PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
projects/components/hive/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd projects/components/hive/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the hive_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## 14. References

### 14.1 Internal Documentation

- **Complete Spec:** `docs/hive_spec/` ← **Primary technical reference**
- **Master PRD:** `/PRD.md`
- **Repository Guide:** `/CLAUDE.md`

### 14.2 Related Subsystems

- **RAPIDS:** `projects/components/dmas/rapids/` - DMA engine controlled by HIVE-C
- **Delta Network:** `projects/components/delta/` - 4×4 mesh NoC
- **AMBA:** `rtl/amba/` - Monitor infrastructure
- **Common:** `rtl/common/` - Building blocks

### 14.3 External References

- **VexRiscv:** https://github.com/SpinalHDL/VexRiscv
- **SERV:** https://github.com/olofk/serv
- **RISC-V ISA:** https://riscv.org/technical/specifications/
- **AXI4-Stream:** ARM IHI 0051A

---

**Document Version:** 0.1
**Last Updated:** 2025-10-19
**Review Cycle:** Monthly during active development
**Next Review:** 2025-11-19
**Owner:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** `/PRD.md`
- **Complete Specification:** `docs/hive_spec/hive_index.md`
- **Quick Start:** `README.md` (to be created)
- **AI Guidance:** `CLAUDE.md`
- **Tasks:** `TASKS.md` (to be created)
