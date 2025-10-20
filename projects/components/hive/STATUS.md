# HIVE Component Status

**Component:** HIVE (Hierarchical Intelligent Vector Environment)
**Version:** 0.1
**Last Updated:** 2025-10-19
**Overall Status:** 🟢 New Component - Specification Phase

---

## Executive Summary

HIVE is a distributed control and monitoring subsystem featuring hierarchical RISC-V architecture (VexRiscv master + 16 SERV monitors) for coordinating RAPIDS DMA and Delta Network. Currently in specification phase with Chapter 1 complete and Chapter 2 in progress.

---

## Component Status Breakdown

### Specification Status

| Chapter | Status | Notes |
|---------|--------|-------|
| **Ch1: Overview** | ✅ Complete | Architecture, requirements, clocks/reset, acronyms, references |
| **Ch2: Blocks** | ⏳ In Progress | Overview complete, detailed blocks pending |
| **Ch3: Interfaces** | 📝 Planned | HIVE-C, SERV, external entities |
| **Ch4: Programming** | 📝 Planned | Control sequences, configuration |
| **Ch5: Performance** | 📝 Planned | Latency analysis, monitoring overhead |

### RTL Implementation Status

| Block | Status | Notes |
|-------|--------|-------|
| **Block 1: HIVE-C Controller** | 📝 Planned | VexRiscv wrapper, descriptor generation |
| **Block 2: SERV Monitors (16×)** | 📝 Planned | SERV wrapper, traffic counters |
| **Block 3: Control Network** | 📝 Planned | Star topology, round-robin arbiter |
| **Block 4: Configuration Manager** | 📝 Planned | Context storage, atomic switching |

### Documentation Status

| Document | Status | Notes |
|----------|--------|-------|
| **Specification** | ⏳ Active | hive_spec/ Ch1 complete, Ch2 in progress |
| **PRD** | ✅ Complete | Requirements documented |
| **CLAUDE Guide** | ✅ Complete | AI assistance guide |

---

## Current Work

### Active Tasks
1. **Complete Ch2: Block Specifications** - Detailed block descriptions
2. **Create Ch3: Interfaces** - HIVE-C, SERV, external entity specs
3. **Create Ch4: Programming Model** - Configuration sequences
4. **Create Ch5: Performance** - Analysis and targets

### Recently Completed
- ✅ **Chapter 1 Complete** (2025-10-19) - Overview, requirements, clocks/reset, acronyms, references
- ✅ **Chapter 2 Overview** (2025-10-19) - Block organization and resource budget
- ✅ **PRD and CLAUDE Guide** (2025-10-19) - Documentation framework
- ✅ **Documentation Generation** (2025-10-19) - md_to_docx.py tool documented

---

## Design Highlights

### Hierarchical RISC-V Architecture
- **HIVE-C Master:** VexRiscv RV32IM, 5-stage pipeline, 32KB I-mem + D-mem
- **SERV Monitors (16×):** RV32I bit-serial, 2KB I-mem + D-mem each
- **Total:** 17 RISC-V cores in hierarchical arrangement

### Resource Budget (NexysA7 100T)
- **HIVE Total:** 14,100 LUTs (22%), 11,524 FFs, 62 BRAM (46%)
- **Available for Compute:** 49,300 LUTs (78%), 240 DSPs (100%), 73 BRAM (54%)
- **Zero DSP Usage:** All DSP resources available for compute

### Control Architecture
- **Star Topology:** HIVE-C master, 16 SERV slaves
- **Round-Robin Arbitration:** Fair SERV → HIVE-C status reporting
- **Atomic Context Switching:** <25 cycles for network reconfiguration

---

## Metrics

### Target Specifications
- **HIVE-C Frequency:** 100-150 MHz
- **SERV Frequency:** 50-100 MHz
- **Delta Network Frequency:** 100 MHz
- **Descriptor Injection Latency:** <30 cycles
- **Context Switch Latency:** <25 cycles

### Monitoring Capabilities
- **Per-Tile Counters:** 32-bit packet counts (RX/TX per direction)
- **Real-Time Metrics:** 8-bit buffer occupancy per direction
- **Congestion Detection:** <10 cycles latency
- **Periodic Reporting:** Configurable interval (default 1000 cycles)

---

## Next Milestones

### Q4 2025
- [ ] Complete Ch2: Block Specifications (4 detailed block specs)
- [ ] Create Ch3: Interfaces (HIVE-C, SERV, external entities)
- [ ] Create Ch4: Programming Model
- [ ] Create Ch5: Performance Analysis

### Q1 2026
- [ ] HIVE-C RTL implementation (VexRiscv wrapper)
- [ ] SERV monitor RTL implementation (SERV wrapper + counters)
- [ ] Control network implementation
- [ ] Configuration manager implementation

### Q2 2026
- [ ] HIVE-C firmware development
- [ ] SERV firmware development
- [ ] Integration with RAPIDS and Delta
- [ ] FPGA deployment and testing

---

## Dependencies

### Upstream Dependencies
- **VexRiscv Core** - Master controller (external project, stable)
- **SERV Core** - Monitor cores (external project, stable)
- **AMBA Framework** - AXIS interface components (stable)
- **Common RTL** - Arbiters, counters (stable)

### Downstream Dependents
- **RAPIDS** - Controlled via CDA packet injection
- **Delta Network** - Monitored and reconfigured by HIVE
- **Compute Tiles** - Monitored by SERV instances

---

## Integration Points

- **RAPIDS Integration:** CDA packet injection via Virtual Tile 17
- **Delta Network Integration:** Virtual Tile 17 connection, PKT_CONFIG broadcast
- **SERV Monitor Integration:** Co-located with physical tiles 0-15
- **Host Interface:** UART/AXI4-Lite for command input

---

## Quick Links

- **Specification:** [docs/hive_spec/hive_index.md](docs/hive_spec/hive_index.md)
- **PRD:** [PRD.md](PRD.md)
- **CLAUDE Guide:** [CLAUDE.md](CLAUDE.md)
- **Tasks:** [TASKS.md](TASKS.md)

---

**Status Legend:**
- ✅ Complete
- ⏳ In Progress
- ⏸️ Blocked
- ❌ Failed/Deprecated
- 📝 Planned
