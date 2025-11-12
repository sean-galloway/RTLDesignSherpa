# Projects/Components Quick Status

**Last Updated:** 2025-11-11
**Purpose:** High-level status overview of all projects in the components area

---

## Project Status Legend

- **Production Ready** - Complete RTL, comprehensive tests, fully documented, ready for integration
- **Active Development** - Functional RTL with tests, ongoing feature additions and validation
- **Specification Complete** - PRD/specification finalized, ready for or beginning implementation
- **Early Specification** - Initial architecture defined, detailed specification in progress
- **Placeholder** - Reserved for future development, minimal or no implementation

---

## Component Summary

| Project | Status | RTL Files | Test Files | Priority | Completion |
|---------|--------|-----------|------------|----------|------------|
| **converters** | Production Ready | 7 | 7 | High | 100% |
| **apb_xbar** | Production Ready | 12 | 4 | High | 100% |
| **stream** | Active Development | 22 | 15+ | High | 95% |
| **bridge** | Active Development | 20+ | 10+ | High | 95% |
| **rapids** | Active Development | 14 | 23 | High | 80% |
| **retro_legacy_blocks** | Active Development | 16 | 5 | High | 15% (2/13 blocks) |
| **delta** | Active Development | 1 | 0 | Medium | 10% |
| **hive** | Early Specification | 0 | 0 | Low | 5% |
| **bch** | Placeholder | 0 | 0 | Low | 0% |

---

## Detailed Project Status

### 1. Converters - Data Width and Protocol Conversion

**Status:** ✅ Production Ready
**Version:** 1.2
**Location:** `projects/components/converters/`

**What it does:**
- Provides bidirectional data width conversion (upsize/downsize) for AXI streams
- Converts between different protocols (AXI4-to-APB, PeakRDL-to-CMD/RSP)
- Enables seamless integration between components with different data widths or protocols

**Key Features:**
- Generic building blocks: `axi_data_upsize` and `axi_data_dnsize` modules
- Flexible width ratios (2:1, 4:1, 8:1, 16:1, etc.)
- Optional dual-buffer mode for 100% throughput (downsize path)
- Configurable sideband signal handling (WSTRB slice, RRESP broadcast)
- AXI4-to-APB bridge with address/data width adaptation
- PeakRDL register interface adapter

**Documentation:**
- `README.md` - Comprehensive overview with usage examples
- `DUAL_BUFFER_IMPLEMENTATION.md` - Deep dive on high-throughput mode
- `ANALYSIS_APB_CONVERTER.md` - Design validation vs. protocol converters

**Use Cases:**
- Connect 128-bit AXI master to 32-bit AXI slave
- Bridge AXI4 system to APB peripherals
- Adapt register interfaces to custom protocols

---

### 2. APB Crossbar (apb_xbar) - APB Interconnect

**Status:** ✅ Production Ready (all tests passing)
**Version:** 1.0
**Location:** `projects/components/apb_xbar/`

**What it does:**
- Connects M APB masters to N APB slaves with address decode and arbitration
- Provides pre-generated crossbars (1x1, 2x1, 1x4, 2x4) and Python generator for custom sizes
- Enables multi-master peripheral systems with fair arbitration

**Key Features:**
- Pre-generated modules for common configurations
- Python generator for custom MxN crossbars (up to 16x16)
- Per-slave round-robin arbitration
- Grant persistence during transactions
- Fixed 64KB address space per slave
- Thin variant for minimal overhead

**Documentation:**
- `README.md` - Quick start and usage guide
- `PRD.md` - Complete specification
- `CLAUDE.md` - Integration patterns and best practices

**Use Cases:**
- CPU + DMA to peripheral interconnect
- Multi-core processor peripheral sharing
- Hierarchical peripheral bus systems

---

### 3. STREAM - Scatter-Gather Transfer Rapid Engine for AXI Memory

**Status:** 🟢 Active Development (95% complete)
**Version:** 1.0
**Location:** `projects/components/stream/`

**What it does:**
- Tutorial-focused descriptor-based DMA engine for memory-to-memory transfers
- Demonstrates streaming pipeline architecture with AXI read/write engines
- Educational reference for scatter-gather DMA design

**Key Features:**
- Descriptor-driven scatter-gather transfers
- Separate AXI read and write engines (NO FSM - streaming pipelines)
- SRAM buffering with flow control
- Performance profiler for bandwidth monitoring
- Bubble-free write engine pipeline
- Transaction completion tracking

**Core Blocks Complete:**
- ✅ descriptor_engine.sv
- ✅ scheduler.sv
- ✅ axi_read_engine.sv (with pipelining)
- ✅ axi_write_engine.sv (bubble-free pipeline)
- ✅ sram_controller.sv
- ✅ stream_alloc_ctrl.sv
- ✅ stream_drain_ctrl.sv
- ✅ stream_latency_bridge.sv
- ✅ perf_profiler.sv
- ✅ stream_core.sv (complete integration)

**Remaining (5%):**
- APB configuration interface (PeakRDL generation)
- Top-level stream_top wrapper
- Final integration test

**Documentation:**
- `PRD.md` - Product requirements and architecture
- `CLAUDE.md` - Implementation guidance
- `README.md` - Quick start guide
- `docs/stream_spec/` - Complete microarchitecture specification

**Use Cases:**
- Memory-to-memory DMA transfers
- Scatter-gather I/O operations
- Educational DMA engine reference

---

### 4. Bridge - AXI4 Full Crossbar Generator

**Status:** 🟢 Active Development (95% complete)
**Version:** 1.0
**Location:** `projects/components/bridge/`

**What it does:**
- Python-based generator for parameterized AXI4 full crossbars
- Connects multiple AXI4 masters to multiple AXI4 slaves with complete 5-channel routing
- Enables high-performance memory-mapped interconnects

**Key Features:**
- Python code generation for custom MxN topologies
- Complete AXI4 implementation (AW, W, B, AR, R channels)
- ID-based response routing with distributed RAM tracking
- Per-slave round-robin arbitration with burst-aware grant locking
- CSV-based configuration for easy customization
- Automatic RTL and testbench generation

**Current Status:**
- ✅ Python generator infrastructure complete
- ✅ RTL generation for all channel types
- ✅ Adapter modules (APB, AXIL to native AXI4)
- ✅ Crossbar routing logic
- ✅ Test infrastructure and auto-generation
- 🔧 Final integration and validation

**Documentation:**
- `PRD.md` - Complete specification
- `CLAUDE.md` - Implementation guidance and testbench architecture
- `docs/bridge_spec/` - Detailed architecture documentation

**Use Cases:**
- Multi-core processor interconnects
- Accelerator to memory fabric
- High-performance SoC interconnect

---

### 5. RAPIDS - Rapid AXI Programmable In-band Descriptor System

**Status:** 🟡 Active Development (~80% test coverage)
**Version:** 1.0
**Location:** `projects/components/rapids/`

**What it does:**
- Custom DMA-style accelerator with network interfaces for descriptor injection
- Demonstrates inband descriptor delivery via AXI-Stream packets
- Production-grade accelerator with scheduler and dual data paths

**Key Features:**
- Scheduler group for descriptor management and task scheduling
- Sink data path (network → memory via AXI write)
- Source data path (memory → network via AXI read)
- Inband descriptor delivery via CDA packets (from HIVE control plane)
- Credit-based flow control
- MonBus integration for performance monitoring

**Documentation:**
- `PRD.md` - Complete product requirements
- `CLAUDE.md` - Implementation guidance and known issues
- `docs/rapids_spec/` - Detailed specification

**Use Cases:**
- Network-attached accelerators
- DMA with inband control
- Distributed computing data movers

**Current Focus:**
- Scheduler credit counter bug fixes
- Comprehensive test coverage
- Integration with HIVE control plane

---

### 6. Retro Legacy Blocks - Intel ILB-Compatible Peripherals

**Status:** 🟡 Active Development (2/13 blocks complete)
**Version:** 1.0
**Location:** `projects/components/retro_legacy_blocks/`

**What it does:**
- Collection of Intel Low-power Block (ILB) compatible legacy peripherals
- Production-quality implementations of time-tested peripheral designs
- Modular blocks for embedded systems and FPGA-based platform emulation

**Completed Blocks (2/13):**
- ✅ **HPET** (High Precision Event Timer) - Production Ready (0x4000_0000-0x0FFF)
  * 5/6 configurations passing 100%
  * 64-bit counter, multiple comparators, periodic/one-shot modes
  * Complete documentation and test coverage

- ✅ **8254 PIT** (Programmable Interval Timer) - Complete (0x4000_2000-0x2FFF)
  * 3 independent 16-bit counters
  * 6 counting modes (terminal count, one-shot, rate generator, square wave, etc.)
  * BCD and binary counting modes
  * RTL complete, testing in progress

**Planned Blocks (11 remaining):**
- **8259 PIC** - Programmable Interrupt Controller (0x4000_1000-0x1FFF) - High Priority
- **RTC** - Real-Time Clock (0x4000_3000-0x3FFF)
- **SMBus** - System Management Bus Controller (0x4000_4000-0x4FFF)
- **PM/ACPI** - Power Management Controller (0x4000_5000-0x5FFF)
- **IOAPIC** - I/O Advanced PIC (0x4000_6000-0x6FFF)
- GPIO, UART, SPI, I2C, Watchdog, Interconnect (future)

**RLB Wrapper Goal:**
- Single APB slave entry point at 0x4000_0000
- 4KB window decode routing to individual blocks
- Drop-in replacement for legacy Intel ILB

**Documentation:**
- `PRD.md` - Complete requirements for all blocks
- `CLAUDE.md` - AI development guidance
- `BLOCK_STATUS.md` - Master tracking for all 13 blocks
- `docs/hpet_spec/` - Complete HPET specification

**Use Cases:**
- Legacy platform compatibility
- FPGA-based system emulation
- Educational peripheral design
- Embedded systems requiring ILB peripherals

---

### 7. Delta - AXI-Stream Crossbar Generator / Network-on-Chip

**Status:** 🟡 Active Development (v0.3 - Early PoC)
**Version:** 1.0
**Location:** `projects/components/delta/`

**What it does:**
- **Delta Network:** 4x4 mesh Network-on-Chip with intelligent packet routing
- **Delta AXIS Crossbar:** Python-based generator for AXI-Stream crossbars (older project)

**Key Features (Delta Network - NEW):**
- 4x4 mesh topology with 5-port routers (N/S/E/W/Local)
- XY dimension-ordered routing (deadlock-free)
- Virtual channels for QoS
- Four packet types (DATA, DESC, CONFIG, STATUS)
- Virtual tiles for external entities (RAPIDS=16, HIVE-C=17)
- Integration with RAPIDS DMA and HIVE control plane

**Documentation:**
- `README.md` - Quick start (AXIS crossbar)
- `PRD.md` - Requirements (AXIS crossbar)
- `docs/delta_spec/` - Complete NoC specification (Delta Network)

**Use Cases:**
- Network-on-Chip for multi-tile systems
- Distributed computing interconnect
- Educational NoC reference

---

### 8. HIVE - Hierarchical Intelligent Vector Environment

**Status:** 🟡 Early Specification Phase
**Version:** 0.1
**Location:** `projects/components/hive/`

**What it does:**
- Distributed control and monitoring subsystem for RAPIDS/Delta Network
- Demonstrates hierarchical RISC-V processor architecture (1 master + 16 monitors)
- Enables dynamic network reconfiguration and distributed monitoring

**Key Features:**
- HIVE-C master controller (VexRiscv RV32IM core)
- 16 SERV monitors (SERV RV32I bit-serial cores, one per tile)
- Control network (star topology for HIVE-C ↔ SERV communication)
- Configuration manager (4 virtual routing contexts with atomic switching)
- Inband descriptor delivery to RAPIDS via CDA packets
- Per-tile traffic monitoring and congestion detection

**Documentation:**
- `PRD.md` - Product requirements overview
- `CLAUDE.md` - Architecture guidance
- `docs/hive_spec/` - Detailed specification

**Use Cases:**
- Distributed control system architecture
- Network reconfiguration coordination
- Performance monitoring aggregation
- Educational RISC-V integration reference

---

### 9. BCH - Error Correction Codes

**Status:** 📋 Placeholder - Structure Created
**Version:** 0.1
**Location:** `projects/components/bch/`

**What it does:**
- Configurable BCH (Bose-Chaudhuri-Hocquenghem) encoder and decoder
- Production-quality error correction for storage and communications
- Suitable for NAND flash, SSDs, optical storage, wireless communications

**Planned Features:**
- Configurable BCH(n, k, t) parameters
- Systematic encoder (LFSR-based, low latency)
- Hard-decision decoder (syndrome, Berlekamp-Massey, Chien search)
- AXI4-Stream and simple handshake interfaces
- Support for common configurations: BCH(511,493,2), BCH(1023,1013,2), etc.

**Documentation:**
- `README.md` - Overview and BCH fundamentals
- `PRD.md` - Complete product requirements
- `CLAUDE.md` - AI development guidance
- `TASKS.md` - Development task tracking

**Use Cases:**
- NAND flash memory error correction
- Solid-state drives (SSDs)
- Optical storage (CD, DVD, Blu-ray)
- Wireless communications

---

## Project Relationships

### Integration Hierarchy

```
HIVE (Control Plane)
  ├─ Controls: RAPIDS DMA (via CDA descriptors)
  ├─ Monitors: Delta Network (16 SERV monitors)
  └─ Reconfigures: Delta routing modes

Delta Network (Data Plane)
  ├─ Routes: RAPIDS DMA traffic (Virtual Tile 16)
  ├─ Routes: HIVE-C commands (Virtual Tile 17)
  └─ Connects: 16 compute tiles

RAPIDS (Accelerator)
  ├─ Uses: Delta Network (inband descriptors)
  ├─ Controlled by: HIVE-C (descriptor injection)
  └─ Example: Accelerator with network interface

STREAM (Tutorial DMA)
  ├─ Simpler cousin of RAPIDS
  ├─ Educational reference
  └─ Standalone usage

Converters (Infrastructure)
  ├─ Used by: All projects requiring width/protocol adaptation
  └─ Example: RAPIDS may use for AXI width conversion

APB Crossbar (Peripheral Interconnect)
  ├─ Used by: Any project with APB peripherals
  └─ Example: Retro blocks connect via APB crossbar

Retro Legacy Blocks (Peripherals)
  ├─ HPET, 8254 PIT, 8259 PIC, etc.
  ├─ Unified RLB wrapper with single APB interface
  └─ Can be controlled by any APB master

Bridge (Memory Interconnect)
  ├─ Used by: Multi-master systems
  └─ Example: Connect RAPIDS + CPU to memory
```

---

## Development Priority

**Tier 1 (Production Ready):**
- ✅ converters - Production infrastructure
- ✅ apb_xbar - Production interconnect

**Tier 2 (Active Development - Nearing Completion):**
- 🟢 stream - Tutorial DMA (95% complete) - APB config + wrapper remaining
- 🟢 bridge - Crossbar generator (95% complete) - Final integration remaining

**Tier 3 (Active Development):**
- 🟡 rapids - Production accelerator (80% complete)
- 🟡 retro_legacy_blocks - ILB peripherals (15% complete - HPET + 8254 done, 11 blocks remaining)

**Tier 4 (Early Implementation):**
- 🟡 delta - NoC infrastructure (10% complete)

**Tier 5 (Early Specification):**
- 🟡 hive - Control plane (5% complete)

**Tier 6 (Future Projects):**
- 📋 bch - Error correction codes (0% - structure created, awaiting development)

---

## Resource Requirements (NexysA7 100T Target)

| Project | LUTs | BRAMs | DSPs | Notes |
|---------|------|-------|------|-------|
| **converters** | ~200 | 0 | 0 | Per converter instance |
| **apb_xbar** | ~100/slave | 0 | 0 | 2x4 crossbar ~400 LUTs |
| **stream** | ~3000 | 8 | 0 | Full DMA engine |
| **bridge** | ~500/slave | TBD | 0 | Estimate for full crossbar |
| **rapids** | ~5000 | 16 | 0 | Full accelerator |
| **retro_legacy_blocks** | ~1500 | 0 | 0 | HPET + 8254 PIT currently, 11 more blocks planned |
| **delta** | ~15000 | TBD | 0 | 4x4 mesh estimate |
| **hive** | ~9000 | 24 | 0 | HIVE-C + 16 SERV monitors |
| **bch** | ~35K | 2-4 | 0 | Encoder + Decoder estimates |

---

## Quick Commands

```bash
# View project status
cat projects/components/PROJECT_QUICK_STATUS.md

# Check individual project details
cat projects/components/{project}/PRD.md
cat projects/components/{project}/CLAUDE.md
cat projects/components/{project}/README.md

# Run project tests
cd projects/components/{project}/dv/tests
pytest test_*.py -v

# Lint project RTL
cd projects/components/{project}/rtl
make lint-all

# View component master Makefile
cat projects/components/Makefile
```

---

## Contact and Contributions

**Repository:** https://github.com/sean-galloway/RTLDesignSherpa
**Maintainer:** RTL Design Sherpa Project
**License:** MIT

For detailed technical information on each project, see the individual `PRD.md` and `CLAUDE.md` files in each project directory.

---

**Version:** 2.0
**Last Updated:** 2025-11-11
**Maintained By:** RTL Design Sherpa Project
