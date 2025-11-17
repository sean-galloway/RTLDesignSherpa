# RTL Design Sherpa - Components Directory

**Version:** 1.1
**Last Updated:** 2025-10-24
**Purpose:** Overview of demonstration components and design examples

---

## Overview

The `projects/components/` directory contains demonstration components showcasing industry-standard RTL design practices and verification methodologies. Each component serves as both a functional building block and an educational reference for FPGA/ASIC design.

**Design Philosophy:**
- **Specification First:** Complete PRD before implementation
- **Performance Modeling:** Analytical models validate requirements
- **Comprehensive Verification:** CocoTB testbenches with multi-level coverage
- **Documentation:** Inline comments + standalone specifications
- **Reusability:** Technology-agnostic, synthesizable SystemVerilog

---

## Components Summary

| Component | Type | Status | Purpose | Complexity |
|-----------|------|--------|---------|------------|
| **[apb_xbar](#apb_xbar)** | Generator | ✅ Complete | APB crossbar interconnect | Medium |
| **[bch](#bch)** | Error Correction | 📋 Planned | BCH encoder/decoder for storage | High |
| **[bridge](#bridge)** | Generator | 🟢 95% Complete | AXI4 full crossbar generator | High |
| **[converters](#converters)** | Converters | ✅ Complete | AXI4 data width converters | Medium |
| **[delta](#delta)** | Generator | 🔧 In Progress | AXI-Stream crossbar generator | Medium |
| **[hive](#hive)** | Control Plane | 🟡 Early Spec | Distributed control subsystem | Very High |
| **[misc](#misc)** | Utilities | ✅ Active | Reusable utility components (ROM/RAM wrappers) | Low-Medium |
| **[rapids](#rapids)** | Accelerator | 🔧 In Progress | DMA with network integration | Very High |
| **[retro_legacy_blocks](#retro_legacy_blocks)** | Peripherals | 🟢 Active Dev | Intel ILB-compatible legacy peripherals | Medium |
| **[shims](#shims)** | Adapter | ✅ Complete | Protocol conversion adapters | Low-Medium |
| **[stream](#stream)** | DMA Engine | 🟢 95% Complete | Tutorial-focused scatter-gather DMA | Medium-High |

---

## Component Details

### apb_xbar

**APB Crossbar Generator**

**Status:** ✅ Complete (all configurations passing)

**Description:**
Python-based code generator producing parameterized APB crossbar RTL for connecting multiple APB masters to multiple slaves. Pre-generated variants available for common configurations (1×1, 2×1, 1×4, 2×4).

**Key Features:**
- Python code generation for custom M×N configurations
- Pre-generated modules for common sizes (1×1, 2×1, 1×4, 2×4, thin variant)
- Round-robin arbitration per slave with grant locking
- Fixed 64KB address regions per slave
- Configurable base address parameter
- Comprehensive test coverage (100% passing)

**Available Pre-Generated Modules:**
- `apb_xbar_1to1.sv` - Passthrough/protocol conversion
- `apb_xbar_2to1.sv` - Multi-master arbitration
- `apb_xbar_1to4.sv` - Address decode for peripherals
- `apb_xbar_2to4.sv` - Full crossbar (CPU + DMA)
- `apb_xbar_thin.sv` - Minimal overhead variant

**Address Map:**
- Slave 0: BASE_ADDR + 0x0000_0000 (64KB)
- Slave 1: BASE_ADDR + 0x0001_0000 (64KB)
- Slave N: BASE_ADDR + N × 0x10000

**Applications:**
- SoC peripheral interconnects
- Multi-master APB fabrics
- CPU + DMA peripheral access
- Address decode and arbitration

**Resources:**
- RTL: `rtl/apb_xbar_*.sv` (pre-generated)
- Generator: `bin/generate_xbars.py`
- Tests: `dv/tests/test_apb_xbar_*.py`
- Documentation: `PRD.md`, `CLAUDE.md`

**Generation Example:**
```bash
cd apb_xbar/bin/
python generate_xbars.py --masters 3 --slaves 6 --output ../rtl/apb_xbar_3to6.sv
```

**📖 See:** [`apb_xbar/PRD.md`](apb_xbar/PRD.md) for complete specification

---

### bridge

**AXI4 Full Crossbar Generator**

**Status:** 🟢 95% Complete - Final Integration Pending

**Description:**
Python-based code generator producing parameterized AXI4 full crossbar RTL for connecting multiple masters to multiple slaves. Supports out-of-order transactions, burst optimization, and ID-based routing.

**Key Features:**
- Python code generation (similar to APB crossbar automation)
- Full AXI4 protocol support (5 channels: AW, W, B, AR, R)
- Out-of-order transaction support via ID-based routing
- Configurable address maps with range checking
- Performance modeling (analytical + simulation)
- Flat topology (full M×N interconnect)

**Target Performance:**
- Latency: ≤3 cycles for single-beat transactions
- Throughput: Concurrent transfers on all M×S paths
- Fmax: ≥300 MHz on Xilinx UltraScale+

**Use Cases:**
- Multi-core processor interconnects
- DMA + accelerator systems
- High-performance memory-mapped fabrics

**Resources:**
- Generator: `bin/bridge_generator.py` (planned)
- Performance Model: `bin/bridge_performance_model.py` (planned)
- Documentation: `PRD.md`

**📖 See:** [`bridge/PRD.md`](bridge/PRD.md) for complete specification

---

### converters

**AXI4 Data Width Converters**

**Status:** ✅ Complete (all tests passing)

**Description:**
AXI4 data width up/down conversion modules for interfacing components with different data bus widths. Supports read and write path conversion with proper handling of strobes, bursts, and alignment.

**Key Features:**
- Read data width converter (narrow master → wide slave)
- Write data width converter (wide master → narrow slave)
- Automatic burst decomposition/composition
- Strobe (WSTRB) alignment handling
- Full AXI4 protocol compliance
- Parameterized data widths (must be power-of-2 multiples)

**Supported Conversions:**
- 32-bit ↔ 64-bit
- 32-bit ↔ 128-bit
- 64-bit ↔ 256-bit
- Any power-of-2 ratio

**Use Cases:**
- Connecting 32-bit CPU to 64-bit memory controller
- Interfacing 128-bit accelerator to 32-bit peripheral bus
- Width adaptation in multi-width SoC fabrics
- Performance optimization (wider memory interfaces)

**Resources:**
- RTL: `rtl/axi4_dwidth_converter_rd.sv`, `rtl/axi4_dwidth_converter_wr.sv`
- Tests: `dv/tests/test_axi4_dwidth_converter_rd.py`, `test_axi4_dwidth_converter_wr.py`
- Documentation: Design comments in RTL

**📖 See:** Component tests for usage examples

---

### delta

**AXI-Stream Crossbar Generator**

**Status:** 🔧 In Progress

**Description:**
Python-based AXI-Stream crossbar generator supporting both flat (low-latency) and tree (modular) topologies. Demonstrates code generation techniques and topology trade-off analysis.

**Key Features:**
- Dual topology support: Flat crossbar and hierarchical tree
- Python RTL generation (95% code reuse from APB patterns)
- Performance modeling (analytical + SimPy simulation)
- Complete AXI-Stream protocol compliance
- TDEST-based routing with round-robin arbitration

**Topologies:**

**Flat Crossbar:**
- Latency: 2 cycles
- Throughput: High aggregate
- Resources: ~1,920 LUTs (4×16 @ 64-bit)
- Best for: Production systems

**Tree Topology:**
- Latency: 4-6 cycles (multi-stage)
- Throughput: Lower aggregate
- Resources: ~1,600 LUTs (4×16 @ 64-bit)
- Best for: Educational demonstrations

**Use Cases:**
- RISC cores routing to DSP arrays
- Streaming data fabric
- Educational topology comparisons

**Resources:**
- Generator: `bin/delta_generator.py` (planned)
- Performance Model: `bin/delta_performance_model.py` (planned)
- Documentation: `PRD.md`

**📖 See:** [`delta/PRD.md`](delta/PRD.md) for complete specification

---

### rapids

**Rapid AXI Programmable In-band Descriptor System**

**Status:** 🔧 In Progress - Validation Phase

**Description:**
Complex hardware accelerator demonstrating descriptor-based DMA operations with network interface integration. Features sophisticated FSM coordination, credit-based flow control with exponential encoding, and comprehensive monitoring.

**Key Features:**
- Descriptor-based operation with FIFO queuing
- Dual data paths: Sink (Network→Memory) and Source (Memory→Network)
- Credit-based flow control with exponential encoding (0→1, 1→2, 2→4, ..., 15→∞)
- SRAM buffering to decouple network from memory
- AXI4 burst support for efficient transfers
- MonBus integration for monitoring

**Architecture:**
- **Scheduler Group:** Task FSM, descriptor parsing, program sequencing
- **Sink Path:** Network Slave → SRAM → AXI4 Write Engine
- **Source Path:** AXI4 Read Engine → SRAM → Network Master
- **Monitoring:** MonBus reporter for events and performance

**Test Coverage:** ~85% functional (basic scenarios validated, descriptor engine 100%)

**Resources:**
- RTL: `rtl/rapids_fub/*.sv`, `rtl/rapids_macro/*.sv`
- Tests: `dv/tests/fub_tests/`, `dv/tests/integration_tests/`
- Documentation: `PRD.md`, `CLAUDE.md`, `docs/rapids_spec/` (complete specification)

**📖 See:**
- [`rapids/PRD.md`](rapids/PRD.md) - Requirements overview
- [`rapids/docs/rapids_spec/miop_index.md`](rapids/docs/rapids_spec/miop_index.md) - Complete specification

---

### shims

**Protocol Conversion and Glue Logic Adapters**

**Status:** ✅ Complete (all tests passing)

**Description:**
Collection of protocol conversion adapters and glue logic modules for interfacing between different register file standards and custom protocols.

**Key Components:**

**PeakRDL-to-CmdRsp Adapter:**
- Converts PeakRDL-generated APB register interfaces to custom CmdRsp protocol
- Simplifies register integration in custom accelerators
- Maintains timing and protocol semantics
- Fully tested and validated

**Key Features:**
- Protocol adaptation (APB ↔ CmdRsp)
- Minimal latency overhead
- Full address and data width support
- Error response mapping
- Ready for production use

**Use Cases:**
- Integrating PeakRDL registers with custom engines
- APB-to-custom protocol bridges
- Glue logic for heterogeneous systems
- Register file adaptation

**Resources:**
- RTL: `rtl/peakrdl_to_cmdrsp.sv`
- Tests: `dv/tests/test_peakrdl_to_cmdrsp.py`
- Documentation: Inline RTL comments

**📖 See:** Component tests for usage examples

---

### stream

**STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory**

**Status:** 🟢 95% Complete - APB Config and Top-Level Wrapper Pending

**Description:**
Simplified DMA engine designed as a beginner-friendly tutorial demonstrating descriptor-based scatter-gather patterns. Intentionally simplified from RAPIDS for educational purposes.

**Key Features:**
- 8 independent channels with shared resources
- APB configuration with simple kick-off mechanism
- Descriptor-based scatter-gather with chaining support
- Separate read/write AXI engines (multiple versions planned)
- Aligned addresses only (tutorial simplification)
- Length specified in beats (not bytes/chunks)

**Simplifications from RAPIDS:**
- ✅ Aligned addresses only (no fixup logic)
- ✅ Length in beats (simplified math)
- ✅ No circular buffers (explicit termination)
- ✅ No credit management (simple limits)
- ✅ Pure memory-to-memory (no network interfaces)

**Architecture:**
- **APB Config:** 8-channel register interface
- **Scheduler:** Simplified FSM coordination
- **Descriptor Engine:** From RAPIDS (reused)
- **Data Path:** AXI read/write engines + SRAM buffer
- **MonBus:** Standard monitoring integration

**Learning Path:**
1. **STREAM** - Basic DMA with aligned addresses
2. **STREAM Extended** - Add alignment fixup
3. **RAPIDS** - Full complexity with network + credits

**Resources:**
- RTL: `rtl/fub/*.sv` (complete), `rtl/macro/*.sv` (complete)
- Tests: `dv/tests/fub/` (passing), `dv/tests/macro/` (passing)
- Documentation: `PRD.md`, `CLAUDE.md`, `docs/stream_spec/` (complete microarchitecture)
- Performance Model: `bin/dma_model/` (comprehensive analytical + SimPy models)

**📖 See:** [`stream/PRD.md`](stream/PRD.md) for complete specification

---

### retro_legacy_blocks

**Retro Legacy Blocks - Intel ILB-Compatible Peripherals**

**Status:** 🟢 Active Development (2/13 blocks complete)

**Description:**
Collection of Intel Low-power Block (ILB) compatible legacy peripherals. Production-quality implementations of time-tested peripheral designs packaged as a unified subsystem with single APB entry point. Goal is drop-in replacement for legacy Intel ILB with modern RTL practices.

**Architecture:**
Unified RLB Wrapper provides single APB slave interface at `0x4000_0000` with 4KB window decode routing to individual peripheral blocks. Each block occupies 4KB address space for clean power-of-2 decoding.

**Completed Blocks (2/13):**

| Block | Status | Address Range | Description |
|-------|--------|---------------|-------------|
| **HPET** | ✅ Production | 0x4000_0000-0x0FFF | High Precision Event Timer with 64-bit counter |
| **8254 PIT** | ✅ Complete | 0x4000_2000-0x2FFF | Programmable Interval Timer (3× 16-bit counters) |

**HPET Features:**
- Configurable timer count: 2, 3, or 8 independent timers
- 64-bit main counter with 64-bit comparators
- One-shot and periodic operating modes
- Optional clock domain crossing support
- PeakRDL-generated APB register interface
- 5/6 configurations passing 100% tests

**8254 PIT Features:**
- 3 independent 16-bit counters
- 6 counting modes: terminal count, one-shot, rate generator, square wave, strobe, retriggerable
- BCD and binary counting modes
- Standard Intel 8254 register-compatible interface
- RTL complete with comprehensive test coverage

**Planned Blocks (11 remaining):**

| Priority | Block | Address Range | Description |
|----------|-------|---------------|-------------|
| High | **8259 PIC** | 0x4000_1000-0x1FFF | Programmable Interrupt Controller |
| Medium | **RTC** | 0x4000_3000-0x3FFF | Real-Time Clock with CMOS RAM |
| Medium | **SMBus** | 0x4000_4000-0x4FFF | System Management Bus Controller |
| Medium | **PM/ACPI** | 0x4000_5000-0x5FFF | Power Management Controller |
| Medium | **IOAPIC** | 0x4000_6000-0x6FFF | I/O Advanced Programmable Interrupt Controller |
| Medium | GPIO | TBD | General Purpose I/O |
| Medium | UART | TBD | Universal Asynchronous Receiver/Transmitter |
| Low | SPI | TBD | Serial Peripheral Interface |
| Low | I2C | TBD | Inter-Integrated Circuit |
| Low | Watchdog | TBD | System Watchdog Timer |
| Low | **Interconnect** | 0x4000_F000-0xFFFF | ID/Version Registers |

**RLB Wrapper Goal:**
Single APB slave at `0x4000_0000` with internal 4KB window decode routing to all blocks. Drop-in compatible with legacy Intel ILB implementations but using modern synthesizable RTL.

**Applications:**
- Legacy platform compatibility
- FPGA-based system emulation
- Embedded systems requiring ILB peripherals
- Educational peripheral design reference
- PC architecture compatibility layers

**Resources:**
- RTL: `rtl/hpet/`, `rtl/pit_8254/` (completed), `rtl/{block}/` (planned)
- Tests: `dv/tests/hpet/`, `dv/tests/pit_8254/` (completed), `dv/tests/{block}/` (planned)
- Documentation: `PRD.md`, `CLAUDE.md`, `docs/hpet_spec/` (complete)
- Status Tracking: `BLOCK_STATUS.md` - Master tracking for all 13 blocks

**📖 See:**
- [`retro_legacy_blocks/PRD.md`](retro_legacy_blocks/PRD.md) - Complete requirements for all blocks
- [`retro_legacy_blocks/BLOCK_STATUS.md`](retro_legacy_blocks/BLOCK_STATUS.md) - Development status tracking
- [`retro_legacy_blocks/docs/hpet_spec/hpet_index.md`](retro_legacy_blocks/docs/hpet_spec/hpet_index.md) - HPET complete specification

---

### bch

**BCH Error Correction Codes**

**Status:** 📋 Placeholder - Structure Created

**Description:**
Configurable BCH (Bose-Chaudhuri-Hocquenghem) encoder and decoder for error correction in storage and communication systems. Production-quality implementation suitable for NAND flash, SSDs, optical storage, and wireless communications.

**Planned Features:**
- Configurable BCH(n, k, t) parameters
- Systematic encoder (LFSR-based, low latency)
- Hard-decision decoder (syndrome, Berlekamp-Massey, Chien search)
- AXI4-Stream and simple handshake interfaces
- Support for common configurations: BCH(511,493,2), BCH(1023,1013,2), etc.

**Applications:**
- NAND flash memory error correction
- Solid-state drives (SSDs)
- Optical storage (CD, DVD, Blu-ray)
- Wireless communications
- Data integrity in high-reliability systems

**Resources:**
- Documentation: `README.md`, `PRD.md`, `CLAUDE.md`, `TASKS.md`
- Future: `rtl/`, `dv/tests/`, `docs/bch_spec/`

**📖 See:** [`bch/PRD.md`](bch/PRD.md) for complete requirements (when ready)

---

### hive

**HIVE - Hierarchical Intelligent Vector Environment**

**Status:** 🟡 Early Specification Phase

**Description:**
Distributed control and monitoring subsystem for RAPIDS/Delta Network. Demonstrates hierarchical RISC-V processor architecture with 1 master controller (HIVE-C) and 16 lightweight monitors (SERV cores). Enables dynamic network reconfiguration and distributed monitoring.

**Planned Architecture:**
- **HIVE-C Master:** VexRiscv RV32IM core for global control
- **16× SERV Monitors:** Bit-serial RV32I cores, one per Delta Network tile
- **Control Network:** Star topology for HIVE-C ↔ SERV communication
- **Configuration Manager:** 4 virtual routing contexts with atomic switching
- **Descriptor Delivery:** Inband CDA packets to RAPIDS accelerators
- **Monitoring:** Per-tile traffic monitoring and congestion detection

**Integration with Other Components:**
- Controls RAPIDS DMA via CDA descriptor injection
- Monitors Delta Network traffic and congestion
- Reconfigures Delta routing modes dynamically
- Aggregates performance data from 16 tiles

**Applications:**
- Distributed control system architecture
- Network reconfiguration coordination
- Performance monitoring aggregation
- Educational RISC-V integration reference
- Hierarchical processor organization

**Resources:**
- Documentation: `PRD.md`, `CLAUDE.md`, `docs/hive_spec/`
- Future: `rtl/`, `dv/tests/`

**📖 See:** [`hive/PRD.md`](hive/PRD.md) for complete specification

---

### misc

**Miscellaneous Utility Components**

**Status:** ✅ Active - Collection of reusable building blocks

**Description:**
Collection of utility components and adapters that solve common integration problems. These are production-quality, single-purpose modules with standard interfaces (AXI4, APB) that don't fit into larger subsystems but are useful across multiple projects.

**Key Characteristics:**
- **Single-Purpose:** Each component solves one specific problem
- **Reusable:** Parameterized, technology-agnostic implementations
- **Standard Interfaces:** AXI4, APB, or other industry standards
- **Production Quality:** Fully tested, documented, lint-clean

**Current/Planned Components:**

| Component | Status | Description |
|-----------|--------|-------------|
| `axi_rom_wrapper` | 📋 Planned | AXI4 read-only memory (boot ROM, LUTs, config data) |
| `axi_ram_wrapper` | 📋 Future | AXI4 read/write memory |
| `apb_rom_wrapper` | 📋 Future | APB read-only memory |
| `apb_ram_wrapper` | 📋 Future | APB read/write memory |
| `axi_pattern_gen` | 📋 Future | AXI4 test pattern generator |
| `async_fifo_wrapper` | 📋 Future | Clock domain crossing FIFO |

**AXI ROM Wrapper (First Component):**
- AXI4 read-only slave interface
- Parameterizable data width (32, 64, 128, 256, 512 bits)
- Parameterizable depth
- FPGA block RAM inference
- Optional initialization from hex/mem files
- Single-cycle read latency
- Burst support (INCR, WRAP, FIXED)

**Applications:**
- Boot ROM for embedded processors
- Configuration data storage
- Lookup tables for algorithms
- Test pattern storage
- Calibration data

**Resources:**
- Documentation: `README.md`, `CLAUDE.md`
- Future: `rtl/axi_rom_wrapper.sv`, `dv/tests/test_axi_rom.py`

**📖 See:** [`misc/README.md`](misc/README.md) for complete overview and component guidelines

---

## Comparison Matrix

### Protocol and Interface Support

| Component | APB | AXI4 | AXI4-Lite | AXI-Stream | Network | MonBus | Other |
|-----------|-----|------|-----------|------------|---------|--------|-------|
| **apb_xbar** | ✅ Crossbar | - | - | - | - | - | - |
| **bch** | - | - | - | ✅ M/S | - | - | ✅ Simple HS |
| **bridge** | - | ✅ Crossbar | - | - | - | - | - |
| **converters** | - | ✅ Converter | - | - | - | - | - |
| **delta** | - | - | - | ✅ Crossbar | - | - | - |
| **hive** | - | - | - | - | ✅ Control | ✅ Master | ✅ RISC-V |
| **misc** | ✅ Slave | ✅ Slave | - | - | - | - | - |
| **rapids** | - | ✅ Master | ✅ Slave | - | ✅ M/S | ✅ Master | - |
| **retro_legacy_blocks** | ✅ Slave | - | - | - | - | - | ✅ Interrupts |
| **shims** | ✅ Adapter | - | - | - | - | - | ✅ CmdRsp |
| **stream** | ✅ Slave | ✅ Master | - | - | - | ✅ Master | - |

### Complexity and Scope

| Component | RTL Modules | Test Coverage | Primary Focus | Educational Value |
|-----------|-------------|---------------|---------------|-------------------|
| **apb_xbar** | 5 pre-gen + generator | 100% | Crossbar interconnect | High |
| **bch** | TBD | N/A | Error correction | High |
| **bridge** | Generated | TBD | Code generation | High |
| **converters** | 2 | 100% | Data width adaptation | Medium |
| **delta** | Generated | TBD | Topology comparison | High |
| **hive** | TBD | N/A | Distributed control | Very High |
| **misc** | 1-6 (planned) | TBD | Utility wrappers | Medium |
| **rapids** | 17 | ~85% | Complex accelerator | Very High |
| **retro_legacy_blocks** | 16 (2 complete) | 95-100% (HPET/PIT) | Legacy peripherals | Medium-High |
| **shims** | 1 | 100% | Protocol conversion | Low-Medium |
| **stream** | 10+ | 95%+ | Tutorial DMA | High |

### Resource Utilization (Estimates)

| Component | LUTs | FFs | BRAM | Notes |
|-----------|------|-----|------|-------|
| **apb_xbar** | ~150-600 | ~200-500 | 0 | Depends on M×N size |
| **bch** | ~35K | TBD | 2-4 | Encoder + Decoder estimates |
| **bridge** | ~2,500 | ~3,000 | 0 | 4×4 @ 512-bit |
| **converters** | ~200-400 | ~150-300 | 0 | Per converter, depends on width ratio |
| **delta** | ~1,600-1,920 | ~1,200 | 0 | 4×16 @ 64-bit |
| **hive** | ~9K | TBD | 24 | HIVE-C + 16× SERV monitors |
| **misc** | ~100-500 | ~100-300 | 1-4 | Per component, depends on depth |
| **rapids** | ~10K | ~8K | 0 | Plus SRAM (dominant) |
| **retro_legacy_blocks** | ~1,500 | ~1,000 | 0 | HPET + PIT currently, more planned |
| **shims** | ~50-100 | ~50-100 | 0 | Minimal glue logic |
| **stream** | ~5K | ~4K | 0 | Plus SRAM |

---

## Directory Structure

```
projects/components/
├── apb_xbar/                    # APB Crossbar Generator
│   ├── rtl/                     # Pre-generated RTL
│   ├── bin/                     # Python generator
│   ├── dv/tests/                # CocoTB verification
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md                # Quick start
│
├── bch/                         # BCH Error Correction (Planned)
│   ├── PRD.md, CLAUDE.md, TASKS.md
│   └── README.md
│
├── bridge/                      # AXI4 Crossbar Generator
│   ├── bin/                     # Python generator
│   ├── rtl/                     # Generated RTL
│   ├── dv/tests/                # CocoTB verification
│   ├── docs/bridge_spec/        # Specifications
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md
│
├── converters/                  # AXI4 Data Width Converters
│   ├── rtl/                     # SystemVerilog RTL
│   ├── dv/tests/                # CocoTB verification
│   └── README.md
│
├── delta/                       # AXI-Stream Crossbar Generator
│   ├── bin/                     # Python generator (planned)
│   ├── docs/delta_spec/         # Specifications
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md
│
├── hive/                        # Hierarchical Intelligent Vector Environment
│   ├── docs/hive_spec/          # Specifications
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md
│
├── misc/                        # Miscellaneous Utility Components
│   ├── bin/                     # Utility scripts (ROM init generators)
│   ├── rtl/                     # Component implementations
│   ├── dv/
│   │   ├── tbclasses/           # Testbench classes
│   │   └── tests/               # Test runners
│   ├── docs/                    # Component specifications
│   ├── README.md                # Overview and guidelines
│   └── CLAUDE.md                # AI assistance guide
│
├── rapids/                      # Rapid AXI Programmable In-band Descriptor System
│   ├── rtl/
│   │   ├── rapids_fub/          # Functional unit blocks
│   │   └── rapids_macro/        # Integration blocks
│   ├── dv/
│   │   ├── tbclasses/           # Testbench classes
│   │   └── tests/               # Unit, integration, and system tests
│   ├── docs/rapids_spec/        # Complete specification (5 chapters)
│   ├── known_issues/            # Bug tracking
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md                # Quick start
│
├── retro_legacy_blocks/         # Intel ILB-Compatible Peripherals
│   ├── rtl/
│   │   ├── hpet/                # ✅ High Precision Event Timer (Complete)
│   │   ├── pit_8254/            # ✅ Programmable Interval Timer (Complete)
│   │   ├── pic_8259/            # 📋 Programmable Interrupt Controller (Planned)
│   │   ├── rtc/                 # 📋 Real-Time Clock (Planned)
│   │   ├── smbus/               # 📋 SMBus Controller (Planned)
│   │   ├── pm_acpi/             # 📋 Power Management (Planned)
│   │   └── ioapic/              # 📋 I/O APIC (Planned)
│   ├── dv/
│   │   ├── tbclasses/           # Block-specific testbench classes
│   │   └── tests/               # Per-block test suites
│   ├── docs/
│   │   ├── hpet_spec/           # ✅ HPET complete specification
│   │   └── {block}_spec/        # 📋 Other block specs (planned)
│   ├── BLOCK_STATUS.md          # Master status tracking (13 blocks)
│   ├── PRD.md, CLAUDE.md        # Documentation
│   └── README.md                # Quick start
│
├── shims/                       # Protocol Conversion Adapters
│   ├── rtl/                     # SystemVerilog RTL
│   ├── dv/tests/                # CocoTB verification
│   └── README.md
│
└── stream/                      # Scatter-gather Transfer Rapid Engine for AXI Memory
    ├── rtl/
    │   ├── fub/                 # Functional unit blocks (complete)
    │   └── macro/               # Integration blocks (complete)
    ├── dv/
    │   ├── tbclasses/           # Testbench classes
    │   └── tests/               # FUB and macro tests
    ├── bin/dma_model/           # Performance models (analytical + SimPy)
    ├── docs/stream_spec/        # Complete microarchitecture specification
    ├── PRD.md, CLAUDE.md        # Documentation
    └── README.md                # Quick start
```

---

## Getting Started

### Prerequisites

**Tools:**
- Verilator (RTL simulation and linting)
- Python 3.8+ (for CocoTB and code generation)
- CocoTB framework (installed in repository)
- pytest (test runner)

**Optional:**
- PeakRDL (for apb_hpet register generation)
- GTKWave (waveform viewing)
- Xilinx Vivado or open-source synthesis tools

### Quick Start Examples

#### Running Component Tests with Makefiles

All component test directories now include comprehensive Makefiles with REG_LEVEL support for controlled test depth:

```bash
# Using make targets (RECOMMENDED)
cd projects/components/{component}/dv/tests/

# Quick smoke test (~5 min)
make run-all-gate-parallel

# Default functional coverage (~30 min)
make run-all-func-parallel

# Comprehensive validation (~4 hr)
make run-all-full-parallel

# View all available targets
make help
```

**REG_LEVEL Control:**
- **GATE**: Quick smoke test - Basic connectivity validation
- **FUNC**: Functional coverage (DEFAULT) - Standard test suite
- **FULL**: Comprehensive validation - Stress tests and edge cases

#### Running Retro Legacy Blocks Tests

```bash
# Using make targets (RECOMMENDED)
cd projects/components/retro_legacy_blocks/dv/tests/

# Run all HPET tests
cd hpet/
make run-all-func-parallel        # FUNC level, 48 workers
make run-hpet-gate                # Quick smoke test
make run-hpet-full                # Comprehensive test

# Run all 8254 PIT tests
cd ../pit_8254/
pytest test_apb_pit_8254.py -v

# Direct pytest invocation (from retro_legacy_blocks/dv/tests/)
pytest hpet/ -v                   # All HPET tests
pytest pit_8254/ -v               # All PIT tests

# Run specific HPET configuration
pytest "hpet/test_apb_hpet.py::test_hpet[2-32902-1-0-basic-2-timer Intel-like]" -v

# Run with waveforms
WAVES=1 pytest hpet/ -v
gtkwave hpet/logs/{test_name}.vcd
```

#### Running RAPIDS Tests

```bash
# Using make targets (RECOMMENDED)
cd projects/components/rapids/dv/tests/
make run-fub-func-parallel          # FUB tests, 48 workers
make run-macro-func-parallel        # Macro tests, 48 workers
make run-system-func-parallel       # System tests, 48 workers
make run-all-gate-parallel          # Quick smoke test

# Direct pytest invocation
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v
pytest projects/components/rapids/dv/tests/fub_tests/descriptor_engine/ -v
pytest projects/components/rapids/dv/tests/integration_tests/ -v
pytest projects/components/rapids/dv/tests/ -v
```

#### Running STREAM Performance Models

```bash
cd projects/components/stream/bin/dma_model/bin/

# Comprehensive analysis with all modes
python3 comprehensive_analysis.py --include-perfect --plots --report

# Specific mode analysis
python3 comprehensive_analysis.py --mode HIGH --report

# Generate performance plots
python3 generate_optimization_plots.py
```

---

## Component Selection Guide

### When to Use Each Component

**Retro Legacy Blocks:**
- ✅ Need Intel ILB-compatible peripherals
- ✅ Legacy platform compatibility (PC architecture)
- ✅ FPGA-based system emulation
- ✅ Educational peripheral design examples
- ✅ Production-ready timers (HPET, 8254 PIT)

**Bridge (AXI4 Crossbar):**
- ✅ Building multi-core processor interconnects
- ✅ Need memory-mapped crossbar with out-of-order support
- ✅ Learning AXI4 protocol and ID-based routing
- ✅ Require burst optimization for cache line fills

**Delta (AXI-Stream Crossbar):**
- ✅ Routing streaming data between processors
- ✅ Need low-latency crossbar for compute fabric
- ✅ Comparing topology trade-offs (flat vs tree)
- ✅ Learning code generation techniques

**RAPIDS:**
- ✅ Complex DMA with network interface integration
- ✅ Descriptor-based data movement
- ✅ Credit-based flow control needed
- ✅ Advanced FSM coordination examples
- ✅ Educational reference for complex accelerators

**STREAM:**
- ✅ Learning descriptor-based DMA design
- ✅ Tutorial-focused scatter-gather engine
- ✅ Memory-to-memory transfers (no network)
- ✅ Simplified design for teaching
- ✅ Foundation before tackling RAPIDS complexity

---

## Design Patterns Demonstrated

### Specification-Driven Design
All components follow the same workflow:
1. **PRD First:** Complete requirements before code
2. **Performance Modeling:** Analytical validation
3. **RTL Implementation:** Parameterized, synthesizable
4. **Comprehensive Testing:** Multi-level verification
5. **Documentation:** Inline + standalone specs

### Code Generation (bridge, delta)
- Python-based RTL generation
- Parameterization without manual edits
- ~95% code reuse between generators
- Performance models validate generated RTL

### Verification Methodology
- **FUB Tests:** Individual block validation
- **Integration Tests:** Block-to-block interfaces
- **System Tests:** Complete data flows
- **Stress Tests:** Corner cases and performance

### Monitoring and Debug
- MonBus standard protocol (rapids, stream)
- Performance counters
- Comprehensive event reporting
- Waveform-friendly signal naming

---

## Educational Value

### Learning Path

**Beginner:**
1. **retro_legacy_blocks (HPET/PIT)** - Simple peripherals with standard APB interface
2. **stream** - Tutorial DMA with aligned addresses
3. **apb_xbar** - Crossbar interconnect concepts
4. **delta (flat)** - AXI-Stream crossbar basics

**Intermediate:**
1. **converters** - Data width adaptation patterns
2. **delta (tree)** - Topology comparisons
3. **bridge** - AXI4 full protocol
4. **stream (extended)** - Add alignment fixup
5. **retro_legacy_blocks (8259 PIC)** - Interrupt controller complexity

**Advanced:**
1. **rapids** - Complete accelerator with FSM coordination
2. **hive** - Distributed control with RISC-V processors
3. **bch** - Error correction algorithms
4. **Custom components** - Apply learned patterns

### Key Concepts Taught

**Interfaces and Protocols:**
- APB (retro_legacy_blocks, apb_xbar, stream)
- AXI4 (bridge, rapids, stream, converters)
- AXI4-Lite (rapids)
- AXI-Stream (delta, bch)
- Custom protocols (rapids Network, shims CmdRsp)
- RISC-V (hive)

**Design Patterns:**
- Descriptor-based engines (rapids, stream)
- Credit-based flow control (rapids)
- Scatter-gather DMA (stream)
- Crossbar arbitration (bridge, delta)
- FSM coordination (rapids)

**Verification:**
- CocoTB testbench framework
- BFM (Bus Functional Model) usage
- Multi-level testing strategy
- Continuous monitoring patterns
- Queue-based verification

**Code Generation:**
- Python RTL generation (bridge, delta)
- Parameterization techniques
- Performance modeling
- Topology trade-off analysis

---

## Contributing

When adding new components or modifying existing ones:

1. **Follow Established Patterns:**
   - Create complete PRD before implementation
   - Include performance models
   - Write comprehensive tests
   - Document thoroughly

2. **Directory Structure:**
   ```
   component_name/
   ├── rtl/               # RTL source
   ├── dv/tests/          # Verification
   ├── docs/              # Specifications
   ├── PRD.md             # Requirements
   ├── CLAUDE.md          # AI guidance
   └── README.md          # Quick start
   ```

3. **Required Documentation:**
   - PRD.md with requirements and architecture
   - CLAUDE.md for AI assistance guidance
   - README.md for quick start
   - Inline RTL comments
   - Test documentation

4. **Quality Gates:**
   - Verilator lint clean
   - All tests passing (100% success rate)
   - >90% functional coverage
   - Performance validated against models

---

## References

### Internal Documentation
- `/PRD.md` - Master product requirements
- `/CLAUDE.md` - Repository-wide guidance
- `bin/CocoTBFramework/` - Reusable verification infrastructure
- `docs/` - Design guides and reports

### External Standards
- **AMBA Specifications:** ARM IHI series (AXI4, APB, etc.)
- **SystemVerilog:** IEEE 1800-2017
- **CocoTB:** https://docs.cocotb.org/
- **Verilator:** https://verilator.org/guide/latest/

---

## Quick Reference

### Common Commands

```bash
# View component specification
cat projects/components/{component}/PRD.md

# Run component tests with Makefile (RECOMMENDED)
cd projects/components/{component}/dv/tests/
make run-all-func-parallel       # Default: FUNC level, 48 workers
make run-all-gate-parallel       # Quick smoke test
make run-all-full-parallel       # Comprehensive validation
make help                        # View all available targets

# Run component tests with pytest (direct)
pytest projects/components/{component}/dv/tests/ -v

# Lint component RTL
verilator --lint-only projects/components/{component}/rtl/{module}.sv

# Generate performance reports (stream)
cd projects/components/stream/bin/dma_model/bin/
python3 comprehensive_analysis.py --report

# View waveforms
gtkwave {test_output}.vcd
```

### Makefile Targets Reference

All component Makefiles provide consistent targets:

```bash
# REG_LEVEL variants
make run-all-gate[-parallel]     # Quick smoke test (~5 min)
make run-all-func[-parallel]     # Functional coverage (~30 min, DEFAULT)
make run-all-full[-parallel]     # Comprehensive validation (~4 hr)

# Individual module targets
make run-{module}-{gate|func|full}   # Run specific module at test level

# Utility targets
make collect-all                 # Verify tests without running
make clean-all                   # Remove all test artifacts
make status                      # Show test status summary
make list-all                    # List all test modules
make help                        # Show all available targets
```

### Status Legend

- ✅ **Complete** - Fully tested, ready for use
- 🔧 **In Progress** - Active development or validation
- 🔴 **Planned** - Future component

---

**Version:** 2.0
**Last Updated:** 2025-11-11
**Maintained By:** RTL Design Sherpa Project

**Recent Updates:**
- **Miscellaneous (NEW):** Created utility component area for ROM/RAM wrappers and other reusable building blocks
- **Retro Legacy Blocks:** Reorganized apb_hpet as mega-block with 13 total peripherals (2 complete: HPET, 8254 PIT)
- **STREAM:** Nearly complete at 95%, all core blocks passing tests
- **Bridge:** 95% complete with comprehensive test infrastructure
- **BCH and HIVE:** Added as planned components with documentation structure
- Updated directory structure to reflect all 11 component areas
- Comprehensive Makefile infrastructure with REG_LEVEL support across all components
- Increased parallel test execution (48 workers)
- Unified testing methodology matching val/common and val/amba patterns

---

## Navigation

- **← Back to Root:** [`/README.md`](../../README.md)
- **Master PRD:** [`/PRD.md`](../../PRD.md)
- **Repository Guide:** [`/CLAUDE.md`](../../CLAUDE.md)
- **CocoTB Framework:** [`bin/CocoTBFramework/`](../../bin/CocoTBFramework/)
