# RTL Design Sherpa - Components Directory

**Version:** 1.0
**Last Updated:** 2025-10-18
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
| **[apb_hpet](#apb_hpet)** | Peripheral | ✅ Complete | Multi-timer with 64-bit counter | Medium |
| **[bridge](#bridge)** | Generator | 🔧 In Progress | AXI4 full crossbar generator | High |
| **[delta](#delta)** | Generator | 🔧 In Progress | AXI-Stream crossbar generator | Medium |
| **[rapids](#rapids)** | Accelerator | 🔧 In Progress | DMA with network integration | Very High |
| **[stream](#stream)** | DMA Engine | 🔧 In Progress | Tutorial-focused scatter-gather DMA | Medium-High |

---

## Component Details

### apb_hpet

**APB High Precision Event Timer**

**Status:** ✅ Complete (5/6 configurations 100% passing)

**Description:**
Configurable multi-timer peripheral with up to 8 independent hardware timers. Features 64-bit main counter, 64-bit comparators, one-shot and periodic modes, and optional clock domain crossing support.

**Key Features:**
- Configurable timer count: 2, 3, or 8 independent timers
- 64-bit main counter for high-resolution timestamps
- One-shot and periodic operating modes
- Optional CDC for timer/APB clock independence
- APB interface with PeakRDL-generated register map
- Production-ready with comprehensive test coverage

**Applications:**
- System tick generation
- Real-time OS scheduling
- Precise event timing
- Performance profiling
- Watchdog timers

**Resources:**
- RTL: `rtl/apb_hpet.sv`, `rtl/hpet_core.sv`
- Tests: `dv/tests/test_apb_hpet.py`
- Documentation: `PRD.md`, `CLAUDE.md`

**📖 See:** [`apb_hpet/PRD.md`](apb_hpet/PRD.md) for complete specification

---

### bridge

**AXI4 Full Crossbar Generator**

**Status:** 🔧 In Progress - Specification Complete

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

### stream

**STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory**

**Status:** 🔧 In Progress - Initial Design

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
- RTL: `rtl/stream_fub/*.sv` (planned)
- Tests: `dv/tests/fub_tests/`, `dv/tests/integration_tests/` (planned)
- Documentation: `PRD.md`, `CLAUDE.md`
- Performance Model: `bin/dma_model/` (comprehensive analytical + SimPy models)

**📖 See:** [`stream/PRD.md`](stream/PRD.md) for complete specification

---

## Comparison Matrix

### Protocol and Interface Support

| Component | APB | AXI4 | AXI4-Lite | AXI-Stream | Network | MonBus |
|-----------|-----|------|-----------|------------|---------|--------|
| **apb_hpet** | ✅ Slave | - | - | - | - | - |
| **bridge** | - | ✅ Crossbar | - | - | - | - |
| **delta** | - | - | - | ✅ Crossbar | - | - |
| **rapids** | - | ✅ Master | ✅ Slave | - | ✅ M/S | ✅ Master |
| **stream** | ✅ Slave | ✅ Master | - | - | - | ✅ Master |

### Complexity and Scope

| Component | RTL Modules | Test Coverage | Primary Focus | Educational Value |
|-----------|-------------|---------------|---------------|-------------------|
| **apb_hpet** | 4 | 92-100% | Production peripheral | Medium |
| **bridge** | Generated | TBD | Code generation | High |
| **delta** | Generated | TBD | Topology comparison | High |
| **rapids** | 17 | ~85% | Complex accelerator | Very High |
| **stream** | 8-10 (est.) | TBD | Tutorial DMA | High |

### Resource Utilization (Estimates)

| Component | LUTs | FFs | BRAM | Notes |
|-----------|------|-----|------|-------|
| **apb_hpet** | ~500-1200 | ~300-800 | 0 | Depends on timer count |
| **bridge** | ~2,500 | ~3,000 | 0 | 4×4 @ 512-bit |
| **delta** | ~1,600-1,920 | ~1,200 | 0 | 4×16 @ 64-bit |
| **rapids** | ~10K | ~8K | 0 | Plus SRAM (dominant) |
| **stream** | ~5K (est.) | ~4K (est.) | 0 | Plus SRAM |

---

## Directory Structure

```
projects/components/
├── apb_hpet/                    # APB High Precision Event Timer
│   ├── rtl/                     # SystemVerilog RTL
│   ├── dv/tests/                # CocoTB verification
│   ├── docs/                    # Specifications and reports
│   ├── PRD.md                   # Product requirements
│   ├── CLAUDE.md                # AI guidance
│   └── README.md                # Quick start
│
├── bridge/                      # AXI4 Crossbar Generator
│   ├── bin/                     # Python generator (planned)
│   ├── docs/                    # Specifications
│   ├── PRD.md                   # Product requirements
│   └── README.md                # Quick start (planned)
│
├── delta/                       # AXI-Stream Crossbar Generator
│   ├── bin/                     # Python generator (planned)
│   ├── docs/                    # Specifications
│   ├── PRD.md                   # Product requirements
│   └── README.md                # Quick start (planned)
│
├── rapids/                      # Rapid AXI Programmable In-band Descriptor System
│   ├── rtl/
│   │   ├── rapids_fub/          # Functional unit blocks
│   │   └── rapids_macro/        # Integration blocks
│   ├── dv/tests/
│   │   ├── fub_tests/           # Unit tests
│   │   ├── integration_tests/   # Multi-block tests
│   │   └── system_tests/        # Full system tests
│   ├── docs/
│   │   └── rapids_spec/         # Complete specification (5 chapters)
│   ├── known_issues/            # Bug tracking
│   ├── PRD.md                   # Requirements overview
│   ├── CLAUDE.md                # AI guidance
│   └── README.md                # Quick start
│
└── stream/                      # Scatter-gather Transfer Rapid Engine for AXI Memory
    ├── rtl/
    │   ├── stream_fub/          # Functional unit blocks (planned)
    │   └── stream_macro/        # Integration blocks (planned)
    ├── dv/tests/                # CocoTB verification (planned)
    ├── bin/dma_model/           # Performance models (analytical + SimPy)
    ├── docs/                    # Specifications
    ├── PRD.md                   # Product requirements
    ├── CLAUDE.md                # AI guidance
    └── README.md                # Quick start (planned)
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

#### Running APB HPET Tests

```bash
# Run all HPET tests
pytest projects/components/apb_hpet/dv/tests/ -v

# Run specific configuration
pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[2-32902-1-0-basic-2-timer Intel-like]" -v

# Run with waveforms
pytest projects/components/apb_hpet/dv/tests/ -v --vcd=hpet_debug.vcd
gtkwave hpet_debug.vcd
```

#### Running RAPIDS Tests

```bash
# FUB (unit) tests
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v
pytest projects/components/rapids/dv/tests/fub_tests/descriptor_engine/ -v

# Integration tests
pytest projects/components/rapids/dv/tests/integration_tests/ -v

# All RAPIDS tests
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

**APB HPET:**
- ✅ Need precise timing in embedded systems
- ✅ Require multiple independent timers
- ✅ Want production-ready peripheral with full verification
- ✅ Educational example of PeakRDL integration

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
1. **apb_hpet** - Simple peripheral with standard APB interface
2. **stream** - Tutorial DMA with aligned addresses
3. **delta (flat)** - Basic crossbar concepts

**Intermediate:**
1. **delta (tree)** - Topology comparisons
2. **bridge** - AXI4 full protocol
3. **stream (extended)** - Add alignment fixup

**Advanced:**
1. **rapids** - Complete accelerator with FSM coordination
2. **Custom components** - Apply learned patterns

### Key Concepts Taught

**Interfaces and Protocols:**
- APB (apb_hpet, stream)
- AXI4 (bridge, rapids, stream)
- AXI4-Lite (rapids)
- AXI-Stream (delta)
- Custom protocols (rapids Network)

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

# Run component tests
pytest projects/components/{component}/dv/tests/ -v

# Lint component RTL
verilator --lint-only projects/components/{component}/rtl/{module}.sv

# Generate performance reports (stream)
cd projects/components/stream/bin/dma_model/bin/
python3 comprehensive_analysis.py --report

# View waveforms
gtkwave {test_output}.vcd
```

### Status Legend

- ✅ **Complete** - Fully tested, ready for use
- 🔧 **In Progress** - Active development or validation
- 🔴 **Planned** - Future component

---

**Version:** 1.0
**Last Updated:** 2025-10-18
**Maintained By:** RTL Design Sherpa Project

---

## Navigation

- **← Back to Root:** [`/README.md`](../../README.md)
- **Master PRD:** [`/PRD.md`](../../PRD.md)
- **Repository Guide:** [`/CLAUDE.md`](../../CLAUDE.md)
- **CocoTB Framework:** [`bin/CocoTBFramework/`](../../bin/CocoTBFramework/)
