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

# RTL Design Sherpa - Component Projects Index

**Last Updated:** 2026-10-12

---

## Overview

This index provides links to component project documentation within the RTL Design Sherpa repository. Each component has complete documentation in its project directory.

**Component Documentation Structure:**
- **Full Specification:** `projects/components/{name}/docs/` - Complete technical documentation
- **Requirements:** `projects/components/{name}/PRD.md` - Product requirements document
- **AI Guide:** `projects/components/{name}/CLAUDE.md` - AI-specific guidance
- **Implementation:** `projects/components/{name}/docs/IMPLEMENTATION_STATUS.md` - Test results and status

---

## Available Components

### DMA and Data Transfer

#### STREAM - Scatter-gather Transfer Rapid Engine for AXI Memory
**Status:** Ready (Tutorial DMA engine)
**Location:** [`projects/components/dma-ip/stream/`](../../../projects/components/dma-ip/stream/)

Beginner-friendly descriptor-based DMA engine for memory-to-memory transfers.

**Key Features:**
- 8 independent channels with descriptor chaining
- Simple scatter-gather (aligned addresses only)
- APB configuration interface (PeakRDL)
- AXI4 master interfaces for data transfer
- Tutorial focus - intentional simplifications

**Documentation:**
- [Complete Specification](../../../projects/components/dma-ip/stream/docs/stream_mas/stream_index.md)
- [Product Requirements](../../../projects/components/dma-ip/stream/PRD.md)
- [AI Guide](../../../projects/components/dma-ip/stream/CLAUDE.md)
- Architectural Notes *(documentation planned)*

---

#### RAPIDS - Rapid Application Processing and I/O Data Streams
**Status:** In Progress (Test cleanup in progress)
**Location:** [`projects/components/dma-ip/rapids/`](../../../projects/components/dma-ip/rapids/)

Advanced descriptor-based DMA with network interfaces and complex features.

**Key Features:**
- Full alignment fixup logic
- Network TX/RX integration
- Credit-based flow control
- Control read/write engines
- Production-ready complexity

**Documentation:**
- [Complete Specification](../../../projects/components/dma-ip/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md)
- [Product Requirements](../../../projects/components/dma-ip/rapids/PRD.md)
- [AI Guide](../../../projects/components/dma-ip/rapids/CLAUDE.md)

---

### Integration Components

#### APB Crossbar
**Status:** Production Ready (All tests passing at 100%)
**Location:** [`projects/components/fabric-gen-ip/lattice-apbx-xbar/`](../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/)

Parametric MxN APB interconnect connecting multiple masters to multiple slaves with automatic address-based routing and round-robin arbitration.

**Key Features:**
- Configurable M×N matrix (up to 16×16)
- Automatic address decode (64KB per slave)
- Per-slave round-robin arbitration
- Zero-bubble throughput
- RTL generator for custom configurations

**Documentation:**
- [Complete Specification](../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/docs/lattice_has/lattice_has_index.md)
- [Product Requirements](../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/PRD.md)
- [AI Guide](../../../projects/components/fabric-gen-ip/lattice-apbx-xbar/CLAUDE.md)

---

#### Bridge Components
**Status:** Ready (Done 2026-10-11)
**Location:** [`projects/components/fabric-gen-ip/bridge/`](../../../projects/components/fabric-gen-ip/bridge/)

Generated protocol-bridge family covering eight flavors: AXI3, AXI4, AXI5,
AXI4-Lite, AXI5-Lite, APB, APB5, and Wishbone-4 — with RDL-generated
configuration registers.

**Documentation:**
- [HAS](../../../projects/components/fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md)
- [MAS](../../../projects/components/fabric-gen-ip/bridge/docs/bridge_mas/bridge_mas_index.md)
- [GAS](../../../projects/components/fabric-gen-ip/bridge/docs/bridge_gas/bridge_gas_index.md)

---

#### Protocol Converters
**Status:** Production Ready (UART to AXI4-Lite)
**Location:** [`projects/components/utility-ip/converters/`](../../../projects/components/utility-ip/converters/)

Protocol conversion bridges for interfacing different communication standards.

**Key Features:**
- UART to AXI4-Lite master bridge
- ASCII command parsing (W/R commands)
- Configurable data width (32/64-bit)
- Configurable baud rate
- Timing isolation via skid buffers

**Documentation:**
- [Component Guide](converters.md) - Complete specification and usage
- [Implementation README](../../../projects/components/utility-ip/converters/rtl/uart_to_axil4/README.md)

---

### Memory Controllers

#### pumice — DDR2 / LPDDR2 Controller
**Status:** Ready (at rest — board-validated bring-up on Nexys A7)
**Location:** [`projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/`](../../../projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/)

**Documentation:**
- [Specification](../../../projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/pumice_mas_index.md)

---

#### scoria — DDR3 / LPDDR3 Controller
**Status:** In progress (simulation-verified — 221 tests, 9 formal blocks; board bring-up ongoing)
**Location:** [`projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/`](../../../projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/)

---

#### andesite — DDR4 / LPDDR4 Controller
**Status:** Planned (directory baseline, structure only)
**Location:** [`projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/`](../../../projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/)

---

#### granite / gabbro / diorite — product tops
**Status:** Planned (scaffolds 2026-10-11 — production-shaped tops wrapping the research rocks)
**Location:** [`projects/components/mem-ctrl-ip/product-ip/`](../../../projects/components/mem-ctrl-ip/product-ip/)

---

### Error Correction (ECC)

#### Reed-Solomon
**Status:** Ready — 1.0, hardware-loopback-validated (Nexys A7 + Genesys 2)
**Location:** [`projects/components/ecc-ip/reed-solomon/`](../../../projects/components/ecc-ip/reed-solomon/)

RS(n,k) over GF(2^m) with riBM or Euclidean solver and optional AXIS/AXI4 adapters.

**Documentation:**
- [Family README](../../../projects/components/ecc-ip/README.md)
- [PRD](../../../projects/components/ecc-ip/reed-solomon/PRD.md)

---

#### BCH
**Status:** Ready — 1.0, Genesys-2 board-validated
**Location:** [`projects/components/ecc-ip/bch/`](../../../projects/components/ecc-ip/bch/)

Binary BCH encoder/decoder importing the reed-solomon GF(2^m) layer (`gf_pkg`, riBM array).

---

### RISC-V Falcon Suite

#### kestrel — RV32I single-cycle core
**Status:** Ready — rv32ui battery 42/42 spike lockstep, riscv-formal 42/42; doc book v0.1
**Location:** [`projects/components/riscv-ip/kestrel-rv32i/`](../../../projects/components/riscv-ip/kestrel-rv32i/)

**Documentation:**
- [Suite README](../../../projects/components/riscv-ip/README.md)
- [Design spec](../../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md)

---

#### merlin / peregrine / gyrfalcon / garuda — the ladder
**Status:** Planned (structure only)
**Location:** [`projects/components/riscv-ip/`](../../../projects/components/riscv-ip/)

Educational ladder ascending in microarchitectural complexity: merlin
(5-stage pipeline, RV32I), peregrine (advanced in-order RV32IM), gyrfalcon
(OoO capstone with a baseline and an `A`-extension atomics flavor), garuda
(gyrfalcon + FPU, RV32IMAF — one past the largest falcon).

---

#### Hive
**Status:** Planned (spec only; re-homed from compute-eng-ip 2026-10-10)
**Location:** [`projects/components/riscv-ip/hive-serv/`](../../../projects/components/riscv-ip/hive-serv/)

SERV-based compute cluster — 1 VexRiscv control plane + 16 SERV monitor cores.

**Documentation:**
- [Specification](../../../projects/components/riscv-ip/hive-serv/docs/)

---

### Cache Coherence (gemstone family)

#### amber — blocking MESI snoopy L1
**Status:** In progress — HAS/MAS v1.0, RTL landing
**Location:** [`projects/components/cache-ip/amber-mesi-l1/`](../../../projects/components/cache-ip/amber-mesi-l1/)

First of the gemstone family; MonBus-instrumented research cache with ACE snoop transport.

---

#### jet / basalt / onyx
**Status:** Planned
**Location:** [`projects/components/cache-ip/`](../../../projects/components/cache-ip/)

jet — lockup-free (MSHR) MESI L1 follow-on; basalt — MOESI L2 (gated behind
onyx v1); onyx — the ACE coherence manager (CCU) that turns a pile of
coherent caches into a system.

---

### Debug / DFX

#### dfx-ip — house debug port
**Status:** Scaffold (2026-10-11) — no RTL
**Location:** [`projects/components/dfx-ip/`](../../../projects/components/dfx-ip/)

JTAG transport (jtag-tap), config poke agent (jtag-axil-agent), and the
RISC-V override plane (riscv-debug).

**Documentation:**
- [HAS index](../../../projects/components/dfx-ip/docs/dfx_has/dfx_has_index.md)

---

### Retro Legacy Blocks

#### Retro Legacy Peripheral Collection
**Status:** Stable (Collection of legacy/retro peripherals)
**Location:** [`projects/components/legacy-ip/retro_legacy_blocks/`](../../../projects/components/legacy-ip/retro_legacy_blocks/)

Collection of legacy and retro-computing peripherals for historical SoC designs.

**Included Blocks:**
- **HPET** - High Precision Event Timer (APB interface)
- **GPIO** - General Purpose I/O with interrupts
- **UART 16550** - Full 16550-compatible UART
- **8259 PIC** - Programmable Interrupt Controller
- **8254 PIT** - Programmable Interval Timer
- **RTC** - Real-Time Clock
- **SMBUS** - System Management Bus controller
- **PM/ACPI** - Power Management / Advanced Configuration and Power Interface
- **IOAPIC** - I/O Advanced Programmable Interrupt Controller

**Documentation:**
- [Collection Overview](../../../projects/components/legacy-ip/retro_legacy_blocks/README.md)
- [HPET Specification](../../../projects/components/legacy-ip/retro_legacy_blocks/docs/hpet_mas/hpet_mas_index.md)
- [Requirements](../../../projects/components/legacy-ip/retro_legacy_blocks/PRD.md)
- [AI Guide](../../../projects/components/legacy-ip/retro_legacy_blocks/CLAUDE.md)

---

## Status Legend

- **Production Ready** - Complete, verified, ready for integration
- **Functional** - Working, test cleanup/refinement ongoing
- **In Development** - Active development, partial functionality
- **Planned** - Design phase, not yet implemented

---

## Component Selection Guide

### When to Use Components vs. Building Blocks

**Use Components When:**
- Need complete, tested peripheral ready for SoC integration
- Require comprehensive register interface (APB, AXI)
- Need production-ready solution with verification
- Want standardized interfaces and protocols

**Use Building Blocks When:**
- Building custom logic from scratch
- Need simple, reusable primitives (counters, FIFOs, arbiters)
- Creating specialized accelerators
- Implementing vendor-specific features

### Learning Path Recommendations

1. **Start with STREAM** - Simplified DMA for tutorial/learning
2. **Progress to RAPIDS** - Full-featured DMA with alignment and network
3. **Integrate APB Crossbar** - Production-ready multi-master interconnect
4. **Explore Retro Blocks** - Legacy peripherals (HPET, PIC, PIT, etc.)

---

## Testing Components

### Test Hierarchy

All components follow a 3-level test hierarchy:

1. **Basic Tests** - Register access, simple functionality (<10s)
2. **Medium Tests** - Complex features, multi-component interactions (10-60s)
3. **Full Tests** - Stress testing, edge cases, CDC (60-180s)

### Running Tests

```bash
# Run all tests for a component
pytest projects/components/{name}/dv/tests/ -v

# Run specific test level
pytest projects/components/{name}/dv/tests/ -v -m basic
pytest projects/components/{name}/dv/tests/ -v -m medium
pytest projects/components/{name}/dv/tests/ -v -m full

# Run specific configuration
pytest "projects/components/{name}/dv/tests/test_{name}.py::test_function[params]" -v
```

---

## Resources

### Repository Documentation
- [Main README](../../../README.md) - Repository overview and setup
- [Master PRD](../../../PRD.md) - Project requirements and goals
- [Root CLAUDE.md](../../../CLAUDE.md) - AI assistance guide

### Building Blocks
- [rtl/common/](../../../rtl/common/) - 224 reusable building blocks (counters, math, FP)
- [rtl/amba/](../../../rtl/amba/) - 124 AMBA protocol modules (APB, AXI4, AMBA5)

### Verification Framework
- [bin/TBClasses/](../../../bin/TBClasses/) - CocoTB testbench infrastructure
- [CocoTB Documentation](https://docs.cocotb.org/) - External reference

### External Standards
- [AMBA Specifications](https://developer.arm.com/architectures/system-architectures/amba)
- [PeakRDL](https://peakrdl.readthedocs.io/) - Register generation
- [SystemRDL 2.0](https://www.accellera.org/downloads/standards/systemrdl)

---

## Component Development Structure

Each component follows this standard structure:

```
projects/components/{name}/
├── rtl/                    # RTL source code
│   ├── {name}_fub/         # Functional unit blocks
│   ├── {name}_macro/       # Top-level integration
│   └── includes/           # Package definitions
├── dv/                     # Design verification
│   ├── tests/              # Test runners (pytest + cocotb_test)
│   │   ├── fub_tests/      # Individual block tests
│   │   ├── macro_tests/    # Integration tests
│   │   └── conftest.py     # Pytest configuration
│   ├── tbclasses/          # Testbench classes (project-specific)
│   └── components/         # BFMs (if needed)
├── docs/                   # Component documentation
│   ├── {name}_spec/        # Detailed specification
│   │   ├── {name}_index.md # Specification index
│   │   ├── ch01_overview/  # Overview chapter
│   │   ├── ch02_blocks/    # Block descriptions
│   │   └── assets/         # Diagrams, waveforms
│   └── IMPLEMENTATION_STATUS.md # Test results
├── bin/                    # Component-specific scripts
├── known_issues/           # Issue tracking
├── PRD.md                  # Product requirements document
├── CLAUDE.md               # AI assistance guide
├── TASKS.md                # Work tracking
└── README.md               # Quick start guide
```

---

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2026-10-12
