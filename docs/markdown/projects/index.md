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

**Last Updated:** 2026-01-04

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
**Status:** 🟡 In Development (Tutorial DMA engine)
**Location:** [`projects/components/stream/`](../../../projects/components/stream/)

Beginner-friendly descriptor-based DMA engine for memory-to-memory transfers.

**Key Features:**
- 8 independent channels with descriptor chaining
- Simple scatter-gather (aligned addresses only)
- APB configuration interface (PeakRDL)
- AXI4 master interfaces for data transfer
- Tutorial focus - intentional simplifications

**Documentation:**
- 📖 [Complete Specification](../../../projects/components/stream/docs/stream_spec/stream_index.md)
- 📋 [Product Requirements](../../../projects/components/stream/PRD.md)
- 🤖 [AI Guide](../../../projects/components/stream/CLAUDE.md)
- 📝 [Architectural Notes](../../../projects/components/stream/docs/ARCHITECTURAL_NOTES.md)

---

#### RAPIDS - Rapid Application Processing and I/O Data Streams
**Status:** 🟢 Functional (Test cleanup in progress)
**Location:** [`projects/components/rapids/`](../../../projects/components/rapids/)

Advanced descriptor-based DMA with network interfaces and complex features.

**Key Features:**
- Full alignment fixup logic
- Network TX/RX integration
- Credit-based flow control
- Control read/write engines
- Production-ready complexity

**Documentation:**
- 📖 [Complete Specification](../../../projects/components/rapids/docs/rapids_spec/rapids_index.md)
- 📋 [Product Requirements](../../../projects/components/rapids/PRD.md)
- 🤖 [AI Guide](../../../projects/components/rapids/CLAUDE.md)

---

### Integration Components

#### APB Crossbar
**Status:** ✅ Production Ready (All tests passing at 100%)
**Location:** [`projects/components/apb_xbar/`](../../../projects/components/apb_xbar/)

Parametric MxN APB interconnect connecting multiple masters to multiple slaves with automatic address-based routing and round-robin arbitration.

**Key Features:**
- Configurable M×N matrix (up to 16×16)
- Automatic address decode (64KB per slave)
- Per-slave round-robin arbitration
- Zero-bubble throughput
- RTL generator for custom configurations

**Documentation:**
- 📖 [Complete Specification](../../../projects/components/apb_xbar/docs/apb_xbar_spec/apb_xbar_index.md)
- 📋 [Product Requirements](../../../projects/components/apb_xbar/PRD.md)
- 🤖 [AI Guide](../../../projects/components/apb_xbar/CLAUDE.md)

---

#### Bridge Components
**Status:** 🟡 In Development
**Location:** [`projects/components/bridge/`](../../../projects/components/bridge/)

Protocol bridge components for bus conversion.

**Documentation:**
- 📖 [Specification](../../../projects/components/bridge/docs/)

---

#### Protocol Converters
**Status:** ✅ Production Ready (UART to AXI4-Lite)
**Location:** [`projects/components/converters/`](../../../projects/components/converters/)

Protocol conversion bridges for interfacing different communication standards.

**Key Features:**
- UART to AXI4-Lite master bridge
- ASCII command parsing (W/R commands)
- Configurable data width (32/64-bit)
- Configurable baud rate
- Timing isolation via skid buffers

**Documentation:**
- 📖 [Component Guide](converters.md) - Complete specification and usage
- 📋 [Implementation README](../../../projects/components/converters/rtl/uart_to_axil4/README.md)

---

### Retro Legacy Blocks

#### Retro Legacy Peripheral Collection
**Status:** ✅ Stable (Collection of legacy/retro peripherals)
**Location:** [`projects/components/retro_legacy_blocks/`](../../../projects/components/retro_legacy_blocks/)

Collection of legacy and retro-computing peripherals for historical SoC designs.

**Included Blocks:**
- **HPET** - High Precision Event Timer (APB interface)
- **8259 PIC** - Programmable Interrupt Controller
- **8254 PIT** - Programmable Interval Timer
- **RTC** - Real-Time Clock
- **SMBUS** - System Management Bus controller
- **PM/ACPI** - Power Management / Advanced Configuration and Power Interface
- **IOAPIC** - I/O Advanced Programmable Interrupt Controller

**Documentation:**
- 📋 [Collection Overview](../../../projects/components/retro_legacy_blocks/README.md)
- 📖 [HPET Specification](../../../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md)
- 📋 [Requirements](../../../projects/components/retro_legacy_blocks/PRD.md)
- 🤖 [AI Guide](../../../projects/components/retro_legacy_blocks/CLAUDE.md)
- 📊 [Block Status](../../../projects/components/retro_legacy_blocks/BLOCK_STATUS.md)

---

### Other Components

#### Delta
**Location:** [`projects/components/delta/`](../../../projects/components/delta/)

**Documentation:**
- 📖 [Specification](../../../projects/components/delta/docs/)

---

#### Hive
**Location:** [`projects/components/hive/`](../../../projects/components/hive/)

**Documentation:**
- 📖 [Specification](../../../projects/components/hive/docs/)

---

## Status Legend

- ✅ **Production Ready** - Complete, verified, ready for integration
- 🟢 **Functional** - Working, test cleanup/refinement ongoing
- 🟡 **In Development** - Active development, partial functionality
- 🔴 **Planned** - Design phase, not yet implemented

---

## Component Selection Guide

### When to Use Components vs. Building Blocks

**Use Components When:**
- ✅ Need complete, tested peripheral ready for SoC integration
- ✅ Require comprehensive register interface (APB, AXI)
- ✅ Need production-ready solution with verification
- ✅ Want standardized interfaces and protocols

**Use Building Blocks When:**
- ✅ Building custom logic from scratch
- ✅ Need simple, reusable primitives (counters, FIFOs, arbiters)
- ✅ Creating specialized accelerators
- ✅ Implementing vendor-specific features

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
- [bin/CocoTBFramework/](../../../bin/CocoTBFramework/) - CocoTB testbench infrastructure
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
**Last Review:** 2026-01-04
