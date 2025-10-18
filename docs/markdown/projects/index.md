**[← Back to Main Index](../index.md)** | **[Projects Overview](overview.md)**

# RTL Design Sherpa - Component Projects

**Last Updated:** 2025-10-17

---

## Overview

This directory contains documentation for integrated component projects in the RTL Design Sherpa repository. Unlike the simpler building blocks in `rtl/common/` and `rtl/amba/`, these are complete, production-ready mega-blocks suitable for direct SoC integration.

---

## Available Components

### APB HPET - High Precision Event Timer
**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**Location:** `projects/components/apb_hpet/`
**Documentation:** [apb_hpet.md](apb_hpet.md)

Multi-timer peripheral with 64-bit counter, one-shot/periodic modes, and optional clock domain crossing.

**Key Features:**
- Configurable 2, 3, or 8 independent timers
- 64-bit main counter and comparators
- APB4 interface with optional CDC
- PeakRDL-based register generation
- Comprehensive CocoTB verification

**Applications:**
- System tick generation
- Real-time OS scheduling
- Precise event timing
- Performance profiling
- Watchdog timers

---

## Component Categories

### Timing and Control
- **APB HPET** - Multi-timer with high-precision counter

### Communication (Future)
- **AXI Interconnect** - Planned
- **APB Crossbar** - Planned

### Memory (Future)
- **Memory Controller** - Planned
- **Cache Controller** - Planned

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

---

## Component Development Status

| Component | Status | Test Coverage | Documentation | Production Ready |
|-----------|--------|---------------|---------------|------------------|
| APB HPET  | ✅ Complete | 92-100% | Complete | Yes (5/6 configs) |

**Legend:**
- ✅ Complete and verified
- 🚧 In development
- 📋 Planned

---

## Documentation Structure

Each component includes:

1. **Component Documentation** (this directory)
   - Architecture overview
   - Design details
   - Integration examples
   - Performance characteristics

2. **Product Requirements** (`projects/components/{name}/PRD.md`)
   - Detailed specifications
   - Functional requirements
   - Verification status
   - Known issues

3. **AI Guide** (`projects/components/{name}/CLAUDE.md`)
   - AI-specific guidance
   - Common patterns and anti-patterns
   - Debugging workflows
   - Quick reference

4. **Implementation Status** (`projects/components/{name}/docs/`)
   - Test results
   - Coverage reports
   - Performance metrics

---

## Quick Links

### Component Documentation
- [Overview](overview.md) - Component ecosystem and design philosophy
- [APB HPET](apb_hpet.md) - High Precision Event Timer

### Component Source
- [APB HPET](../../../projects/components/apb_hpet/) - Source code and tests

### Design Guides
- [RTL Design Sherpa README](../../../README.md) - Repository overview
- [Master PRD](../../../PRD.md) - Project requirements

---

## Getting Started

### Using a Component

1. **Review Documentation:**
   ```bash
   # Read component overview
   cat docs/markdown/projects/apb_hpet.md

   # Review detailed requirements
   cat projects/components/apb_hpet/PRD.md
   ```

2. **Examine Integration Example:**
   ```systemverilog
   // See component documentation for RTL instantiation
   // See PRD.md Section 9 for software initialization
   ```

3. **Run Verification:**
   ```bash
   # Run component tests
   pytest projects/components/apb_hpet/dv/tests/ -v
   ```

4. **Integrate into Design:**
   - Copy RTL files or add to filelist
   - Instantiate component with desired parameters
   - Connect to bus infrastructure
   - Initialize via software

### Creating a New Component

1. **Follow RAPIDS/HPET Structure:**
   ```
   projects/components/{name}/
   ├── rtl/              # RTL source
   ├── dv/               # Design verification
   │   ├── tests/        # Test runners with conftest.py
   │   ├── tbclasses/    # Reusable testbenches (in bin/CocoTBFramework/)
   │   ├── components/   # BFMs
   │   └── scoreboards/  # Verification
   ├── docs/             # Implementation status
   ├── bin/              # Scripts
   ├── known_issues/     # Issue tracking
   ├── PRD.md            # Requirements
   ├── CLAUDE.md         # AI guide
   └── TASKS.md          # Work tracking
   ```

2. **Create Documentation:**
   - Component markdown in `docs/markdown/projects/`
   - PRD.md for requirements
   - CLAUDE.md for AI assistance

3. **Implement Verification:**
   - CocoTB testbenches in `bin/CocoTBFramework/tbclasses/`
   - Test runners with conftest.py
   - Achieve >95% coverage

---

## Component Testing

### Test Hierarchies

All components follow a 3-level test hierarchy:

1. **Basic Tests** - Register access, simple functionality
2. **Medium Tests** - Complex features, multi-component interactions
3. **Full Tests** - Stress testing, edge cases, CDC

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

### Internal
- [RTL Design Sherpa Documentation](../../README.md)
- [CocoTB Framework](../../../bin/CocoTBFramework/)
- [Common Building Blocks](../../../rtl/common/)
- [AMBA Infrastructure](../../../rtl/amba/)

### External
- [AMBA Specifications](https://developer.arm.com/architectures/system-architectures/amba)
- [PeakRDL](https://peakrdl.readthedocs.io/) - Register generation
- [CocoTB](https://docs.cocotb.org/) - Verification framework

---

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-17
