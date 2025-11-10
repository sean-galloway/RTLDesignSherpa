# RTL Design Sherpa Documentation

**Repository:** [rtldesignsherpa](https://github.com/yourusername/rtldesignsherpa)

*A progressive learning framework for RTL development using open-source tools*

---

## About This Documentation

This documentation supports **RTL Design Sherpa** - a hands-on learning framework for digital hardware design. We guide you from fundamental building blocks to production-ready FPGA systems, with comprehensive verification at every step.

**What makes RTL Design Sherpa different:**
- Progressive learning path (5 levels from counters to complete SoCs)
- Comprehensive test suites using CocoTB
- Open-source tools only (Verilator, pytest, PeakRDL)
- Industry best practices
- Complete transparency - all design decisions explained

**See:** [README - Project Overview](markdown/overview.md) for complete project overview and progressive learning path

---

## Documentation Structure

### 📚 [guides/](guides/) - User Guides and How-Tos
Practical guides for using the framework and tools:
- **[AXI_Monitor_Configuration_Guide.md](guides/AXI_Monitor_Configuration_Guide.md)** - Configure AXI monitors correctly
- **[VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md)** - Verification methodology and best practices
- **[descriptor_engine_waveform_guide.md](guides/descriptor_engine_waveform_guide.md)** - Debug descriptor engines with waveforms
- **[Wavedrom_AutoBind_Guide.md](guides/Wavedrom_AutoBind_Guide.md)** - WaveDrom automatic signal binding

### 📐 [design/](design/) - Design Specifications and Analysis
Architecture and design documents:
- **[AXI4_Complete_Matrix_Phase4.md](design/AXI4_Complete_Matrix_Phase4.md)** - Complete AXI4 test matrix specification
- **[WAVEDROM_CANDIDATE_SURVEY.md](design/WAVEDROM_CANDIDATE_SURVEY.md)** - WaveDrom integration candidate analysis

### 🔬 [investigations/](investigations/) - Research and Experiments
Experimental work, optimizations attempted, lessons learned:
- **CDC Handshake Optimization** - See [investigations/README.md](investigations/README.md)
  - 3 implementation attempts, all failed
  - Valuable lessons about CDC timing
  - **Status:** Abandoned - stick with proven original design

### 📖 [markdown/](markdown/) - RTL and Framework Reference
Detailed reference documentation (auto-generated and curated):

#### Component Projects
- **[projects/components/index.md](../projects/components/index.md)** - Master component index (all components)
- **[projects/index.md](markdown/projects/index.md)** - Component documentation index
- **[projects/overview.md](markdown/projects/overview.md)** - Component ecosystem and patterns
- **[projects/apb_hpet.md](markdown/projects/apb_hpet.md)** - APB HPET Timer (redirects to Retro Legacy Blocks)
- **[retro_legacy_blocks/](../projects/components/retro_legacy_blocks/README.md)** - Legacy peripheral collection (HPET, PIC, PIT, RTC, etc.)

#### RTL Modules
- **[RTLAmba/](markdown/RTLAmba/)** - AMBA protocol modules (AXI4, APB, AXIS)
- **[RTLCommon/](markdown/RTLCommon/)** - Common building blocks (counters, FIFOs, arbiters, etc.)

#### Verification Framework
- **[CocoTBFramework/](markdown/CocoTBFramework/)** - Testbench components and BFMs
  - **[components/wavedrom/](markdown/CocoTBFramework/components/wavedrom/)** - WaveDrom integration

#### Utilities
- **[Scripts/](markdown/Scripts/)** - Utility scripts documentation
- **[TestTutorial/](markdown/TestTutorial/)** - Getting started with testing

### 🖼️ Supporting Directories
- **[images_scripts_uml/](images_scripts_uml/)** - Scripts and images for documentation
- **[logos/](logos/)** - Project logos and branding
- **[UML/](UML/)** - UML diagrams for architecture

---

## Quick Start

**New to the project?** Follow this path:

1. **[../README.md](../README.md)** - Start here! Understand the learning levels and project structure
2. **[guides/VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md)** - Learn the verification methodology
3. **[../projects/components/index.md](../projects/components/index.md)** - Browse all available components

**Looking for specific information?**

| I want to... | Go to... |
|--------------|----------|
| Configure AXI monitors | [guides/AXI_Monitor_Configuration_Guide.md](guides/AXI_Monitor_Configuration_Guide.md) |
| Understand test methodology | [guides/VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md) |
| See AXI4 test matrix | [design/AXI4_Complete_Matrix_Phase4.md](design/AXI4_Complete_Matrix_Phase4.md) |
| Learn about Retro Legacy Blocks | [../projects/components/retro_legacy_blocks/README.md](../projects/components/retro_legacy_blocks/README.md) |
| Learn about HPET Timer | [../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md](../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md) |
| Browse RTL modules | [markdown/RTLAmba/](markdown/RTLAmba/) or [markdown/RTLCommon/](markdown/RTLCommon/) |
| Use WaveDrom | [guides/Wavedrom_AutoBind_Guide.md](guides/Wavedrom_AutoBind_Guide.md) |
| Understand CDC optimization failure | [investigations/README.md](investigations/README.md) |

**Want to contribute?** See main [/CLAUDE.md](../CLAUDE.md) for repository structure and conventions

---

## Learning Levels (from Root README)

RTL Design Sherpa follows a progressive 5-level learning path:

### Level 1: Common Building Blocks (90 modules)
**Location:** `rtl/common/` | **Docs:** [../rtl/common/PRD.md](../rtl/common/PRD.md)

Learn: Counters, FIFOs, Arbiters, Math, Data Integrity
- Binary counters, Gray code, Johnson counters
- Synchronous/asynchronous FIFOs
- Round-robin arbiters, priority encoders
- CRC engines, ECC (Hamming SECDED)

### Level 2: AMBA Protocol Infrastructure (106 modules)
**Location:** `rtl/amba/` | **Docs:** [../rtl/amba/PRD.md](../rtl/amba/PRD.md)

Apply: APB, AXI4, AXI4-Lite, AXI-Stream protocols
- APB masters, slaves, crossbars
- AXI4 full protocol implementation
- AXI4-Lite register interfaces
- AXI-Stream high-throughput data

### Level 3: Integration Examples
**Locations:** `rtl/integ_common/`, `rtl/integ_amba/`

Integrate: Multi-module systems
- CDC Counter Display
- APB Crossbar (1-to-1, 1-to-4, 2-to-1, 2-to-4)
- Protocol bridges

### Level 4: Production Components (2+ components)
**Location:** `projects/components/` | **Docs:** [Component Index](../projects/components/index.md) | [Documentation Index](markdown/projects/index.md)

Build: Complete peripherals
- **APB HPET** - High Precision Event Timer (✅ Production Ready)
- **APB Crossbar** - MxN APB Interconnect (✅ Production Ready)
- **STREAM DMA** - Tutorial DMA Engine (🟡 In Development)
- **RAPIDS DMA** - Advanced DMA with Network (🟢 Functional)

### Level 5: Complete FPGA Projects
**Status:** Planned

Deploy: Full SoC designs with verification

---

## Navigation Tips

### By Document Type

- **Guides** - Practical how-tos for DOING something
- **Design** - Specifications explaining WHY things are designed this way
- **Investigations** - What was TRIED and what we LEARNED (including failures)
- **Markdown** - Complete REFERENCE for all RTL and framework code

### By Role

**If you're a student/learner:**
1. Start with [../README.md](../README.md) to understand the learning path
2. Read [guides/VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md)
3. Browse [markdown/RTLCommon/](markdown/RTLCommon/) to see basic modules
4. Check [markdown/RTLAmba/](markdown/RTLAmba/) for protocol implementations

**If you're implementing a component:**
1. Read [markdown/projects/overview.md](markdown/projects/overview.md) for patterns
2. Check [../projects/components/retro_legacy_blocks/README.md](../projects/components/retro_legacy_blocks/README.md) for collection example
3. Review [../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md](../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md) for complete peripheral example
4. See [guides/AXI_Monitor_Configuration_Guide.md](guides/AXI_Monitor_Configuration_Guide.md) for monitoring

**If you're debugging:**
1. Check [guides/descriptor_engine_waveform_guide.md](guides/descriptor_engine_waveform_guide.md)
2. Use [guides/Wavedrom_AutoBind_Guide.md](guides/Wavedrom_AutoBind_Guide.md) for timing diagrams
3. Review [investigations/](investigations/) for known issues and lessons learned

**If you're contributing:**
1. Read [/CLAUDE.md](../CLAUDE.md) - Repository structure and AI guide
2. See [guides/VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md)
3. Check [design/](design/) for specification examples

### Directory README Files

Each subdirectory has its own detailed README:
- [guides/README.md](guides/README.md) - Index of all user guides
- [design/README.md](design/README.md) - Index of design specifications
- [investigations/README.md](investigations/README.md) - Index of experimental work

---

## Key Resources

### RTL Module Documentation
- **Common Library** (90 modules): [../rtl/common/PRD.md](../rtl/common/PRD.md)
- **AMBA Infrastructure** (106 modules): [../rtl/amba/PRD.md](../rtl/amba/PRD.md)
- **Component Projects** (Master Index): [../projects/components/index.md](../projects/components/index.md)
- **Component Documentation**: [markdown/projects/index.md](markdown/projects/index.md)

### Verification Resources
- **Test Methodology**: [guides/VERIFICATION_ARCHITECTURE_GUIDE.md](guides/VERIFICATION_ARCHITECTURE_GUIDE.md)
- **CocoTB Framework**: [markdown/CocoTBFramework/](markdown/CocoTBFramework/)
- **Test Tutorials**: [markdown/TestTutorial/](markdown/TestTutorial/)

### Design Specifications
- **AXI4 Test Matrix**: [design/AXI4_Complete_Matrix_Phase4.md](design/AXI4_Complete_Matrix_Phase4.md)
- **WaveDrom Candidates**: [design/WAVEDROM_CANDIDATE_SURVEY.md](design/WAVEDROM_CANDIDATE_SURVEY.md)

### Component Documentation
- **Retro Legacy Blocks Collection**: [../projects/components/retro_legacy_blocks/README.md](../projects/components/retro_legacy_blocks/README.md)
- **HPET Timer Specification**: [../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md](../projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md)
- **Component Overview**: [markdown/projects/overview.md](markdown/projects/overview.md)
- **Component Index**: [markdown/projects/index.md](markdown/projects/index.md)

---

## External Resources

### Standards
- [AMBA Specifications](https://developer.arm.com/architectures/system-architectures/amba) - ARM protocols
- [SystemRDL 2.0](https://www.accellera.org/downloads/standards/systemrdl) - Register specification

### Tools
- [CocoTB Documentation](https://docs.cocotb.org/) - Verification framework
- [Verilator Manual](https://verilator.org/guide/latest/) - Simulator guide
- [PeakRDL Docs](https://peakrdl.readthedocs.io/) - Register generation

### Books Referenced
- *Advanced FPGA Design* by Steve Kilts
- *Synthesis of Arithmetic Circuits* by Deschamps, Bioul, Sutter

---

## Recent Updates

- **2025-10-17:** Reorganized docs into guides/, design/, investigations/ for clarity
- **2025-10-17:** Created comprehensive README navigation for all documentation
- **2025-10-17:** Added component project documentation (APB HPET, RAPIDS)
- **2025-10-17:** CDC handshake optimization documented in investigations/

---

## Technology Stack

**Simulation:** Verilator, GTKWave
**Verification:** CocoTB, pytest
**Register Generation:** PeakRDL
**Languages:** SystemVerilog, Python 3.8+
**Build:** Make, Git

**Everything is open-source!** No expensive EDA licenses required.

---

**Maintained by:** RTL Design Sherpa Contributors
**Last Updated:** 2025-10-17

---

*For complete project overview, learning path, and getting started guide, see [../README.md](../README.md)*
