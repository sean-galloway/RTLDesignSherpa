### APB HPET - References

#### External Standards and Specifications

**AMBA Protocol Specifications:**
- **AMBA APB Protocol Specification v2.0**
  - Publisher: ARM Limited
  - Document ID: IHI 0024C
  - URL: https://developer.arm.com/documentation/ihi0024/latest
  - Relevance: APB interface protocol specification

**SystemRDL:**
- **SystemRDL 2.0 Specification**
  - Publisher: Accellera Systems Initiative
  - URL: https://www.accellera.org/downloads/standards/systemrdl
  - Relevance: Register description language for `hpet_regs.rdl`

- **PeakRDL Documentation**
  - Project: PeakRDL Register Description Language Compiler
  - URL: https://peakrdl.readthedocs.io/
  - Relevance: SystemRDL to SystemVerilog compiler tool

**Architectural Reference (Not Specification Compliant):**
- **IA-PC HPET Specification 1.0a**
  - Publisher: Intel Corporation and Microsoft Corporation
  - Date: October 2004
  - URL: https://www.intel.com/content/dam/www/public/us/en/documents/technical-specifications/software-developers-hpet-spec-1-0a.pdf
  - Relevance: Architectural inspiration (APB HPET is NOT IA-PC HPET compliant)
  - **Note:** Used as reference for timer concepts only. APB HPET uses APB interface (not memory-mapped), different register layout, and does not support legacy modes or FSB delivery.

#### Internal Project Documentation

**Component-Specific Documentation:**
- [PRD.md](../../../PRD.md) - Product Requirements Document
  - Complete functional requirements
  - Parameter specifications
  - Verification status

- [CLAUDE.md](../../../CLAUDE.md) - AI Integration Guide
  - Component architecture overview
  - Known issues and workarounds
  - Test methodology

- [TASKS.md](../../../TASKS.md) - Development Task Tracking
  - Active work items
  - Completed milestones
  - Future enhancements

- [IMPLEMENTATION_STATUS.md](../../IMPLEMENTATION_STATUS.md) - Test Results
  - Detailed test results per configuration
  - Pass/fail statistics
  - Root cause analysis

**RTL Source Files:**
- `rtl/apb_hpet.sv` - Top-level wrapper module
- `rtl/hpet_core.sv` - Core timer logic
- `rtl/hpet_config_regs.sv` - Register wrapper
- `rtl/hpet_regs.sv` - PeakRDL generated register file (from hpet_regs.rdl)
- `rtl/hpet_regs_pkg.sv` - PeakRDL generated package

**SystemRDL Specification:**
- `rtl/peakrdl/hpet_regs.rdl` - Register description
- `rtl/peakrdl/README.md` - PeakRDL generation instructions

**Testbench Files:**
- `dv/tbclasses/hpet_tb.py` - Main testbench class
- `dv/tbclasses/hpet_tests_basic.py` - Basic test suite
- `dv/tbclasses/hpet_tests_medium.py` - Medium test suite
- `dv/tbclasses/hpet_tests_full.py` - Full test suite
- `dv/tests/test_apb_hpet.py` - Test runner with pytest integration

**Known Issues Documentation:**
- `known_issues/README.md` - Issue tracking overview
- `known_issues/resolved/timer_cleanup_issue.md` - Timer corruption fix details

#### Repository-Wide Documentation

**Root Documentation:**
- `/README.md` - Repository overview and setup
- `/PRD.md` - Master project requirements
- `/CLAUDE.md` - Repository-wide AI guidance

**Framework Documentation:**
- `bin/CocoTBFramework/README.md` - Testbench framework overview
- `bin/CocoTBFramework/CLAUDE.md` - Framework usage guide
- `bin/CocoTBFramework/components/apb/README.md` - APB BFM documentation

**Verification Architecture:**
- `docs/VERIFICATION_ARCHITECTURE_GUIDE.md` - Complete verification patterns
  - Three-layer architecture (TB + Scoreboard + Test)
  - Queue-based vs memory model verification
  - Mandatory testbench methods

#### Related RTL Components

**APB Infrastructure:**
- `rtl/amba/apb/apb_slave.sv` - Standard APB slave
- `rtl/amba/apb/apb_slave_cdc.sv` - APB slave with clock domain crossing
- `rtl/amba/adapters/peakrdl_to_cmdrsp.sv` - PeakRDL adapter

**Clock Domain Crossing:**
- `rtl/amba/shared/cdc_handshake.sv` - CDC handshake synchronizer
- `rtl/common/sync_2ff.sv` - 2-stage synchronizer
- `rtl/common/sync_pulse.sv` - Pulse synchronizer

**Common Utilities:**
- `rtl/common/edge_detect.sv` - Edge detection logic (used for write strobes)
- `rtl/common/counter_bin.sv` - Binary counter (similar to HPET main counter)

#### Design Tools

**Simulation:**
- Verilator 5.0+ - RTL simulator
- CocoTB 1.9+ - Python testbench framework
- pytest 7.0+ - Test runner and parametrization

**Register Generation:**
- PeakRDL-regblock 0.17+ - SystemRDL to SystemVerilog compiler
- PeakRDL 1.0+ - SystemRDL front-end

**Waveform Viewing:**
- GTKWave - VCD waveform viewer
- GTKW files available in `dv/GTKW/` directory

#### Industry Best Practices References

**RTL Coding:**
- *Synthesis and Simulation Design Guide* - Xilinx UG901
  - Best practices for RTL coding style
  - Clock domain crossing guidelines
  - Reset strategies

- *RTL Modeling with SystemVerilog for Simulation and Synthesis* - Stuart Sutherland
  - SystemVerilog coding guidelines
  - Finite state machine design patterns

**Verification:**
- *Writing Testbenches using SystemVerilog* - Janick Bergeron
  - Testbench architecture patterns
  - Functional coverage methodology

- *Verification Methodology Manual for SystemVerilog* - Janick Bergeron et al.
  - UVM-like verification patterns
  - Coverage-driven verification

**AMBA Protocols:**
- *AMBA Design Kit (ADK)* - ARM
  - Reference implementations
  - Protocol checkers
  - Example testbenches

#### Version Control and Issue Tracking

**Git Repository:**
- Main branch: Production-ready code
- Feature branches: Active development
- Commit history: Detailed change log

**Issue Labels:**
- `bug` - Functional defects
- `enhancement` - New features
- `documentation` - Documentation updates
- `testing` - Test infrastructure improvements

#### Related Projects

**RTL Design Sherpa Components:**
- APB HPET (this component)
- AMBA AXI4 Monitors (`rtl/amba/`)
- RAPIDS DMA Engine (`projects/components/rapids/`)
- Delta Network Arbiter (`projects/components/delta/`)

**External Dependencies:**
- None - APB HPET is fully self-contained within RTL Design Sherpa

---

**Next:** [Chapter 2 - Blocks](../ch02_blocks/00_overview.md)
