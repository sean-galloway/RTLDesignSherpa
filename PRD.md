# Product Requirements Document (PRD)
## RTL Design Sherpa - Master Document

**Version:** 2.0
**Date:** 2025-09-30
**Status:** Active Development
**Owner:** RTL Design Sherpa Project

---

## 1. Executive Summary

**RTL Design Sherpa** is an educational and reference repository demonstrating industry-standard RTL design and verification methodologies using free/open-source tools. The project provides production-quality synthesizable SystemVerilog RTL suitable for both FPGA and ASIC implementations, along with comprehensive CocoTB-based verification infrastructure.

### 1.1 Mission Statement

*"Democratize professional RTL design by providing free, production-quality IP blocks and demonstrating industry-standard design flows that work with open-source tools."*

### 1.2 Project Goals

1. **Education** - Teach modern RTL design and verification best practices
2. **Reusability** - Provide well-tested building blocks for rapid integration
3. **Quality** - Demonstrate production-grade code quality and documentation
4. **Accessibility** - Enable FPGA/ASIC design using only free tools
5. **Standards** - Follow industry conventions and synthesizable SystemVerilog

### 1.3 Repository Metrics

| Metric | Count | Status |
|--------|-------|--------|
| **RTL Modules** | 204 | 86 common + 72 AMBA + 17 RAPIDS + 29 integration |
| **Test Files** | 136 | pytest-based validation using CocoTB |
| **Test Framework** | 196 files | Reusable BFMs, drivers, monitors, scoreboards |
| **Documentation** | Complete | PRDs, guides, specs, KNOWN_ISSUES tracking |
| **Tool Chain** | Free | Verilator, Verible, CocoTB, pytest, GTKWave |

---

## 2. Repository Architecture

### 2.1 Directory Structure

```
rtldesignsherpa/
├── rtl/                        # RTL source code (204 .sv files)
│   ├── common/                 # 86 reusable building blocks
│   ├── amba/                   # 72 AMBA protocol modules
│   ├── rapids/                   # 17 Rapid AXI Programmable In-band Descriptor System modules
│   ├── integ_*/                # Integration examples
│   └── xilinx/                 # Vendor-specific primitives
│
├── val/                        # Validation tests (136 tests)
│   ├── common/                 # Tests for rtl/common/
│   ├── amba/                   # Tests for rtl/amba/
│   ├── rapids/                   # Tests for rtl/rapids/
│   └── integ_*/                # Integration tests
│
├── bin/CocoTBFramework/        # Verification infrastructure (196 files)
│   ├── components/             # Protocol BFMs (AXI, APB, AXIS, etc.)
│   ├── tbclasses/              # Testbench classes and drivers
│   └── scoreboards/            # Verification scoreboards
│
├── docs/                       # Documentation
│   ├── AXI_Monitor_Configuration_Guide.md
│   ├── RAPIDS_Validation_Status_Report.md
│   └── markdown/               # Component documentation
│
├── PRD.md                      # This document (master PRD)
├── README.md                   # Getting started guide
└── CLAUDE.md                   # Guide for Claude Code AI assistance
```

### 2.2 Subsystem Documentation

Each major subsystem has its own detailed PRD:

- **`rtl/common/PRD.md`** - Reusable Building Blocks Library
- **`rtl/amba/PRD.md`** - AMBA Protocol Infrastructure
- **`rtl/rapids/PRD.md`** - Rapid AXI Programmable In-band Descriptor System Specification
- **`bin/CocoTBFramework/README.md`** - Verification Framework Guide

### 2.3 Organizational Standards - MANDATORY PROJECT STRUCTURE

**⚠️ CRITICAL: Framework vs Project Area Separation ⚠️**

This repository enforces a strict organizational pattern to ensure easy discovery of all project-specific code and maintain clear separation between shared infrastructure and project implementations.

#### 2.3.1 The Organizational Principle

**"All project-specific code MUST reside in the project area for easy discovery."**

The framework area (`bin/CocoTBFramework/`) contains ONLY shared, cross-project infrastructure. Project-specific testbench classes, components, and scoreboards belong in the project area under `projects/components/{name}/dv/`.

#### 2.3.2 MANDATORY Directory Structure

Every project component MUST follow this structure:

```
projects/components/{name}/
├── rtl/                        # RTL source code for this project
│   ├── includes/               # Project-specific packages
│   ├── {name}_fub/             # Functional unit blocks
│   └── {name}_macro/           # Top-level integration
│
└── dv/                         # Design verification (all project-specific)
    ├── tbclasses/              # ★ Testbench classes HERE (not framework!)
    │   ├── {module}_tb.py      # Reusable TB infrastructure
    │   └── {component}_tb.py   # Component testbenches
    │
    ├── components/             # ★ Project-specific BFMs/drivers
    │   └── {custom}_driver.py  # Project-specific components
    │
    ├── scoreboards/            # ★ Project-specific scoreboards
    │   └── {module}_scoreboard.py
    │
    └── tests/                  # Test runners (import TB classes)
        ├── fub_tests/          # Functional unit block tests
        │   └── {module}/
        │       └── test_{module}.py
        └── integration_tests/  # Multi-block integration tests
            └── test_{integration}.py
```

#### 2.3.3 Location Rules - Where Does Code Belong?

| Code Type | ✅ CORRECT Location | ❌ WRONG Location |
|-----------|---------------------|-------------------|
| **Project TB Classes** | `projects/components/{name}/dv/tbclasses/` | `bin/CocoTBFramework/tbclasses/{name}/` |
| **Project BFMs** | `projects/components/{name}/dv/components/` | `bin/CocoTBFramework/components/{name}/` |
| **Project Scoreboards** | `projects/components/{name}/dv/scoreboards/` | `bin/CocoTBFramework/scoreboards/{name}/` |
| **Test Runners** | `projects/components/{name}/dv/tests/` | Anywhere else |
| **Shared Protocol BFMs** | `bin/CocoTBFramework/components/{protocol}/` | Project area |
| **Shared Utilities** | `bin/CocoTBFramework/tbclasses/shared/` | Project area |

#### 2.3.4 Import Pattern from Project Area

Test files must import from the project area, not the framework:

**✅ CORRECT:**
```python
# Add repo root to Python path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB
from projects.components.stream.dv.tbclasses.descriptor_engine_tb import DescriptorEngineTB

# Shared infrastructure still comes from framework
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
```

**❌ WRONG:**
```python
# DON'T import project-specific TB classes from framework!
from CocoTBFramework.tbclasses.rapids.scheduler_tb import SchedulerTB  # ❌ WRONG!
```

#### 2.3.5 Framework vs Project Decision Tree

**When creating new verification code, ask:**

```
Is this code specific to a single project component (RAPIDS, STREAM, Bridge)?
├─ YES → Place in projects/components/{name}/dv/
│   Examples:
│   - RAPIDS scheduler testbench
│   - STREAM descriptor engine testbench
│   - Bridge configuration testbench
│
└─ NO → Is it reusable across multiple projects?
    ├─ YES → Place in bin/CocoTBFramework/
    │   Examples:
    │   - AXI4 protocol drivers/monitors
    │   - APB protocol drivers/monitors
    │   - TBBase class (shared base)
    │   - Memory models (generic)
    │
    └─ UNSURE → Default to project area
        You can always move to framework later if reuse emerges
```

#### 2.3.6 Current Project Components

| Project | Location | Status | TB Classes Location |
|---------|----------|--------|---------------------|
| **RAPIDS** | `projects/components/rapids/` | 🟡 Active | `rapids/dv/tbclasses/` ✅ |
| **STREAM** | `projects/components/stream/` | 🟡 Initial | `stream/dv/tbclasses/` ✅ |
| **Bridge** | `projects/components/bridge/` | 🟡 Planning | `bridge/dv/tbclasses/` ✅ |

#### 2.3.7 Benefits of This Organization

1. **Easy Discovery** - All code for a project in one place (`projects/components/{name}/`)
2. **Clear Ownership** - Project teams own their `dv/` area completely
3. **Reusability** - Shared infrastructure in framework remains clean
4. **Composability** - Projects can reference each other's code if needed
5. **Maintainability** - Changes isolated to project area don't affect others
6. **Onboarding** - New developers see complete project in one directory tree

#### 2.3.8 Migration from Framework to Project Area

If project-specific code is found in the framework area, it MUST be moved:

1. **Identify:** Search for `bin/CocoTBFramework/tbclasses/{project}/`
2. **Create:** Ensure `projects/components/{project}/dv/tbclasses/` exists
3. **Move:** Transfer TB classes to project area
4. **Update:** Fix all imports in test files
5. **Verify:** Run tests to confirm imports work
6. **Delete:** Remove old framework copy

**See:** Git commit history for examples of RAPIDS migration (2025-10-18)

---

## 3. Subsystem Overview

### 3.1 Common Library (`rtl/common/`)

**Purpose:** Technology-agnostic reusable primitives
**Modules:** 86 SystemVerilog files
**Status:** ✅ Mature, stable baseline
**Documentation:** `rtl/common/PRD.md`, `rtl/common/CLAUDE.md`

**Module Categories:**

| Category | Example Modules | Use Cases |
|----------|----------------|-----------|
| **Counters** | `counter_bin`, `counter_load_clear`, `counter_freq_invariant` | State machines, timers, event counting |
| **Arbiters** | `arbiter_round_robin`, `arbiter_round_robin_weighted` | Multi-master systems, resource sharing |
| **Data Integrity** | `dataint_crc`, `dataint_ecc_hamming_*`, `dataint_parity` | Error detection/correction, checksums |
| **Math** | `count_leading_zeros`, `bin2gray`, `bin_to_bcd` | Normalization, CDC, display conversion |
| **Clock Utilities** | `clock_divider`, `clock_gate_ctrl`, `clock_pulse` | Frequency generation, power management |
| **Encoders/Decoders** | `encoder`, `decoder`, `priority_encoder` | Address decoding, control logic |
| **Synchronizers** | `debounce`, `edge_detect`, CAM | Signal conditioning, CDC, search |

**Test Coverage:** ~90% functional coverage
**Verification:** `val/common/` (pytest + CocoTB)

---

### 3.2 AMBA Infrastructure (`rtl/amba/`)

**Purpose:** AMBA protocol monitoring and interface components
**Modules:** 72 SystemVerilog files
**Status:** 🟡 Active development, production-ready monitors
**Documentation:** `rtl/amba/PRD.md`, `docs/AXI_Monitor_Configuration_Guide.md`

**Protocols Supported:**

| Protocol | Features | Modules | Status |
|----------|----------|---------|--------|
| **AXI4** | Burst, out-of-order, outstanding | `axi4_master/slave_rd/wr_mon.sv` | ✅ Complete |
| **AXI4-Lite** | Single-beat simplified | Same base with params | ✅ Complete |
| **APB** | Peripheral bus | `apb_monitor.sv` | ✅ Complete |
| **AXI-Stream** | Streaming data | `axis_master.sv`, `axis_slave.sv` | ✅ Complete |

**Key Features:**
- Transaction tracking with error detection (SLVERR, DECERR, timeouts, orphans)
- Performance metrics (latency, throughput, threshold detection)
- Standardized 64-bit monitor bus packet format
- Configurable packet filtering to prevent congestion
- Clock gating variants for power optimization

**Test Coverage:** 95% functional coverage (6/8 comprehensive tests passing)
**Verification:** `val/amba/` (pytest + CocoTB)

**Known Issues:**
- ✅ Transaction table exhaustion (FIXED 2025-09-30)
- ⚠️ Test configuration issues for error/orphan scenarios (non-RTL)
- See `rtl/amba/KNOWN_ISSUES/` for details

---

### 3.3 Rapid AXI Programmable In-band Descriptor System (`rtl/rapids/`)

**Purpose:** Custom accelerator for memory-to-memory operations
**Modules:** 17 SystemVerilog files
**Status:** 🟡 Active development, validation in progress
**Documentation:** `rtl/rapids/PRD.md`, `rtl/rapids/rapids_spec/`

**Architecture Blocks:**

```
RAPIDS Architecture
├── Scheduler Group
│   ├── Scheduler (task management, FSM control)
│   ├── Descriptor Engine (descriptor FIFO, parsing)
│   └── Program Engine (program sequencing, alignment)
│
├── Sink Data Path (Network → SRAM → Memory)
│   ├── Network Slave (network interface ingress)
│   ├── Sink SRAM Control (buffer management)
│   └── Sink AXI Write Engine (system memory write)
│
├── Source Data Path (Memory → SRAM → Network)
│   ├── Source AXI Read Engine (system memory read)
│   ├── Source SRAM Control (buffer management)
│   └── Network Master (network interface egress)
│
└── MonBus Integration (Monitor bus reporting)
```

**Use Cases:**
- DMA-style memory-to-memory transfers
- Network packet buffering and forwarding
- Custom data path acceleration
- Example of complex FSM coordination

**Test Coverage:** ~80% functional coverage (basic scenarios validated)
**Verification:** `val/rapids/fub_tests/`, `val/rapids/integration_tests/`

**Known Issues:**
- ⚠️ Scheduler credit counter initialization bug (workaround: disable credits)
- ⚠️ Descriptor engine edge cases under stress
- See `rtl/rapids/known_issues/` for details

---

### 3.4 Verification Infrastructure (`bin/CocoTBFramework/`)

**Purpose:** Reusable CocoTB-based verification components
**Files:** 196 Python files
**Status:** ✅ Mature, actively maintained
**Documentation:** `bin/CocoTBFramework/README.md`, `bin/CocoTBFramework/CLAUDE.md`

**Component Categories:**

| Directory | Purpose | Key Components |
|-----------|---------|----------------|
| `components/` | Protocol BFMs | AXI4, APB, AXIS, GAXI, Network drivers/monitors |
| `tbclasses/` | Testbench classes | Subsystem-specific test infrastructure |
| `scoreboards/` | Transaction checking | Reference models, coverage collectors |

**Key Features:**
- Randomized transaction generation
- Protocol compliance checking
- Functional coverage collection
- Waveform correlation utilities
- Reusable across all subsystems

**Usage Examples:**
- See `val/amba/test_axi_monitor.py` for comprehensive AXI monitor testing
- See `val/rapids/fub_tests/` for RAPIDS validation patterns

---

## 4. Design Principles

### 4.1 Core Design Philosophy

1. **Reuse First**
   - Search existing modules before creating new ones
   - Adapt/parameterize rather than duplicate
   - Document reuse decisions and alternatives considered

2. **Synthesizable Only**
   - Standard IEEE 1800-2017 SystemVerilog
   - No vendor-specific primitives (except `rtl/xilinx/`)
   - FPGA and ASIC portable

3. **Test Everything**
   - Every RTL module requires CocoTB test
   - Target >95% functional coverage
   - Document test methodology

4. **Document Everything**
   - Inline comments for complex logic
   - Module headers with parameter descriptions
   - Standalone docs for subsystems (PRD, CLAUDE, TASKS, KNOWN_ISSUES)
   - **CRITICAL: No emojis in technical specifications** - Emojis break PDF generation tools (LaTeX) and appear unprofessional in formal documentation

5. **Industry Standards**
   - Follow real-world naming conventions
   - Use standard interfaces (AXI, APB, AXIS)
   - Professional coding style
   - Technical writing suitable for production documentation

### 4.2 Coding Conventions

**Module Structure:**
```systemverilog
module module_name #(
    parameter int WIDTH = 32,  // UPPER_CASE parameters
    parameter int DEPTH = 16
) (
    input  logic          i_clk,      // Input: i_* prefix
    input  logic          aresetn,    // Active-low async reset
    output logic [WIDTH-1:0] o_data,  // Output: o_* prefix
    output logic          o_valid
);
    // Internal signals
    logic [WIDTH-1:0] r_register;  // Registered: r_* prefix
    logic [WIDTH-1:0] w_wire;      // Combinational: w_* prefix

    // Logic here
endmodule
```

**Reset Convention:**
- Always use `aresetn` (active-low asynchronous reset)
- Synchronize internally if needed
- Never use positive reset (`rst`, `reset`)

**State Machines:**
- Use `typedef enum` for state definitions
- Separate state register from next-state logic
- Document state transitions

### 4.3 Verification Principles

**Test-Driven Development:**
1. Write test plan before RTL
2. Implement RTL
3. Run tests, iterate
4. Achieve coverage goals
5. Document results

**Coverage Goals:**
- Functional: >95% feature coverage
- Code: >90% line/branch coverage
- Corner cases: 100% explicit testing

**Test Organization:**
- One test file per RTL module
- Use CocoTB framework
- Leverage `bin/CocoTBFramework/` infrastructure
- Generate waveforms for debug

**🚨 MANDATORY: Pytest Function Naming Convention 🚨**

**All pytest test functions MUST follow this naming pattern to prevent conflicts:**

```python
# Pattern: test_<module_name> where <module_name> EXACTLY matches the RTL module

✅ CORRECT:
# File: val/amba/test_axi4_dwidth_converter_wr.py
def test_axi4_dwidth_converter_wr(request, params):  # ← Matches axi4_dwidth_converter_wr.sv
    """Test for write data width converter"""
    ...

# File: val/amba/test_axi4_write_master.py
def test_axi4_write_master(stub, id_width, data_width):  # ← Matches module
    """Test for AXI4 write master"""
    ...

❌ WRONG - Generic names cause pytest collection conflicts:
# File: val/amba/test_axi4_dwidth_converter_wr.py
def test_axi4_dwidth_converter(request, params):  # ← Conflicts with _rd test!
    ...

def test_converter(request, params):  # ← Too generic!
    ...
```

**Rationale:**
- Related modules (e.g., `axi4_dwidth_converter_wr.sv`, `axi4_dwidth_converter_rd.sv`) share
  the same directory (`val/amba/`)
- Pytest collects ALL test functions across files in a directory
- Generic function names like `test_axi4_dwidth_converter()` create collection conflicts
- Function names appear in logs, reports, CI - must be descriptive and unique

**Enforcement:**
- This is a **HARD REQUIREMENT** enforced in code review
- PRs with non-compliant test function names will be rejected
- File name: `test_{module}.py`
- Function name: `def test_{module}(...)` (MUST match module name)

### 4.4 Testbench Architecture Pattern

**⚠️ CRITICAL: Mandatory Separation of Concerns**

All verification follows a strict three-layer architecture for reusability and maintainability:

#### Layer 1: Testbench Class (TB)
**Location:** `bin/CocoTBFramework/tbclasses/{subsystem}/{module}_tb.py`

**Purpose:** Reusable infrastructure and base methods

**Contents:**
- BFM instantiation and management
- Clock and reset control
- DUT interface wrappers
- Base test methods (e.g., `run_basic_test()`, `run_stress_test()`)
- Protocol-specific utilities

**Example:**
```python
# bin/CocoTBFramework/tbclasses/rapids/scheduler_tb.py
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class SchedulerTB(TBBase):
    """Reusable testbench for RAPIDS Scheduler"""

    def __init__(self, dut):
        super().__init__(dut)
        # BFM instantiation
        self.apb_driver = APBDriver(dut, ...)
        self.axi_slave = AXI4SlaveWrite(dut, ...)

    async def setup_clocks_and_reset(self):
        """Standard initialization"""
        # Clock and reset sequence

    async def run_basic_test(self, num_ops=10):
        """Base method - reusable across tests"""
        # Test logic using BFMs
```

#### Layer 2: Test Runner
**Location:** `val/{subsystem}/test_{module}.py`

**Purpose:** Test intelligence and scenario logic

**Contents:**
- CocoTB test functions (prefixed with `cocotb_`)
- Pytest wrappers with parametrization
- Test-specific scenario logic
- **Imports** TB class, does NOT define it

**Example:**
```python
# val/rapids/fub_tests/scheduler/test_scheduler.py
from CocoTBFramework.tbclasses.rapids.scheduler_tb import SchedulerTB

@cocotb.test()
async def cocotb_test_basic_flow(dut):
    """Test runner - uses TB methods"""
    tb = SchedulerTB(dut)  # Import from tbclasses/
    await tb.setup_clocks_and_reset()
    result = await tb.run_basic_test(num_ops=10)
    assert result, "Basic test failed"

@pytest.mark.parametrize("num_ops", [10, 50, 100])
def test_basic_flow(num_ops, ...):
    """Pytest wrapper - handles parameters"""
    run(verilog_sources=..., module=module, ...)
```

#### Layer 3: Scoreboard (Separate Component)
**Location:** `bin/CocoTBFramework/scoreboards/{protocol}/`

**Purpose:** Transaction verification and checking

**Contents:**
- Expected vs actual comparison
- Queue-based verification (use `monitor._recvQ.popleft()`)
- Coverage collection
- **No memory models** for simple tests - direct queue access

**Example:**
```python
# bin/CocoTBFramework/scoreboards/rapids/program_engine_scoreboard.py
class ProgramEngineScoreboard:
    """Scoreboard for program engine verification"""

    def __init__(self, aw_monitor, w_monitor):
        self.aw_monitor = aw_monitor
        self.w_monitor = w_monitor

    def check_write_transaction(self, expected_addr, expected_data):
        """Verify write transaction by checking monitor queues"""
        # Access monitor queues directly
        if self.aw_monitor._recvQ:
            aw_pkt = self.aw_monitor._recvQ.popleft()
            w_pkt = self.w_monitor._recvQ.popleft()

            # Verify
            assert aw_pkt.addr == expected_addr
            assert w_pkt.data == expected_data
            return True
        return False

    def clear_queues(self):
        """Clear monitor queues after verification section"""
        self.aw_monitor._recvQ.clear()
        self.w_monitor._recvQ.clear()
```

#### Key Principles:

1. **TB = Infrastructure**
   - Contains all BFMs and hardware interface code
   - Provides reusable methods
   - Used across multiple test scenarios
   - Lives in `bin/CocoTBFramework/tbclasses/`

2. **Test = Intelligence**
   - Scenario-specific logic
   - Calls TB methods
   - Handles parametrization
   - Lives in `val/{subsystem}/`

3. **Scoreboard = Verification**
   - Separate from TB and Test
   - Uses monitor queues directly: `monitor._recvQ.popleft()`
   - No memory models for simple verification
   - Can run on test sections and clear queues

4. **Verification Strategy: Queue Access vs Memory Models**

   **Choose the right verification approach based on complexity:**

   **Direct Queue Access** (Simple, in-order scenarios):
   - Use for: Control paths, configuration interfaces, simple single-master systems
   - Example: Program engine writes, APB transactions, descriptor interfaces
   - Pattern: `aw_pkt = self.aw_monitor._recvQ.popleft()`
   - Benefits: Simple, direct, minimal overhead
   - Scoreboard clears queues after each verification section

   **Memory Models** (Complex, stateful scenarios):
   - Use for: Data paths, multi-master systems, out-of-order transactions
   - Example: DMA data transfers, memory subsystems, cache coherency
   - Pattern: `data = memory_model.read(addr, size)`
   - Benefits: Tracks memory state, handles address overlaps, validates data integrity
   - When: Multiple masters, overlapping addresses, need actual memory state tracking

   **Decision Tree:**
   ```
   Need to verify transactions?
   ├─ Is it a control/config path (APB, simple writes)?
   │  └─ YES → Use direct queue access (simple)
   │
   ├─ Is it single-master, in-order, no address overlap?
   │  └─ YES → Use direct queue access (simple)
   │
   ├─ Is it a data path with bulk transfers?
   │  └─ YES → Use memory model (tracks state)
   │
   ├─ Multiple masters with overlapping addresses?
   │  └─ YES → Use memory model (prevents conflicts)
   │
   └─ Out-of-order transactions?
      └─ YES → Use memory model (tracks completion)
   ```

   **Examples:**
   - ✅ **Queue Access**: Program engine (single write, in-order)
   - ✅ **Memory Model**: DMA sink data path (burst writes, streaming data)
   - ✅ **Queue Access**: APB configuration registers (simple read/write)
   - ✅ **Memory Model**: Multi-master AXI interconnect (address overlap)

   **Key Principle:** Use the simplest verification method that correctly validates the behavior. Don't add memory model complexity where queue access suffices.

#### Anti-Patterns to Avoid:

❌ **Wrong:** Testbench class defined inside test file
```python
# val/rapids/test_scheduler.py - WRONG!
class SchedulerTB:  # ❌ Should be in tbclasses/
    """This makes TB completely unreusable!"""
```

❌ **Wrong:** BFM code in test file
```python
# val/rapids/test_scheduler.py - WRONG!
async def send_apb_transaction():  # ❌ Should be in TB class
    """BFM logic embedded in test - not reusable!"""
```

❌ **Wrong:** Using memory models for simple verification
```python
# WRONG!
memory_model = MemoryModel()
written_data = memory_model.read(addr, 4)  # ❌ Unnecessary complexity
```

✅ **Correct:** Direct queue access
```python
# CORRECT!
aw_pkt = self.aw_monitor._recvQ.popleft()  # ✅ Simple and direct
w_pkt = self.w_monitor._recvQ.popleft()
```

#### Benefits:

- **Reusability:** Same TB used in unit, integration, system tests
- **Maintainability:** Fix bug once in TB, all tests benefit
- **Composability:** TB classes can inherit/compose for complex scenarios
- **Clarity:** Clear separation of infrastructure vs intelligence
- **Simplicity:** Queue-based verification without memory model overhead

**📖 See:**
- **`docs/VERIFICATION_ARCHITECTURE_GUIDE.md`** - Complete guide with examples for all subsystems
- `bin/CocoTBFramework/CLAUDE.md` - Framework-specific patterns
- `rtl/rapids/CLAUDE.md` Section "Rule #0" - Detailed testbench architecture
- `val/amba/test_apb_slave.py` - Reference example following this pattern

---

## 5. User Personas

### 5.1 FPGA Designer (Primary)
**Background:** Designing custom FPGA applications
**Needs:** Proven building blocks, rapid prototyping
**Uses:** `rtl/common/` for infrastructure, `rtl/amba/` for interfaces
**Skill Level:** Intermediate to advanced SystemVerilog

### 5.2 ASIC Designer (Primary)
**Background:** Designing application-specific integrated circuits
**Needs:** Technology-agnostic RTL, comprehensive verification
**Uses:** All subsystems, optimizes for area/power
**Skill Level:** Advanced SystemVerilog, industry experience

### 5.3 Verification Engineer (Primary)
**Background:** Creating testbenches and verification environments
**Needs:** Protocol monitors, BFMs, scoreboards, coverage
**Uses:** `bin/CocoTBFramework/`, `rtl/amba/` monitors, test examples
**Skill Level:** Python + SystemVerilog, CocoTB proficiency

### 5.4 Student/Learner (Secondary)
**Background:** Learning RTL design and verification
**Needs:** Well-documented examples, industry practices, free tools
**Uses:** All subsystems as learning references
**Skill Level:** Beginner to intermediate

### 5.5 Researcher/Prototyper (Tertiary)
**Background:** Rapid prototyping of custom accelerators
**Needs:** Reusable components, quick integration
**Uses:** `rtl/common/` + `rtl/amba/`, `rtl/rapids/` as example
**Skill Level:** Variable, functional focus

---

## 6. Tool Chain

### 6.1 Required Tools (All Free)

| Tool | Purpose | Version | Installation |
|------|---------|---------|--------------|
| **Verilator** | RTL simulation | 5.0+ | `sudo apt-get install verilator` |
| **Verible** | Linting | Latest | Download from GitHub releases |
| **Python** | Test infrastructure | 3.10+ | System package manager |
| **CocoTB** | Verification framework | 1.9+ | `pip install cocotb` |
| **pytest** | Test runner | Latest | `pip install pytest` |
| **GTKWave** | Waveform viewer | Latest | `sudo apt-get install gtkwave` |
| **VSCode** | IDE (optional) | Latest | Download from Microsoft |

### 6.2 Python Dependencies

See `requirements.txt` for complete list. Key packages:
- `cocotb==1.9.2` - Verification framework
- `pytest==8.2.2` - Test execution
- `cocotb-coverage==1.2.0` - Coverage collection
- `cocotbext-axi` - AXI protocol BFMs

### 6.3 Development Environment Setup

```bash
# 1. Clone repository
git clone https://github.com/sean-galloway/RTLDesignSherpa.git
cd RTLDesignSherpa

# 2. Create Python virtual environment
python3 -m venv venv
source venv/bin/activate

# 3. Install Python dependencies
pip install -r requirements.txt

# 4. Add local Python paths
source env_python

# 5. Run a test to verify setup
pytest val/common/test_counter_bin.py -v
```

---

## 7. Development Workflow

### 7.1 Creating New RTL Module

**Step 1: Search for Existing Modules**
```bash
# Search for similar functionality
find rtl/ -name "*.sv" | xargs grep -l "counter\|fifo\|arbiter"

# Review existing modules
ls rtl/common/*.sv
```

**Step 2: Create Module (if no reuse possible)**
- Follow naming convention: `{category}_{function}.sv`
- Use standard port prefixes (`i_`, `o_`, `io_`)
- Include comprehensive module header comment
- Document all parameters with valid ranges

**Step 3: Create Test**
- File: `val/{subsystem}/test_{module}.py`
- Import CocoTB framework from `bin/CocoTBFramework/`
- Target >95% functional coverage
- Include waveform dumps

**Step 4: Verify**
```bash
# Run test
pytest val/{subsystem}/test_{module}.py -v

# Check waveforms
gtkwave waves.vcd

# Lint RTL
verilator --lint-only rtl/{subsystem}/{module}.sv
```

**Step 5: Document**
- Update subsystem `PRD.md` if major feature
- Update `TASKS.md` with completion
- Add to `KNOWN_ISSUES/` if limitations found

### 7.2 Modifying Existing RTL

**Before Modifying:**
1. Read module header and inline comments
2. Check `KNOWN_ISSUES/` for documented bugs
3. Review existing tests in `val/{subsystem}/`
4. Understand module usage (grep for instantiations)

**After Modifying:**
1. Run all tests for that module
2. Run subsystem regression: `pytest val/{subsystem}/ -v`
3. Update documentation if behavior changed
4. Update tests if new features added

### 7.3 Running Tests

```bash
# Single test
pytest val/amba/test_axi_monitor.py -v

# Single test with specific parameters
pytest "val/amba/test_axi4_master_rd_mon.py::test_function[params]" -v

# All tests in subsystem
pytest val/common/ -v

# All tests in repository (long!)
pytest val/ -v

# With coverage
pytest val/amba/ --cov=rtl/amba/ --cov-report=html
```

---

## 8. Success Metrics

### 8.1 Functional Metrics

| Subsystem | Status | Tests Passing | Known Issues |
|-----------|--------|---------------|--------------|
| rtl/common/ | ✅ Stable | ~90% | None blocking |
| rtl/amba/ | 🟡 Active | 6/8 (75%) | 1 test config issue |
| rtl/rapids/ | 🟡 Active | ~80% | 1 RTL bug (workaround) |
| CocoTBFramework | ✅ Stable | N/A (library) | None |

### 8.2 Quality Metrics

- **Code Coverage:** Target >90% (currently ~85% average)
- **Functional Coverage:** Target >95% (currently ~90% average)
- **Linting:** 0 Verilator warnings (currently achieved)
- **Documentation:** All modules have tests and docs (100%)

### 8.3 Adoption Metrics

- **GitHub Stars:** Community interest indicator
- **Issues/PRs:** Community engagement
- **Educational Use:** University/bootcamp adoption
- **Production Use:** Designs deployed with these IP blocks

---

## 9. Roadmap

### 9.1 Current Status (Q4 2025)

- ✅ Common Library: Stable, mature baseline
- 🟡 AMBA Infrastructure: Active development, monitor bug fixes
- 🟡 RAPIDS: Validation in progress, known issues being addressed
- ✅ CocoTBFramework: Mature, production-ready

### 9.2 Near-Term (Q1 2026)

**rtl/amba/ Priorities:**
- Fix remaining test configuration issues
- Complete AXI4 monitor validation (8/8 tests passing)
- Document integration examples
- Performance characterization

**rtl/rapids/ Priorities:**
- Fix scheduler credit counter bug
- Complete descriptor engine stress testing
- Integration tests with realistic traffic
- Performance benchmarking

**Documentation:**
- Complete all subsystem PRD.md files
- Create integration guides
- Add more usage examples

### 9.3 Long-Term (2026+)

- **Additional Protocols:** AHB, CHI support
- **Formal Verification:** Property checking examples
- **Advanced Features:** Address filtering, ID filtering
- **Performance Optimization:** Area/power improvements
- **Educational Content:** Tutorials, videos, workshops
- **Community Growth:** Accept contributions, maintain quality

---

## 10. Known Issues Summary

### 10.1 Critical Issues (Blocking)

**None currently** - All critical bugs resolved or have workarounds

### 10.2 High Priority Issues

1. **AMBA: Test Configuration for Error Responses** (`rtl/amba/`)
   - Impact: 2 tests failing (non-RTL issue)
   - Workaround: RTL works, tests need adjustment
   - Priority: P1 (high)

2. **RAPIDS: Scheduler Credit Counter Init** (`rtl/rapids/known_issues/scheduler.md`)
   - Impact: Credit-based flow control non-functional
   - Workaround: Disable credits in tests
   - Priority: P1 (high)

### 10.3 Documentation

All issues documented in `rtl/{subsystem}/KNOWN_ISSUES/` with:
- Clear description
- Impact assessment
- Workarounds (if available)
- Fix priority
- Related test/task references

---

## 11. Getting Help

### 11.1 Documentation Resources

- **Root README:** `README.md` - Setup and getting started
- **This PRD:** Overall project requirements and structure
- **Subsystem PRDs:** `rtl/{subsystem}/PRD.md` - Detailed subsystem specs
- **Claude Guide:** `CLAUDE.md` - AI assistance guide
- **Known Issues:** `rtl/{subsystem}/KNOWN_ISSUES/` - Bug tracking
- **Configuration Guides:** `docs/` - Usage guides

### 11.2 Common Commands Quick Reference

```bash
# Run tests
pytest val/{subsystem}/test_{module}.py -v

# Lint RTL
verilator --lint-only rtl/{subsystem}/{module}.sv

# Search for modules
find rtl/ -name "*.sv" | xargs grep "^module"

# View waveforms
gtkwave waves.vcd

# Check documentation
cat rtl/{subsystem}/PRD.md
cat rtl/{subsystem}/CLAUDE.md
```

### 11.3 For Claude Code Users

See `CLAUDE.md` for comprehensive guide on:
- Repository structure and navigation
- Workflow for creating/modifying RTL
- Common patterns and anti-patterns
- Subsystem-specific guidance
- Tool commands and usage

---

## 12. References

### 12.1 Subsystem Documentation

- `rtl/common/PRD.md` - Common Library detailed spec
- `rtl/amba/PRD.md` - AMBA Infrastructure detailed spec
- `rtl/rapids/PRD.md` - RAPIDS detailed spec
- `bin/CocoTBFramework/README.md` - Verification framework guide

### 12.2 Design Guides

- `docs/AXI_Monitor_Configuration_Guide.md` - Monitor setup best practices
- `docs/RAPIDS_Validation_Status_Report.md` - RAPIDS test status
- `rtl/rapids/rapids_spec/` - Complete RAPIDS architecture specification

### 12.3 External Resources

- **CocoTB:** https://docs.cocotb.org/
- **Verilator:** https://verilator.org/guide/latest/
- **SystemVerilog LRM:** IEEE 1800-2017
- **AXI Specification:** ARM IHI0022E
- **APB Specification:** ARM IHI0024C

### 12.4 Books Referenced

- *Advanced FPGA Design* by Steve Kilts
- *Synthesis of Arithmetic Circuits* by Deschamps, Bioul, Sutter

---

**Document Version History:**

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-09-30 | Original | AXI Monitor subsystem focus |
| 2.0 | 2025-09-30 | Claude | Expanded to cover entire repository |

---

**Document Owner:** RTL Design Sherpa Project
**Last Updated:** 2025-09-30
**Review Cycle:** Quarterly or on major milestones
**Next Review:** 2026-01-01
