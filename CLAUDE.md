# Claude Code Guide for RTL Design Sherpa

**Version:** 1.0
**Last Updated:** 2025-09-30
**Purpose:** Help Claude Code work efficiently with this repository

---

## Repository Philosophy

RTL Design Sherpa demonstrates industry-standard RTL design and verification flows using free/open-source tools, suitable for both FPGA and ASIC implementation.

### Core Principles

1. **Reuse First** - Search existing modules before creating new ones
2. **Synthesizable Only** - Standard SystemVerilog, no vendor-specific primitives (except rtl/xilinx/)
3. **Test Everything** - Comprehensive CocoTB verification for all RTL
4. **Document Everything** - Inline comments + standalone documentation
5. **Industry Standards** - Follow real-world design practices and flows

---

## 📖 Global Requirements Reference

**IMPORTANT: All mandatory requirements are consolidated in `/GLOBAL_REQUIREMENTS.md`**

Before working in this repository, review the global requirements document:
- **Location:** `/GLOBAL_REQUIREMENTS.md`
- **Contents:** All MANDATORY requirements extracted from all CLAUDE.md files
- **Organization:** Categorized by RTL standards, testbench architecture, test standards, framework usage, and documentation

This CLAUDE.md provides repository-wide guidance and examples. For subsystem-specific details, see:
- `projects/components/CLAUDE.md` - Project area standards
- `bin/CocoTBFramework/CLAUDE.md` - Framework patterns
- `projects/components/{name}/CLAUDE.md` - Component-specific guidance
- `rtl/{subsystem}/CLAUDE.md` - Subsystem-specific guidance

---

## Repository Structure

```
rtldesignsherpa/
├── rtl/                    # RTL source code
│   ├── common/            # 86 reusable building blocks (counters, arbiters, FIFOs, etc.)
│   ├── amba/              # 72 AMBA protocol modules (AXI4, APB, AXIS monitors)
│   ├── rapids/              # 17 Rapid AXI Programmable In-band Descriptor System modules (custom accelerator)
│   ├── integ_*/           # Integration examples
│   └── xilinx/            # Vendor-specific primitives
├── val/                    # Validation tests (pytest + CocoTB)
│   ├── common/            # Tests for rtl/common/
│   ├── amba/              # Tests for rtl/amba/
│   ├── rapids/              # Tests for rtl/rapids/
│   └── integ_*/           # Integration tests
├── bin/CocoTBFramework/   # Reusable testbench infrastructure (196 files)
│   ├── components/        # BFMs for AXI, APB, AXIS, etc.
│   ├── tbclasses/         # Testbench classes and drivers
│   └── scoreboards/       # Verification scoreboards
├── docs/                   # Design guides and reports
└── tools/                  # Automation scripts
```

---

## 🚨 CRITICAL RULE #0: Generated File Regeneration Requirements 🚨

**⚠️ READ THIS FIRST - FAILURE TO FOLLOW CAUSES SILENT TEST FAILURES ⚠️**

### The Absolute Rule for Generated Code

**When ANY generator code changes, you MUST delete ALL generated files and regenerate everything from scratch.**

This applies to:
- **RTL generators** (bridge_generator.py, bridge_csv_generator.py, etc.)
- **Test generators** (bridge_test_generator.py, etc.)
- **Testbench generators** (any code that generates .py or .sv files)

### Why This Is Non-Negotiable

Generated files have interdependencies:
- Wrapper RTL may instantiate core RTL
- Tests may import testbench classes
- Signal names, port widths, interfaces must match across all files
- **Partial regeneration creates version mismatches causing silent failures**

### The Workflow - ALWAYS Follow This Pattern

```bash
# ❌ WRONG - Partial regeneration
vim bridge_csv_generator.py  # Make changes
python3 bridge_csv_generator.py --config 4x4  # Regenerate ONE file
# Result: Version mismatch, tests mysteriously fail!

# ✅ CORRECT - Full regeneration
vim bridge_csv_generator.py  # Make changes

# Step 1: DELETE ALL generated files
cd projects/components/bridge/rtl
rm bridge_*.sv  # Or be more selective, but delete EVERYTHING generated
cd ../dv/tests
rm test_bridge_*_generated.py  # If test generator changed
cd ../tbclasses
rm *_generated*.py  # If TB generator changed

# Step 2: Regenerate EVERYTHING
cd ../../bin
./regenerate_all_bridges.sh  # Or manually regenerate each config

# Step 3: Verify ALL tests
cd ../dv/tests
pytest -v  # Run ALL tests, not just the one you think changed
```

### What Counts as "Generator Code"?

**Any Python file that creates .sv or .py files:**
- ✅ `bridge_generator.py` - Triggers full bridge regeneration
- ✅ `bridge_csv_generator.py` - Triggers full bridge regeneration
- ✅ `bridge_test_generator.py` - Triggers full test regeneration
- ✅ `bridge_address_arbiter.py` - Triggers full regeneration (imported by generators)
- ✅ **ANY** module imported by a generator

**When in doubt:** Delete and regenerate everything.

### Symptoms of Partial Regeneration

If you see these, you probably did partial regeneration:
- ❌ Tests that previously passed now fail
- ❌ "Signal not found" errors in simulation
- ❌ Port width mismatches
- ❌ Unexpected routing behavior
- ❌ Missing debug signals
- ❌ Tests marked as xfail still failing after fix implemented

### Think Like a Compiler Developer

Generated code is like compiled object files. When you update a compiler, you run `make clean && make all`, not selective recompilation.

When you update a generator, you **delete all generated outputs and regenerate all**.

**This is not a suggestion. This is a HARD REQUIREMENT that will be enforced.**

---

## 🚨 CRITICAL RULE #0.1: Generated File Directory Organization 🚨

**⚠️ ALL GENERATED FILES MUST BE IN NAMED SUBDIRECTORIES ⚠️**

### The Absolute Rule

**Generated code MUST ALWAYS be in its associated named directory. NEVER at the top level.**

```bash
# ✅ CORRECT - Generated files in subdirectories
projects/components/bridge/rtl/bridge_4x4_rw/bridge_4x4_rw.sv
projects/components/bridge/rtl/bridge_4x4_rw/bridge_axi4_flat_4x4.sv

# ❌ WRONG - Generated files at top level
projects/components/bridge/rtl/bridge_4x4_rw.sv          # WRONG!
projects/components/bridge/rtl/bridge_axi4_flat_4x4.sv   # WRONG!
```

### Why This Matters

1. **Easy cleanup** - Delete entire subdirectory to remove all generated files
2. **No confusion** - Hand-written files stay at top level, generated files in subdirs
3. **Version control** - Clear .gitignore patterns
4. **Parallel work** - Different configs don't conflict

### Hand-Written vs Generated

**Hand-written files (top level):**
```bash
projects/components/bridge/rtl/bridge_cam.sv          # Hand-written CAM module
projects/components/bridge/rtl/Makefile               # Build script
```

**Generated files (subdirectories):**
```bash
projects/components/bridge/rtl/bridge_4x4_rw/         # All 4x4 generated files
projects/components/bridge/rtl/bridge_5x3_channels/   # All 5x3 generated files
```

### Enforcement

If you find generated files at the top level:
1. **STOP** - This is an error
2. **DELETE** stale top-level generated files
3. **REGENERATE** properly into subdirectories
4. **UPDATE** clean targets to catch this

**This is a HARD REQUIREMENT - NO EXCEPTIONS.**

---

## 📖 Organizational Requirements - See Global Requirements

**⚠️ READ THIS BEFORE WRITING ANY TESTBENCH CODE ⚠️**

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 for complete TB location requirements

**Quick Summary - Project-Specific TB Classes:**
- **RAPIDS:** `projects/components/rapids/dv/tbclasses/` ✅
- **STREAM:** `projects/components/stream/dv/tbclasses/` ✅
- **Bridge:** `projects/components/bridge/dv/tbclasses/` ✅
- **Framework (shared only):** `bin/CocoTBFramework/` ✅

**Import Pattern:**
```python
# Project-specific TBs
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared infrastructure
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
```

**Complete details:** Decision trees, anti-patterns, and rationale in `/GLOBAL_REQUIREMENTS.md`

---

## Key Subsystems

### rtl/common/ - Reusable Building Blocks
**Modules:** 86 SystemVerilog files
**Purpose:** Technology-agnostic primitives

**Key Categories:**
- **Counters:** `counter_bin.sv`, `counter_load_clear.sv`, `counter_freq_invariant.sv`
- **Arbiters:** `arbiter_round_robin*.sv` (simple, weighted, PWM variants)
- **FIFOs:** See `rtl/amba/gaxi/` for FIFO implementations
- **Math:** `count_leading_zeros.sv`, `bin2gray.sv`, etc.
- **Data Integrity:** `dataint_crc.sv`, `dataint_ecc_*.sv`, `dataint_parity.sv`
- **Clock Utilities:** `clock_divider.sv`, `clock_gate_ctrl.sv`, `clock_pulse.sv`

**Documentation:** `rtl/common/PRD.md`, `rtl/common/CLAUDE.md`

### rtl/amba/ - AMBA Protocol Infrastructure
**Modules:** 72 SystemVerilog files
**Purpose:** AXI4, AXI4-Lite, APB, AXI-Stream monitors and infrastructure

**Key Features:**
- Transaction monitoring with error detection
- Performance metrics and timeout detection
- Standardized 64-bit monitor bus protocol
- Support for burst transactions, ID reordering, backpressure

**Critical Files:**
- `shared/axi_monitor_base.sv` - Core monitor infrastructure
- `axi4/*_mon*.sv` - AXI4 master/slave read/write monitors
- `apb/apb_monitor.sv` - APB protocol monitor
- `axis/axis_master.sv`, `axis_slave.sv` - AXI-Stream interfaces

**Documentation:** `rtl/amba/PRD.md`, `rtl/amba/CLAUDE.md`, `rtl/amba/KNOWN_ISSUES/`

### rtl/rapids/ - Rapid AXI Programmable In-band Descriptor System
**Modules:** 17 SystemVerilog files
**Purpose:** Custom accelerator for memory operations

**Architecture:**
- Scheduler group (task scheduling, descriptor management)
- Sink data path (receive from network, write to memory)
- Source data path (read from memory, send to network)
- MonBus integration for monitoring

**Documentation:** `rtl/rapids/PRD.md`, `rtl/rapids/CLAUDE.md`, `rtl/rapids/known_issues/`

### bin/CocoTBFramework/ - Verification Infrastructure
**Files:** 196 Python files
**Purpose:** Reusable testbench components for CocoTB

**Key Components:**
- `components/` - Protocol-specific drivers/monitors (AXI, APB, AXIS, etc.)
- `tbclasses/` - Testbench classes for each subsystem
- `scoreboards/` - Transaction checking and coverage

**Documentation:** `bin/CocoTBFramework/README.md`, `bin/CocoTBFramework/CLAUDE.md`

---

## Workflow for Claude Code

### Starting a New Session

1. **Read the PRD** for the subsystem you're working on:
   - Root `/PRD.md` - Overall project goals
   - `rtl/{subsystem}/PRD.md` - Subsystem-specific requirements

2. **Check TASKS.md** for current priorities:
   - `rtl/{subsystem}/TASKS.md` - Active work items
   - Understand dependencies and status

3. **Review KNOWN_ISSUES/** before modifying RTL:
   - `rtl/{subsystem}/KNOWN_ISSUES/` - Documented bugs and workarounds
   - Avoid wasting time on known limitations

4. **Read subsystem CLAUDE.md** for specific guidance:
   - `rtl/{subsystem}/CLAUDE.md` - Module-specific tips
   - Common patterns and anti-patterns

### Before Creating New RTL

**CRITICAL: Always search for existing implementations first!**

```bash
# Search for similar functionality
find rtl/ -name "*.sv" | xargs grep -l "keyword"

# Find module definitions
find rtl/{subsystem}/ -name "*.sv" -exec grep -H "^module" {} \;

# Search for specific signals/parameters
grep -r "MAX_TRANSACTIONS\|FIFO_DEPTH\|ADDR_WIDTH" rtl/

# Check test usage examples
grep -r "module_name" val/
```

**Decision Tree:**
- ✅ Existing module found → Reuse with parameters
- ✅ Existing module close → Adapt/extend it
- ⚠️ Existing module insufficient → Document why, then create new
- ❌ No search performed → STOP, search first!

### Before Writing Testbenches - Check Signal Naming

**CRITICAL: Audit RTL for signal naming conflicts BEFORE writing testbench code!**

When using AXI factory functions with pattern matching, internal signals can conflict with external AXI port names, causing factory initialization failures.

**Run the Signal Naming Audit Tool:**

```bash
# Audit single file before writing testbench
./bin/audit_signal_naming_conflicts.py rtl/rapids/rapids_macro/scheduler_group.sv

# Audit entire directory
./bin/audit_signal_naming_conflicts.py rtl/rapids/

# Generate markdown report for documentation
./bin/audit_signal_naming_conflicts.py rtl/rapids/ --markdown rtl/rapids/signal_conflicts.md
```

**Why This Matters:**

AXI factory pattern matching searches for signals like `{prefix}ar_valid`, `{prefix}r_ready`, etc. If you have:
- Internal: `desc_valid`, `desc_ready` (simple handshake)
- External: `desc_ar_valid`, `desc_ar_ready` (AXI AR channel)

Both match the pattern `desc_*valid` → Factory finds BOTH signals → Initialization fails!

**Workflow:**
1. ✅ Write RTL module
2. ✅ **Run audit script to detect conflicts**
3. ✅ Fix any naming conflicts (rename internal signals)
4. ✅ Write testbench using factory pattern matching

**📖 Complete Guide:** `bin/SIGNAL_NAMING_AUDIT.md`

### Writing RTL

**Style Conventions:**
- **Module names:** `{category}_{function}.sv` (e.g., `counter_bin.sv`, `axi_monitor_base.sv`)
- **Parameters:** `UPPER_CASE` (e.g., `WIDTH`, `DEPTH`, `MAX_TRANSACTIONS`)
- **Ports:** `snake_case` with prefix
  - Inputs: `i_*` (e.g., `i_clk`, `i_data`)
  - Outputs: `o_*` (e.g., `o_valid`, `o_result`)
  - Bidirectional: `io_*`
- **Internal signals:** `snake_case` with prefix
  - Registers: `r_*` (e.g., `r_counter`, `r_state`)
  - Wires: `w_*` (e.g., `w_sum`, `w_match`)
- **Reset:** Always `aresetn` (active-low asynchronous reset)
- **Clock:** `aclk` for AXI/AMBA, `i_clk` for common modules

### Writing Tests

**Every RTL module requires a test!**

```bash
# Run specific test
pytest val/{subsystem}/test_{module}.py -v

# Run all tests in subsystem
pytest val/{subsystem}/ -v

# Run with coverage
pytest val/{subsystem}/ --cov=rtl/{subsystem}/
```

**Test Structure:**
1. Use CocoTB framework
2. Import appropriate BFMs from `bin/CocoTBFramework/`
3. Target >95% functional coverage
4. Document test methodology in file header
5. Include waveform dumps for debugging

**Test File Location:**
- `val/common/test_{module}.py` for rtl/common/
- `val/amba/test_{module}.py` for rtl/amba/
- `val/rapids/test_{module}.py` for rtl/rapids/
- `projects/components/{name}/dv/tests/` for project-specific tests

**🚨 CRITICAL: Test Structure Pattern 🚨**

The repository uses TWO different test patterns depending on the location:

**Pattern A: Direct CocoTB (val/common/, val/amba/ areas)**
```python
import cocotb
from cocotb_test.simulator import run

# CocoTB test function - direct @cocotb.test() decorator
@cocotb.test(timeout_time=3, timeout_unit="ms")
async def fifo_test(dut):
    tb = FifoBufferTB(dut, dut.clk, dut.rst_n)
    await tb.start_clock('clk', 10, 'ns')
    # ... test logic

# Pytest wrapper function
@pytest.mark.parametrize("data_width, depth", params)
def test_fifo_buffer(request, data_width, depth):
    # ... setup paths, filelist, parameters
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_name,
        module=module,  # Python module containing cocotb tests
        # ... compilation args
    )
```

**Pattern B: CocoTB + Pytest Wrappers (projects/components/ areas)**

**⚠️ HARD REQUIREMENT for projects/components/: MUST use Pattern B ⚠️**

```python
import cocotb
from cocotb_test.simulator import run

# 1. CocoTB test functions - prefix with "cocotb_test_*" to prevent pytest collection
@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic(dut):  # ← "cocotb_test_*" prefix!
    """CocoTB test function - NOT collected by pytest"""
    tb = SimpleSRAMTB(dut)
    await tb.setup_clocks_and_reset()
    # ... test logic

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_stress(dut):  # ← "cocotb_test_*" prefix!
    """Another CocoTB test function"""
    tb = SimpleSRAMTB(dut)
    await tb.setup_clocks_and_reset()
    # ... stress test logic

# 2. Pytest wrapper functions - call specific cocotb_test_* functions
@pytest.mark.parametrize("addr_width, data_width", params)
def test_basic(request, addr_width, data_width):
    """Pytest wrapper - calls cocotb_test_basic"""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/simple_sram.f'
    )

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_basic",  # ← Explicitly specify which cocotb function to run
        parameters=rtl_parameters,
        # ... compilation args
    )

@pytest.mark.parametrize("addr_width, data_width", params)
def test_stress(request, addr_width, data_width):
    """Pytest wrapper - calls cocotb_test_stress"""
    # ... same setup as above
    run(
        # ... same args except:
        testcase="cocotb_test_stress",  # ← Different cocotb function
        # ...
    )
```

**Why Two Patterns?**

| Aspect | Pattern A (val/) | Pattern B (projects/) |
|--------|------------------|----------------------|
| **CocoTB prefix** | No prefix needed | `cocotb_test_*` prefix REQUIRED |
| **Pytest collection** | Collects module | Collects only wrappers |
| **Test selection** | Runs all cocotb tests | Runs specific test via `testcase=` |
| **Use case** | Simple modules | Complex parameterized tests |
| **Example** | Counter, FIFO | SRAM, engines, integration |

**Critical Rules for Pattern B (projects/components/):**

1. **All CocoTB functions MUST be prefixed with `cocotb_test_*`**
   - Prevents pytest from collecting them as test functions
   - Only pytest wrappers (test_*) are collected

2. **Each pytest wrapper calls ONE specific CocoTB function**
   - Use `testcase="cocotb_test_name"` in run() call
   - Allows parameter sweeps at pytest level

3. **Testbench classes MUST be in project area**
   - `projects/components/{name}/dv/tbclasses/` (NOT framework!)
   - See "Organizational Requirements" section

**When to Use Which Pattern:**

- ✅ Use Pattern A: Simple modules in val/common, val/amba
- ✅ Use Pattern B: ALL tests in projects/components/
- ❌ Never mix patterns in the same file

**Complete Working Example (Pattern B):**

See `projects/components/stream/dv/tests/fub_tests/simple_sram/test_simple_sram.py` for reference implementation.

**🚨 MANDATORY: Pytest Function Naming Convention 🚨**

**All pytest test functions MUST follow this naming pattern to prevent conflicts:**

```python
# Pattern: test_<module_name>_<params> or test_<module_name>
# where <module_name> EXACTLY matches the RTL module being tested

✅ CORRECT:
@pytest.mark.parametrize("params", generate_test_params())
def test_axi4_dwidth_converter_wr(request, params):  # ← Matches module name
    """Test for axi4_dwidth_converter_wr.sv"""
    ...

def test_axi4_write_master(stub, id_width, data_width):  # ← Matches module concept
    """Test for axi4 write master functionality"""
    ...

❌ WRONG - Generic names cause conflicts:
def test_axi4_dwidth_converter(request, params):  # ← Conflicts with read converter!
    ...

def test_converter(request, params):  # ← Too generic!
    ...
```

**Why This Matters:**
- Multiple related modules (e.g., `axi4_dwidth_converter_wr.sv` and `axi4_dwidth_converter_rd.sv`)
  need separate test files in the same directory
- Pytest collects ALL test functions - generic names cause collection conflicts
- Test function name appears in logs, reports, and CI output - must be descriptive

**Enforcement:**
- This is a **HARD REQUIREMENT** - PRs with generic test names will be rejected
- When creating test files, use module name as the base: `test_{module_name}.py`
- Pytest function inside MUST match: `def test_{module_name}(...)`

**Testbench Class Requirements:**

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2 for complete three methods requirement

⚠️ **MANDATORY: Every TB class MUST implement:**
1. `async def setup_clocks_and_reset(self)` - Full initialization
2. `async def assert_reset(self)` - Assert reset signal
3. `async def deassert_reset(self)` - Release reset signal

**Quick Example:**
```python
class MyModuleTB(TBBase):
    async def setup_clocks_and_reset(self):
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.rst_n.value = 0

    async def deassert_reset(self):
        self.dut.rst_n.value = 1
```

**Complete details:** Examples, rationale, and subsystem-specific patterns in `/GLOBAL_REQUIREMENTS.md`

### Test Naming and Organization

**⚠️ CRITICAL: Single Comprehensive Test Per Module**

For complex modules (especially integration tests), use **ONE comprehensive test** with incremental levels instead of multiple separate tests.

**Naming Convention:**
- Test file: `cocotb_{module}_comprehensive.py`
- Main test function: `test_{module}_operation` (singular, not plural)
- Test levels controlled by `TEST_LEVEL` environment variable

**Test Levels:**
- **basic**: Quick smoke test (~30s, 10-20 ops per phase)
- **medium**: Moderate coverage (~90s, 30-50 ops per phase)
- **full**: Comprehensive validation (~180s, 100+ ops, 3x typical FUB test duration)

**Example Structure:**
```python
# File: cocotb_scheduler_group_comprehensive.py

@cocotb.test()
async def test_scheduler_group_operation(dut):
    """Single comprehensive test with incremental levels."""

    # Get test level from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Configure operation counts per level
    test_configs = {
        'basic': {'descriptor_count': 8, 'timing_profile': 'fast'},
        'medium': {'descriptor_count': 32, 'timing_profile': 'normal'},
        'full': {'descriptor_count': 64, 'timing_profile': 'stress'}
    }

    config = test_configs[test_level]

    # Initialize testbench
    tb = SchedulerGroupTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Run test phases with configured operation counts
    await tb.test_descriptor_processing(count=config['descriptor_count'])
    await tb.test_rda_packets(count=config['rda_count'])
    # ... more phases
```

**Rationale:**
1. **Single test = easier maintenance** - One place to update
2. **Incremental coverage** - Scale testing effort appropriately
3. **Consistent interface** - Same test, different depth
4. **Clear intent** - Test level conveys scope immediately
5. **No test proliferation** - Avoid dozens of similar tests

**Anti-Pattern to Avoid:**
```python
# ❌ DON'T: Multiple separate tests for same functionality
@cocotb.test()
async def test_basic_descriptors(dut): ...

@cocotb.test()
async def test_medium_descriptors(dut): ...

@cocotb.test()
async def test_full_descriptors(dut): ...

# ✅ DO: Single test with levels
@cocotb.test()
async def test_descriptor_operation(dut):
    test_level = os.environ.get('TEST_LEVEL', 'basic')
    # ... configure based on level
```

### Documentation Requirements

**Update ALL affected documentation:**

1. **Inline Comments:**
   - Complex logic needs explanation
   - FSM states documented
   - Parameter constraints noted
   - Interface timing requirements

2. **Module Header:**
```systemverilog
// Module: module_name
// Description: Brief description of functionality
// Parameters:
//   - PARAM1: Description, valid range, default
//   - PARAM2: Description, valid range, default
// Notes:
//   - Special constraints or assumptions
//   - Related modules or dependencies
```

3. **Update PRD.md** when:
   - Adding major features
   - Changing requirements
   - Reaching milestones

4. **Update TASKS.md** when:
   - Starting new work
   - Completing tasks
   - Discovering new issues

5. **Update KNOWN_ISSUES/** when:
   - Finding bugs
   - Identifying workarounds
   - Closing issues

6. **CRITICAL: No emojis in technical specifications**
   - Emojis break PDF generation tools (LaTeX)
   - Appear unprofessional in formal documentation
   - Use plain text for all technical documentation
   - Exception: User explicitly requests emojis (rare)

---

## Common Commands

### Simulation and Testing

```bash
# Run single test with verbose output
pytest val/amba/test_axi_monitor.py::test_axi_monitor -v -s

# Run all tests in directory
pytest val/common/ -v

# Run specific test with parameters
pytest "val/amba/test_axi4_master_rd_mon.py::test_function[param1-param2]" -v

# View waveforms (after test with VCD dump)
gtkwave waves.vcd
```

### RTL Verification

```bash
# Lint single file
verilator --lint-only rtl/amba/shared/axi_monitor_base.sv

# Check synthesis
verilator --cc rtl/common/counter_bin.sv --top-module counter_bin

# Find compilation issues
find rtl/{subsystem}/ -name "*.sv" -exec verilator --lint-only {} \;
```

### Code Search

```bash
# Find all instances of module
grep -r "^module axi_monitor" rtl/

# Find parameter usage
grep -r "parameter.*WIDTH" rtl/common/

# Find instantiations
grep -r "axi_monitor_base" rtl/

# Search test files for examples
grep -r "AxiMonitor" val/amba/
```

### Documentation

```bash
# Find all PRD files
find . -name "PRD.md" -o -name "PRD-*.md"

# Check for KNOWN_ISSUES
find rtl/ -type d -name "KNOWN_ISSUES"

# View task lists
cat rtl/*/TASKS.md
```

---

## Critical Gotchas and Warnings

### AMBA Subsystem

⚠️ **AXI Monitor Packet Congestion**
- **Issue:** Enabling all packet types simultaneously overwhelms monitor bus
- **Solution:** Use separate test configurations (see `docs/AXI_Monitor_Configuration_Guide.md`)
- **Rule:** Never enable `cfg_compl_enable` and `cfg_perf_enable` together

⚠️ **Event Reported Feedback**
- **Status:** Fixed in recent commit
- **History:** Transaction table exhaustion due to missing feedback
- **Verification:** Check `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`

### RAPIDS Subsystem

⚠️ **Scheduler Credit Counter Bug**
- **Issue:** Credit counter initializes to 0 instead of `cfg_initial_credit`
- **Impact:** Credit-based flow control non-functional
- **Workaround:** Set `cfg_use_credit = 0` in tests
- **Details:** `rtl/rapids/known_issues/scheduler.md`

### General RTL

⚠️ **Reset Convention**
- Always use `aresetn` (active-low asynchronous reset)
- Never use `rst` or `reset` (positive reset)
- Synchronize resets internally if needed

⚠️ **Parameter Overrides**
- Check instantiation parameters match module definition
- Document parameter dependencies (e.g., `DATA_WIDTH` must be power of 2)
- Use `localparam` for derived parameters

⚠️ **FIFO Depth**
- Always make FIFO depths power of 2 for efficient addressing
- Document minimum depth requirements
- Consider backpressure scenarios

---

## Quick Reference: Module Categories

### rtl/common/

| Category | Example Modules | Use Cases |
|----------|----------------|-----------|
| Counters | `counter_bin`, `counter_load_clear`, `counter_freq_invariant` | State machines, timeouts, event counting |
| Arbiters | `arbiter_round_robin`, `arbiter_round_robin_weighted` | Multi-master arbitration, scheduling |
| Math | `count_leading_zeros`, `bin2gray`, `gray2bin` | Normalization, clock domain crossing |
| Data Integrity | `dataint_crc`, `dataint_ecc_*`, `dataint_parity` | Error detection/correction |
| Clock Utilities | `clock_divider`, `clock_gate_ctrl` | Clock generation, power management |
| Encoders/Decoders | `encoder`, `decoder`, `priority_encoder` | Address decoding, control logic |

### rtl/amba/

| Protocol | Monitor Modules | Purpose |
|----------|----------------|---------|
| AXI4 | `axi4_master_rd_mon`, `axi4_master_wr_mon` | Master-side transaction monitoring |
| AXI4 | `axi4_slave_rd_mon`, `axi4_slave_wr_mon` | Slave-side transaction monitoring |
| APB | `apb_monitor` | APB protocol monitoring |
| AXIS | `axis_master`, `axis_slave` | Stream interface monitoring |
| Monitor Bus | `arbiter_*_monbus` | Monitor packet arbitration |

### bin/CocoTBFramework/

| Directory | Purpose | Key Files |
|-----------|---------|-----------|
| `components/axi4/` | AXI4 BFMs | Master/slave drivers, monitors |
| `components/apb/` | APB BFMs | APB drivers, monitors |
| `components/axis4/` | AXIS BFMs | Stream interface drivers |
| `tbclasses/amba/` | AMBA testbenches | Arbiter tests, monitor tests |
| `scoreboards/` | Verification | Transaction checking |

---

## Design Patterns to Follow

### Pattern 1: Parameterized Module

```systemverilog
module example_fifo #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 16,
    parameter int ADDR_WIDTH = $clog2(DEPTH)  // Derived parameter
) (
    input  logic                  aclk,
    input  logic                  aresetn,
    // ... ports
);
```

### Pattern 2: State Machine

```systemverilog
typedef enum logic [2:0] {
    IDLE   = 3'b000,
    ACTIVE = 3'b001,
    WAIT   = 3'b010,
    DONE   = 3'b011
} state_t;

state_t r_state, w_next_state;

// State register
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) r_state <= IDLE;
    else          r_state <= w_next_state;
end

// Next state logic
always_comb begin
    w_next_state = r_state;  // Default: hold state
    case (r_state)
        IDLE:   if (i_start) w_next_state = ACTIVE;
        ACTIVE: if (i_done)  w_next_state = DONE;
        // ...
    endcase
end
```

### Pattern 3: Module Instantiation

```systemverilog
counter_bin #(
    .WIDTH(16),
    .MAX_VALUE(1000)
) u_counter (
    .i_clk      (aclk),
    .i_rst_n    (aresetn),
    .i_enable   (w_count_enable),
    .o_count    (w_count_value),
    .o_overflow (w_count_overflow)
);
```

---

## Anti-Patterns to Avoid

❌ **Creating new modules without searching existing code**
```systemverilog
// DON'T: Write new binary counter from scratch
module my_new_counter ...

// DO: Search and reuse
// grep -r "module counter" rtl/common/
// Found: counter_bin.sv - Use this!
```

❌ **Mixing clock domains without synchronization**
```systemverilog
// DON'T:
always_ff @(posedge clk_a) r_data_a <= i_data;
always_ff @(posedge clk_b) r_data_b <= r_data_a;  // METASTABILITY!

// DO: Use proper CDC (clock domain crossing)
// See rtl/common/ for synchronizer modules
```

❌ **Incomplete reset handling**
```systemverilog
// DON'T: Mix reset styles
if (rst) ...      // Positive reset
if (!aresetn) ... // Negative reset - BE CONSISTENT

// DO: Always use aresetn (active-low)
if (!aresetn) r_reg <= '0;
else          r_reg <= w_next_value;
```

❌ **Changing code without testing**
```systemverilog
// DON'T: Modify RTL and commit without running tests
// DO:
// 1. Modify RTL
// 2. Run: pytest val/{subsystem}/test_{module}.py -v
// 3. Verify: Check waveforms if test fails
// 4. Document: Update comments and docs
// 5. Commit: Only after tests pass
```

---

## Resources and References

### Internal Documentation
- `/README.md` - Repository overview and setup instructions
- `/PRD.md` - Master product requirements document
- `rtl/{subsystem}/PRD.md` - Subsystem requirements
- `rtl/{subsystem}/CLAUDE.md` - Subsystem-specific guidance
- `rtl/{subsystem}/TASKS.md` - Current work items
- `rtl/{subsystem}/KNOWN_ISSUES/` - Bug tracking and workarounds
- `docs/` - Design guides and reports

### External Resources
- CocoTB Documentation: https://docs.cocotb.org/
- Verilator Manual: https://verilator.org/guide/latest/
- SystemVerilog LRM: IEEE 1800-2017

### Books Referenced in Repository
- *Advanced FPGA Design* by Steve Kilts
- *Synthesis of Arithmetic Circuits* by Deschamps, Bioul, Sutter

---

## Questions or Issues?

### During Development
1. Check `rtl/{subsystem}/KNOWN_ISSUES/` for documented problems
2. Review `rtl/{subsystem}/TASKS.md` for related work
3. Search existing tests in `val/{subsystem}/` for examples
4. Consult subsystem `PRD.md` for design rationale

### For New Features
1. Document in `TASKS.md` before starting
2. Search for similar existing functionality
3. Create comprehensive test plan
4. Update PRD.md with requirements

### For Bugs
1. Document in `KNOWN_ISSUES/` with:
   - Clear description
   - Reproduction steps
   - Workaround (if available)
   - Priority and impact
2. Create task in `TASKS.md` for fix
3. Update tests to catch regression

---

**Version History:**
- v1.0 (2025-09-30): Initial creation

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-09-30
