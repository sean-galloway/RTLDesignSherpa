# Claude Code Guide: RAPIDS Subsystem

**Version:** 1.0
**Last Updated:** 2025-10-11
**Purpose:** AI-specific guidance for working with RAPIDS subsystem

---

## Quick Context

**What:** Rapid AXI Programmable In-band Descriptor System - Custom DMA-style accelerator with network interfaces
**Status:** 🟡 Active development - ~80% test coverage, validation in progress
**Your Role:** Help users understand architecture, fix bugs, extend functionality

**📖 Complete Specification:** `projects/components/rapids/docs/rapids_spec/` ← **Always reference this for technical details**

---

## Critical Rules for This Subsystem

### Rule #0: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for RAPIDS documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** RAPIDS receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

### Rule #0.1: TESTBENCH ARCHITECTURE - MANDATORY SEPARATION

**⚠️ THIS IS A HARD REQUIREMENT - NO EXCEPTIONS ⚠️**

**NEVER embed testbench classes inside test runner files!**

The same testbench logic will be reused across multiple test scenarios. Having testbench code only in test files makes it COMPLETELY WORTHLESS for reuse.

**MANDATORY Structure:**

```
projects/components/rapids/dv/
├── tbclasses/                    # ★ RAPIDS TB classes HERE (not framework!)
│   ├── scheduler_tb.py           # ← REUSABLE TB CLASS
│   ├── descriptor_engine_tb.py   # ← REUSABLE TB CLASS
│   ├── rapids_integration_tb.py  # ← REUSABLE TB CLASS
│   └── [component]_tb.py         # ← REUSABLE TB CLASS
│
└── tests/                        # Test runners (import TB classes from project area)
    ├── fub_tests/
    │   ├── scheduler/
    │   │   └── test_scheduler.py     # ← TEST RUNNER ONLY (imports TB from project area)
    │   ├── descriptor_engine/
    │   │   └── test_desc_engine.py   # ← TEST RUNNER ONLY (imports TB from project area)
    └── integration_tests/
        └── test_miop_integration.py  # ← TEST RUNNER ONLY (imports TB from project area)
```

**✅ CRITICAL: All RAPIDS TB classes are in the PROJECT AREA, not the framework!**

**Test Runner Pattern (CORRECT):**
```python
# projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py

# Add repo root to Python path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB

@cocotb.test()
async def scheduler_test(dut):
    """Test runner - imports TB, runs test"""
    tb = SchedulerTB(dut)  # ← TB imported from tbclasses/
    await tb.setup_clocks_and_reset()
    await tb.run_basic_test()

@pytest.mark.parametrize("credit_mode, ...", generate_test_params())
def test_scheduler(request, credit_mode, ...):
    """Pytest runner - only handles parameters and run()"""
    # ... RTL sources, parameters, etc ...
    run(verilog_sources=..., module=module, ...)
```

**Testbench Class Pattern (CORRECT):**
```python
# projects/components/rapids/dv/tbclasses/scheduler_tb.py ✅ CORRECT LOCATION!
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class SchedulerTB(TBBase):
    """Reusable testbench for RAPIDS Scheduler validation"""

    def __init__(self, dut, **kwargs):
        super().__init__(dut)
        # TB initialization

    async def setup_clocks_and_reset(self):
        """Complete initialization - MANDATORY METHOD"""
        # Clock startup + reset sequence

    async def assert_reset(self):
        """Assert reset - MANDATORY METHOD"""
        # Put DUT in reset

    async def deassert_reset(self):
        """Deassert reset - MANDATORY METHOD"""
        # Release DUT from reset

    async def run_basic_test(self):
        # Test logic
```

**Complete Test File Structure (MANDATORY PATTERN):**

RAPIDS tests MUST follow the same pattern as AMBA tests for consistency:

```python
# projects/components/rapids/dv/tests/fub_tests/scheduler/test_scheduler.py

import os
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to Python path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
import sys
sys.path.insert(0, repo_root)

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_flow(dut):
    """Test basic descriptor flow."""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()  # Mandatory init
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow()
    assert result, "Basic descriptor flow test failed"

# Additional cocotb test functions...

# ===========================================================================
# PARAMETER GENERATION - at bottom of file
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests."""
    return [
        # (channel_id, num_channels, data_width, credit_width)
        (0, 8, 512, 8),  # Standard configuration
    ]

scheduler_params = generate_scheduler_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - at bottom of file
# ===========================================================================

@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_basic_flow(request, channel_id, num_channels, data_width, credit_width):
    """Scheduler basic flow test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub'
    })

    dut_name = "scheduler"
    verilog_sources = [
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'rtl', 'rapids', 'includes', 'rapids_pkg.sv'),
        os.path.join(rtl_dict['rtl_rapids_fub'], f'{dut_name}.sv'),
    ]

    # Format parameters for unique test name (with TBBase.format_dec())
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    cw_str = TBBase.format_dec(credit_width, 2)
    test_name_plus_params = f"test_{dut_name}_cid{cid_str}_nc{nc_str}_dw{dw_str}_cw{cw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'DATA_WIDTH': data_width,
        'CREDIT_WIDTH': credit_width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TEST_CHANNEL_ID': str(channel_id),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[
                os.path.join(repo_root, 'rtl', 'rapids', 'includes'),
                os.path.join(repo_root, 'rtl', 'amba', 'includes'),
            ],
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_basic_flow",  # ← cocotb function name
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
            sim_args=[],
            plusargs=[],
        )
        print(f"✓ Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
```

**File Structure Requirements:**

1. **✅ Testbench location:** `projects/components/rapids/dv/tbclasses/{module}_tb.py` (PROJECT AREA!)
2. **Test location:** `projects/components/rapids/dv/tests/fub_tests/{module}/test_{module}.py`
3. **CocoTB functions:** At top, prefixed with `cocotb_` to avoid pytest collection
4. **Parameter generation:** Near bottom, function + variable
5. **Pytest wrappers:** At bottom, use `@pytest.mark.parametrize()`
6. **Unique test names:** Use `TBBase.format_dec()` for formatting
7. **Parallel execution:** Handle `PYTEST_XDIST_WORKER` environment variable

**📖 Complete Documentation:** See `projects/components/rapids/PRD.md` Section 2.4 for organizational standards

**📖 See:**
- `val/amba/test_apb_slave.py` - Reference AMBA example (lines 1251-1346)
- `projects/components/rapids/PRD.md` Section 12.3 - Complete pattern documentation

**Why This Matters:**

1. **Reusability**: Same TB class used in:
   - Unit tests (`projects/components/rapids/dv/tests/fub_tests/`)
   - Integration tests (`projects/components/rapids/dv/tests/integration_tests/`)
   - System-level tests (`projects/components/rapids/dv/tests/system_tests/`)
   - User projects (external imports)

2. **Maintainability**: Fix bug once in TB class, all tests benefit

3. **Composition**: TB classes can inherit/compose for complex scenarios

#### Scoreboard Pattern: Queue-Based Verification

**⚠️ CRITICAL: No Memory Models for Simple Tests**

For simple verification scenarios, use **direct queue access** from BFM monitors instead of memory models.

**Pattern:**
```python
# bin/CocoTBFramework/scoreboards/rapids/program_engine_scoreboard.py
class ProgramEngineScoreboard:
    """Scoreboard for program engine verification"""

    def __init__(self, aw_monitor, w_monitor):
        self.aw_monitor = aw_monitor
        self.w_monitor = w_monitor

    def check_write_transaction(self, expected_addr, expected_data):
        """Verify write transaction by checking monitor queues"""
        # Access monitor queues directly - NO memory model needed
        if self.aw_monitor._recvQ:
            aw_pkt = self.aw_monitor._recvQ.popleft()
            w_pkt = self.w_monitor._recvQ.popleft()

            # Verify transaction
            assert aw_pkt.addr == expected_addr, f"Address mismatch: expected 0x{expected_addr:X}, got 0x{aw_pkt.addr:X}"
            assert w_pkt.data == expected_data, f"Data mismatch: expected 0x{expected_data:X}, got 0x{w_pkt.data:X}"
            return True
        return False

    def clear_queues(self):
        """Clear monitor queues after verification section"""
        self.aw_monitor._recvQ.clear()
        self.w_monitor._recvQ.clear()
```

**Usage in Testbench:**
```python
# bin/CocoTBFramework/tbclasses/rapids/program_engine_tb.py
class ProgramEngineTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Create AXI monitors
        self.aw_monitor = AXI4AWMonitor(dut, ...)
        self.w_monitor = AXI4WMonitor(dut, ...)

        # Create scoreboard
        self.scoreboard = ProgramEngineScoreboard(self.aw_monitor, self.w_monitor)

    async def verify_write_operation(self, expected_addr, expected_data):
        """TB method: Verify write operation using scoreboard"""
        # Wait for transaction
        await self.wait_for_transaction(self.aw_monitor)

        # Use scoreboard to verify
        result = self.scoreboard.check_write_transaction(expected_addr, expected_data)

        # Clear queues for next test section
        self.scoreboard.clear_queues()

        return result
```

**Key Principles:**

1. **Direct Queue Access:**
   - Use `monitor._recvQ.popleft()` to get transactions
   - No intermediate memory model needed
   - Simple and direct verification

2. **Scoreboard Runs on Sections:**
   - Verify transactions as they complete
   - Clear queues after each verification section
   - Prevents queue buildup and memory issues

3. **No Out-of-Order Complexity:**
   - For simple in-order tests, queue order matches transaction order
   - Memory models only needed for complex OOO scenarios
   - Example: Program engine writes are always in-order

4. **Example Queue Access:**
```python
# Getting items from monitor queue
wr_pkt = self.aw_monitor._recvQ.popleft()  # ✅ Simple and direct

# DON'T use memory models for simple tests
memory_model = MemoryModel()  # ❌ Unnecessary complexity
data = memory_model.read(addr)  # ❌ Extra layer of indirection
```

**When to Use Memory Models:**
- ❌ **Simple in-order tests** - Use queue access
- ❌ **Single-master systems** - Use queue access
- ✅ **Complex out-of-order scenarios** - Memory model may help
- ✅ **Multi-master with address overlap** - Memory model tracks state

**Benefits of Queue-Based Verification:**
- **Simplicity:** Direct verification without intermediate models
- **Performance:** No memory model overhead
- **Clarity:** Clear transaction-by-transaction verification
- **Debugging:** Easy to inspect queue contents

**📖 See:**
- **`docs/VERIFICATION_ARCHITECTURE_GUIDE.md`** - Complete guide with examples and decision trees
- `PRD.md` Section 4.4 - Complete testbench architecture pattern
- `bin/CocoTBFramework/CLAUDE.md` - Framework verification patterns

---

### Rule #0.5: MANDATORY TB INITIALIZATION METHODS

**⚠️ EVERY TESTBENCH CLASS MUST IMPLEMENT THESE THREE METHODS ⚠️**

All testbench classes must provide standardized clock and reset control:

#### 1. `async def setup_clocks_and_reset(self)`
**Purpose:** Complete initialization - starts clocks AND performs reset sequence

**Implementation Pattern:**
```python
async def setup_clocks_and_reset(self):
    """Setup clocks and perform complete reset sequence"""
    # Start all required clocks
    await self.start_clock('clk', freq=10, units='ns')  # From TBBase

    # CRITICAL: Set any config signals that must be valid BEFORE reset
    # Example: Exponential credit encoding must be set before reset
    self.dut.cfg_initial_credit.value = 4  # Set before reset!
    self.dut.cfg_use_credit.value = 1

    # Perform reset
    await self.assert_reset()
    await self.wait_clocks(self.clk_name, 10)  # Hold reset for 10 cycles
    await self.deassert_reset()
    await self.wait_clocks(self.clk_name, 5)   # Stabilization time
```

#### 2. `async def assert_reset(self)`
**Purpose:** Assert reset signal(s) - puts DUT into reset state

**Implementation Pattern:**
```python
async def assert_reset(self):
    """Assert reset signal (active-low)"""
    self.dut.rst_n.value = 0  # Active-low reset
    # OR for active-high: self.dut.rst.value = 1
```

#### 3. `async def deassert_reset(self)`
**Purpose:** Deassert reset signal(s) - releases DUT from reset

**Implementation Pattern:**
```python
async def deassert_reset(self):
    """Deassert reset signal (active-low)"""
    self.dut.rst_n.value = 1  # Release active-low reset
    # OR for active-high: self.dut.rst.value = 0
```

#### Complete Example:
```python
class MyModuleTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

    async def setup_clocks_and_reset(self):
        """Complete initialization"""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Set config before reset (if needed)
        self.dut.cfg_param.value = 5

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset"""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset"""
        self.rst_n.value = 1
```

#### Why This Pattern?

1. **Consistency**: All tests use the same initialization sequence
2. **Reusability**: Tests can selectively call just `assert_reset()` or `deassert_reset()` for mid-test resets
3. **Clarity**: Explicit methods make test intent clear
4. **Configuration Control**: Some RTL requires specific signals set BEFORE reset (e.g., exponential encoding)
5. **Debugging**: Easy to add instrumentation/logging in one place

#### Common Mistake to Avoid:

```python
❌ WRONG: Inline reset without methods
async def some_test(self):
    self.dut.rst_n.value = 0  # Hard to maintain, not reusable
    await self.wait_clocks('clk', 10)
    self.dut.rst_n.value = 1

✅ CORRECT: Use standardized methods
async def some_test(self):
    await self.assert_reset()
    await self.wait_clocks(self.clk_name, 10)
    await self.deassert_reset()
```

#### Test Usage Pattern:

```python
@cocotb.test()
async def test_basic_function(dut):
    """Test runner"""
    tb = MyModuleTB(dut)

    # Full initialization
    await tb.setup_clocks_and_reset()

    # Run test
    result = await tb.test_basic_operation()
    assert result, "Test failed"

@cocotb.test()
async def test_reset_recovery(dut):
    """Test reset during operation"""
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()

    # Start operation
    await tb.start_operation()

    # Mid-test reset
    await tb.assert_reset()
    await tb.wait_clocks(tb.clk_name, 10)
    await tb.deassert_reset()

    # Verify recovery
    result = await tb.verify_recovery()
    assert result, "Recovery failed"
```

---

###  Rule #0.75: Audit Signal Naming BEFORE Writing Testbenches

**⚠️ CRITICAL: Check for Signal Naming Conflicts BEFORE Factory Usage ⚠️**

Before writing testbench code that uses AXI factory functions, audit your RTL for signal naming conflicts.

**The Problem:**
AXI factory pattern matching searches for signals using prefix + channel patterns (e.g., `{prefix}ar_valid`, `{prefix}r_ready`). If you have:
- Internal signals: `desc_valid`, `desc_ready` (simple handshake)
- External AXI ports: `desc_ar_valid`, `desc_ar_ready` (AXI AR channel)

Both match `desc_*valid` → Factory finds BOTH signals → Initialization FAILS!

**Solution - Signal Naming Audit Tool:**

```bash
# Audit single file before writing testbench
../../bin/audit_signal_naming_conflicts.py projects/components/rapids/rtl/rapids_macro/scheduler_group.sv

# Audit entire RAPIDS subsystem
../../bin/audit_signal_naming_conflicts.py projects/components/rapids/rtl/

# Generate markdown report
../../bin/audit_signal_naming_conflicts.py projects/components/rapids/rtl/ --markdown signal_conflicts.md
```

**Known RAPIDS Conflicts:**
See `projects/components/rapids/known_issues/scheduler_group_signal_naming_conflicts.md` for documented conflicts in scheduler_group.sv:
- `desc` prefix: 4 internal + 4 external (AR/R channels)
- `prog` prefix: 4 internal + 6 external (AW/W/B channels)

**Recommended Workflow:**
1. ✅ Write RTL module with signals
2. ✅ **Run audit script to detect conflicts**
3. ✅ Fix naming conflicts (rename internal signals with `_to_sched` suffix)
4. ✅ Write testbench using factory pattern matching

**Three Solutions When Conflicts Found:**
1. **Rename internal signals** (recommended): `desc_valid` → `desc_to_sched_valid`
2. **Use explicit signal_map**: Bypass pattern matching with manual signal mapping
3. **Test at higher level**: Where internal signals aren't visible (e.g., miop_top)

**📖 Complete Guide:** `bin/SIGNAL_NAMING_AUDIT.md`

---

### Rule #1: MANDATORY BFM Usage for FUB-Level Tests

**⚠️ CRITICAL DESIGN INTENTION - USE FRAMEWORK BFMs ⚠️**

**For all RAPIDS FUB (Functional Unit Block) level tests, you MUST use appropriate BFMs from the CocoTB Framework:**

**Interface Type → Required BFM Component:**

| Interface Type | Framework Component Location | Usage |
|----------------|----------------------------|-------|
| **Custom valid/ready** | `bin/CocoTBFramework/components/gaxi/` | **GAXI Master/Slave BFMs** |
| **AXI4** | `bin/CocoTBFramework/components/axi4/` | AXI4 Master/Slave drivers |
| **AXI4-Lite (AXIL)** | `bin/CocoTBFramework/components/axil4/` | AXIL Master/Slave drivers |
| **APB** | `bin/CocoTBFramework/components/apb/` | APB Master/Slave drivers |
| **AXI-Stream (AXIS)** | `bin/CocoTBFramework/components/axis4/` | AXIS Master/Slave drivers |
| **Network** | `bin/CocoTBFramework/components/network/` | Network Master/Slave drivers |
| **MonBus** | `bin/CocoTBFramework/components/monbus/` | MonBus drivers |

**Critical Rules:**

1. **NEVER manually drive valid/ready handshakes** - Use GAXI BFM components
2. **NEVER create custom protocol drivers** - Framework components already exist
3. **NEVER embed simple handshake logic** - Extract to GAXI Master/Slave

**Example - Program Engine Interface:**

```python
# ❌ WRONG: Manual handshake driving
async def send_program_request(self, addr, data):
    # Manually driving program_valid/program_ready - DON'T DO THIS!
    self.dut.program_valid.value = 1
    self.dut.program_pkt_addr.value = addr
    self.dut.program_pkt_data.value = data
    while int(self.dut.program_ready.value) == 0:
        await self.wait_clocks(self.clk_name, 1)
    await self.wait_clocks(self.clk_name, 1)
    self.dut.program_valid.value = 0

# ✅ CORRECT: Use GAXI Master BFM
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster

class ProgramEngineTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Create GAXI master for program interface
        self.program_master = GAXIMaster(
            dut=dut,
            clock=dut.clk,
            valid_signal='program_valid',
            ready_signal='program_ready',
            data_signals=['program_pkt_addr', 'program_pkt_data'],
            data_widths=[64, 32],
            name='program_interface'
        )

    async def send_program_request(self, addr, data):
        # Use GAXI master for proper handshaking
        await self.program_master.write({'program_pkt_addr': addr, 'program_pkt_data': data})
```

**Why This Rule Exists:**

1. **Consistency**: All tests use same handshake protocol
2. **Correctness**: GAXI BFMs handle complex timing scenarios correctly
3. **Reusability**: Same BFM used across all RAPIDS tests
4. **Maintainability**: Fix once in BFM, all tests benefit
5. **Coverage**: GAXI BFMs include timing randomization and backpressure

**When Manual Driving is Acceptable:**

- ✅ **Quick debug/prototype** - Temporary, will be replaced with BFM
- ✅ **Clock/reset initialization** - Not part of protocol handshaking
- ❌ **Production testbenches** - MUST use BFMs

**Search Before Creating:**

```bash
# Find existing GAXI components
find bin/CocoTBFramework/components/gaxi/ -name "*.py"

# Find example usage
grep -r "GAXIMaster\|GAXISlave" projects/components/rapids/dv/tests/fub_tests/
grep -r "from.*gaxi" bin/CocoTBFramework/tbclasses/
```

**BFM Selection Guide:**

```
Need to drive interface with valid/ready?
├─ Standard protocol (AXI4, APB, AXIS, Network)?
│  └─ Use protocol-specific BFM (axi4/, apb/, axis4/, network/)
│
├─ Custom RAPIDS interface with valid/ready signals?
│  └─ Use GAXI Master/Slave BFM (gaxi/)
│
└─ MonBus monitor packet interface?
   └─ Use MonBus BFM (monbus/)
```

**📖 See:**
- `bin/CocoTBFramework/components/gaxi/README.md` - GAXI BFM documentation
- `bin/CocoTBFramework/components/axi4/README.md` - AXI4 BFM documentation
- `val/amba/test_*.py` - Reference examples using framework BFMs

---

### Rule #2: Always Reference Detailed Specification

**This subsystem has extensive documentation in** `projects/components/rapids/docs/rapids_spec/`

**Before answering technical questions:**
```bash
# Check complete specification
ls projects/components/rapids/docs/rapids_spec/
cat projects/components/rapids/docs/rapids_spec/miop_index.md
cat projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md
```

**Your answer should:**
1. Provide direct answer/code
2. **Then link to detailed spec:** "See `projects/components/rapids/docs/rapids_spec/{file}.md` for complete specification"

### Rule #3: Know the Known Issues

**Fixed Critical Issue:**
- ✅ **Scheduler Credit Counter - FIXED** (projects/components/rapids/rtl/rapids_fub/scheduler.sv:567-570)
  - Was: Credit counter hardcoded to 0
  - Now: Implements exponential encoding (0→1, 1→2, 2→4, ..., 15→∞)
  - Impact: Credit-based flow control now functional with proper encoding
  - Tests: Verify exponential decoding works correctly
  - Priority: P0 (Critical - COMPLETED)

**Always check:** `projects/components/rapids/known_issues/` before diagnosing bugs

```bash
ls projects/components/rapids/known_issues/
cat projects/components/rapids/known_issues/scheduler.md
```

### Rule #4: RAPIDS is Complex - Understand Block Interactions

**Key Interaction Patterns:**

1. **Descriptor Flow:**
   ```
   Software → AXIL4 → Descriptor Engine → Scheduler → Data Paths
   ```

2. **Sink Data Path (Network → Memory):**
   ```
   Network Slave → Sink SRAM Control → Sink AXI Write Engine → System Memory
   ```

3. **Source Data Path (Memory → Network):**
   ```
   System Memory → Source AXI Read Engine → Source SRAM Control → Network Master
   ```

4. **Monitoring:**
   ```
   All Blocks → MonBus Reporter → MonBus Output
   ```

**Never work on one block in isolation without understanding its upstream/downstream dependencies!**

### Rule #5: Test Strategy is Multi-Layered

**RAPIDS testing follows this hierarchy:**

1. **FUB (Functional Unit Block) Tests:** `projects/components/rapids/dv/tests/fub_tests/`
   - Individual block testing
   - Focus: Module-level functionality
   - Example: Scheduler FSM, Descriptor Engine FIFO

2. **Integration Tests:** `projects/components/rapids/dv/tests/integration_tests/`
   - Multi-block scenarios
   - Focus: Block-to-block interfaces
   - Example: Scheduler + Descriptor Engine, Sink data path end-to-end

3. **System Tests:** `projects/components/rapids/dv/tests/system_tests/`
   - Full RAPIDS operation
   - Focus: Realistic traffic patterns
   - Example: Complete DMA transfer with monitoring

**When creating/modifying tests, ensure appropriate test layer is used!**

---

## Architecture Quick Reference

### Block Organization

```
RAPIDS Architecture (17 SystemVerilog modules)
├── Scheduler Group
│   ├── scheduler.sv              (Task FSM, credit management)
│   ├── descriptor_engine.sv      (Descriptor FIFO, parsing)
│   └── program_engine.sv         (Program sequencing, alignment)
│
├── Sink Data Path (Network → Memory)
│   ├── network_slave.sv             (Network ingress)
│   ├── sink_sram_control.sv      (Buffer management)
│   └── sink_axi_write_engine.sv  (AXI4 write to system memory)
│
├── Source Data Path (Memory → Network)
│   ├── source_axi_read_engine.sv (AXI4 read from system memory)
│   ├── source_sram_control.sv    (Buffer management)
│   └── network_master.sv            (Network egress)
│
└── MonBus AXIL Group
    ├── axil4_slave.sv            (Control/status registers)
    └── monbus_reporter.sv        (Monitor packet generation)
```

**📖 See:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/00_overview.md` for detailed block descriptions

### Module Quick Reference

| Module | Location | Purpose | Documentation |
|--------|----------|---------|---------------|
| **scheduler.sv** | `rapids_fub/` | Task FSM, credit management | `rapids_spec/ch02_blocks/01_01_scheduler.md` |
| **descriptor_engine.sv** | `rapids_fub/` | Descriptor FIFO, parsing | `rapids_spec/ch02_blocks/01_02_descriptor_engine.md` |
| **program_engine.sv** | `rapids_fub/` | Program sequencing | `rapids_spec/ch02_blocks/01_03_program_engine.md` |
| **network_slave.sv** | `rapids_fub/` | Network ingress | `rapids_spec/ch02_blocks/02_01_network_slave.md` |
| **sink_sram_control.sv** | `rapids_fub/` | Sink buffer management | `rapids_spec/ch02_blocks/02_02_sink_sram_control.md` |
| **sink_axi_write_engine.sv** | `rapids_fub/` | Memory writes | `rapids_spec/ch02_blocks/02_03_sink_axi_write_engine.md` |
| **source_axi_read_engine.sv** | `rapids_fub/` | Memory reads | `rapids_spec/ch02_blocks/03_03_source_axi_read_engine.md` |
| **source_sram_control.sv** | `rapids_fub/` | Source buffer management | `rapids_spec/ch02_blocks/03_02_source_sram_control.md` |
| **network_master.sv** | `rapids_fub/` | Network egress | `rapids_spec/ch02_blocks/03_01_network_master.md` |
| **miop_top.sv** | `rapids_macro/` | Top-level integration | `rapids_spec/ch03_interfaces/01_top_level.md` |

### Interface Summary

| Interface | Type | Width | Purpose | Specification |
|-----------|------|-------|---------|---------------|
| **AXIL4** | Slave | 32-bit | Control/status registers | `rapids_spec/ch03_interfaces/02_axil_interface_spec.md` |
| **AXI4 (Sink)** | Master | Configurable | Write to system memory | `rapids_spec/ch03_interfaces/03_axi4_interface_spec.md` |
| **AXI4 (Source)** | Master | Configurable | Read from system memory | `rapids_spec/ch03_interfaces/03_axi4_interface_spec.md` |
| **Network (Sink)** | Slave | Configurable | Network ingress | `rapids_spec/ch03_interfaces/04_network_interface_spec.md` |
| **Network (Source)** | Master | Configurable | Network egress | `rapids_spec/ch03_interfaces/04_network_interface_spec.md` |
| **MonBus** | Master | 64-bit | Monitor packet output | `rapids_spec/ch03_interfaces/05_monbus_interface_spec.md` |

---

## Common User Questions and Responses

### Q: "How does the scheduler work?"

**A: Direct answer:**

The scheduler is a complex FSM that coordinates RAPIDS operations:

1. **Idle State:** Waits for descriptors from Descriptor Engine
2. **Parse State:** Extracts descriptor fields (address, length, control)
3. **Credit Check:** Verifies credit availability (if credit mode enabled)
4. **Execute State:** Activates appropriate data path (sink or source)
5. **Monitor State:** Tracks operation progress
6. **Complete State:** Generates completion packets, updates credits

**Key FSM States:**
- `IDLE` → `PARSE` → `CREDIT_CHECK` → `EXECUTE` → `MONITOR` → `COMPLETE` → `IDLE`

**Credit Management:**
- ✅ **FIXED:** Exponential credit encoding now implemented (lines 567-570)
- **Encoding:** 0→1, 1→2, 2→4, 3→8, ..., 14→16384, 15→∞ (unlimited)
- **See Q&A below** for complete encoding table and details

**📖 See:**
- `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md` - Complete FSM specification
- `projects/components/rapids/known_issues/scheduler.md` - Known bugs and workarounds

### Q: "How do I configure RAPIDS?"

**A: Configuration via AXIL4 interface:**

```systemverilog
// 1. Initialize RAPIDS via AXIL4 writes
// Configure SRAM depths
write_axil(ADDR_SINK_SRAM_DEPTH, 1024);
write_axil(ADDR_SOURCE_SRAM_DEPTH, 1024);

// Set timeout thresholds
write_axil(ADDR_TIMEOUT_THRESHOLD, 1000);

// Configure initial credits (exponential encoding)
// 0→1, 1→2, 2→4, 3→8, 4→16, etc.
write_axil(ADDR_INITIAL_CREDIT, 4);  // 4 = 16 credits (2^4)
write_axil(ADDR_CREDIT_ENABLE, 1);   // ✅ Enable credit mode (now fixed!)

// 2. Load descriptors
write_descriptor(addr, length, control_bits);

// 3. Enable operation
write_axil(ADDR_ENABLE, 1);
```

**📖 See:**
- `projects/components/rapids/docs/rapids_spec/ch04_programming_models/01_programming.md` - Programming model
- `projects/components/rapids/docs/rapids_spec/ch05_registers/01_registers.md` - Register definitions

### Q: "What's the data flow for network to memory transfer?"

**A: Sink path data flow:**

```
1. Network Packet Arrives
   ↓
2. Network Slave receives packet
   - Validates packet format
   - Handshakes with Network interface
   ↓
3. Sink SRAM Control buffers data
   - Writes to SRAM
   - Manages write pointers
   - Handles backpressure
   ↓
4. Sink AXI Write Engine
   - Reads from SRAM
   - Generates AXI4 write transactions
   - Bursts data to system memory
   ↓
5. Completion Reporting
   - Generates MonBus completion packet
   - Updates scheduler state
```

**Key Considerations:**
- SRAM acts as buffer to decouple network from memory timing
- AXI4 bursts used for efficient memory access
- Backpressure propagates from memory to network

**📖 See:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/02_00_sink_data_path.md`

### Q: "What's the credit counter bug and how does exponential encoding work?"

**A: Scheduler credit counter exponential encoding:**

The scheduler uses **exponential credit encoding** to provide a wide range of credit values (1 to 16384) with a compact 4-bit configuration:

**Encoding Table:**
| `cfg_initial_credit` | Actual Credits | Use Case |
|---------------------|----------------|----------|
| 0 | 1 | Minimum (2^0) |
| 1 | 2 | Very low traffic (2^1) |
| 2 | 4 | Low traffic (2^2) |
| 3 | 8 | (2^3) |
| 4 | 16 | Typical (2^4) |
| 5 | 32 | (2^5) |
| 6 | 64 | Medium traffic (2^6) |
| 7 | 128 | (2^7) |
| 8 | 256 | High traffic (2^8) |
| 10 | 1024 | Very high traffic (2^10) |
| 14 | 16384 | Maximum finite (2^14) |
| 15 | ∞ (0xFFFFFFFF) | Unlimited credits |

**✅ FIXED Implementation:**
```systemverilog
// projects/components/rapids/rtl/rapids_fub/scheduler.sv:567-570
// Exponential credit encoding: 0→1, 1→2, 2→4, ..., 14→16384, 15→∞
r_descriptor_credit_counter <= (cfg_initial_credit == 4'hF) ? 32'hFFFFFFFF :
                              (cfg_initial_credit == 4'h0) ? 32'h00000001 :
                              (32'h1 << cfg_initial_credit);
```

**Was Broken (Before Fix):**
```systemverilog
r_descriptor_credit_counter <= 32'h0;  // ❌ WRONG: Hardcoded to 0
```

**Impact (Before Fix):**
- Credit-based flow control didn't work
- All operations blocked if credit mode enabled
- Descriptors never processed

**Encoding Rationale:**
- Compact 4-bit config covers wide range: 1 to 16384 credits
- Fine-grained control for low traffic (1, 2, 4, 8)
- High-throughput support (256, 1024, 16384)
- Special unlimited mode (15 → ∞)

**Important:** Exponential encoding applies **only at initialization**. Once running, the counter operates linearly (increment/decrement by 1).

**📖 See:**
- `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md` - Complete encoding table
- `projects/components/rapids/known_issues/scheduler.md` - Bug details and fix verification

### Q: "How do I run RAPIDS tests?"

**A: Multi-layered test approach:**

```bash
# 1. FUB (Functional Unit Block) Tests - Individual blocks
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v
pytest projects/components/rapids/dv/tests/fub_tests/descriptor_engine/ -v
pytest projects/components/rapids/dv/tests/fub_tests/ -v  # All FUB tests

# 2. Integration Tests - Multi-block scenarios
pytest projects/components/rapids/dv/tests/integration_tests/ -v

# 3. System Tests - Full RAPIDS operation
pytest projects/components/rapids/dv/tests/system_tests/ -v

# Run with waveforms for debugging
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ --vcd=debug.vcd
gtkwave debug.vcd
```

**Test Organization:**
- **FUB tests:** Focus on individual block functionality
- **Integration tests:** Verify block-to-block interfaces
- **System tests:** Validate complete data flows

**Current Status:** ~80% functional coverage, basic scenarios validated

**📖 See:** `docs/RAPIDS_Validation_Status_Report.md` for detailed test results

---

## Integration Patterns

### Pattern 1: Basic RAPIDS Instantiation

```systemverilog
miop_top #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .Network_DATA_WIDTH(64),
    .SRAM_DEPTH(1024),
    .MAX_DESCRIPTORS(16)
) u_miop (
    // Clock and Reset
    .aclk               (system_clk),
    .aresetn            (system_rst_n),

    // AXIL4 Control Interface
    .s_axil_awaddr      (ctrl_awaddr),
    .s_axil_awvalid     (ctrl_awvalid),
    .s_axil_awready     (ctrl_awready),
    .s_axil_wdata       (ctrl_wdata),
    .s_axil_wstrb       (ctrl_wstrb),
    .s_axil_wvalid      (ctrl_wvalid),
    .s_axil_wready      (ctrl_wready),
    .s_axil_bresp       (ctrl_bresp),
    .s_axil_bvalid      (ctrl_bvalid),
    .s_axil_bready      (ctrl_bready),
    .s_axil_araddr      (ctrl_araddr),
    .s_axil_arvalid     (ctrl_arvalid),
    .s_axil_arready     (ctrl_arready),
    .s_axil_rdata       (ctrl_rdata),
    .s_axil_rresp       (ctrl_rresp),
    .s_axil_rvalid      (ctrl_rvalid),
    .s_axil_rready      (ctrl_rready),

    // AXI4 Memory Interface (Sink - Write)
    .m_axi_sink_awaddr  (mem_sink_awaddr),
    .m_axi_sink_awlen   (mem_sink_awlen),
    .m_axi_sink_awsize  (mem_sink_awsize),
    .m_axi_sink_awburst (mem_sink_awburst),
    .m_axi_sink_awvalid (mem_sink_awvalid),
    .m_axi_sink_awready (mem_sink_awready),
    // ... additional AXI4 sink write channel signals

    // AXI4 Memory Interface (Source - Read)
    .m_axi_source_araddr  (mem_source_araddr),
    .m_axi_source_arlen   (mem_source_arlen),
    .m_axi_source_arsize  (mem_source_arsize),
    .m_axi_source_arburst (mem_source_arburst),
    .m_axi_source_arvalid (mem_source_arvalid),
    .m_axi_source_arready (mem_source_arready),
    // ... additional AXI4 source read channel signals

    // Network Network Interface (Sink - Receive)
    .s_network_tdata       (net_rx_data),
    .s_network_tvalid      (net_rx_valid),
    .s_network_tready      (net_rx_ready),
    .s_network_tlast       (net_rx_last),
    // ... additional Network sink signals

    // Network Network Interface (Source - Transmit)
    .m_network_tdata       (net_tx_data),
    .m_network_tvalid      (net_tx_valid),
    .m_network_tready      (net_tx_ready),
    .m_network_tlast       (net_tx_last),
    // ... additional Network source signals

    // MonBus Output
    .monbus_pkt_valid   (miop_mon_valid),
    .monbus_pkt_ready   (miop_mon_ready),
    .monbus_pkt_data    (miop_mon_data)
);
```

### Pattern 2: Configuration Sequence

```systemverilog
// Recommended initialization sequence
initial begin
    // 1. Assert reset
    aresetn = 0;
    repeat(10) @(posedge aclk);
    aresetn = 1;

    // 2. Configure RAPIDS via AXIL4
    axil_write(ADDR_SINK_SRAM_DEPTH, 1024);
    axil_write(ADDR_SOURCE_SRAM_DEPTH, 1024);
    axil_write(ADDR_TIMEOUT_THRESHOLD, 1000);
    axil_write(ADDR_INITIAL_CREDIT, 4);  // 4 = 16 credits (2^4, exponential encoding)
    axil_write(ADDR_CREDIT_ENABLE, 1);  // ✅ Enable credit mode (now fixed!)

    // 3. Load descriptors
    for (int i = 0; i < num_descriptors; i++) begin
        axil_write(ADDR_DESC_ADDR, descriptor[i].addr);
        axil_write(ADDR_DESC_LEN, descriptor[i].length);
        axil_write(ADDR_DESC_CTRL, descriptor[i].control);
        axil_write(ADDR_DESC_COMMIT, 1);
    end

    // 4. Enable RAPIDS operation
    axil_write(ADDR_ENABLE, 1);
end
```

### Pattern 3: MonBus Integration

```systemverilog
// Always add downstream FIFO for MonBus
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_miop_mon_fifo (
    .i_clk      (aclk),
    .i_rst_n    (aresetn),
    .i_data     (monbus_pkt_data),
    .i_valid    (monbus_pkt_valid),
    .o_ready    (monbus_pkt_ready),
    .o_data     (fifo_mon_data),
    .o_valid    (fifo_mon_valid),
    .i_ready    (consumer_ready)
);
```

---

## Anti-Patterns to Catch

### ❌ Anti-Pattern 1: Not Understanding Exponential Credit Encoding

```systemverilog
❌ WRONG:
.cfg_initial_credit(4'd16),  // Thinks this gives 16 credits - it doesn't!

✅ CORRECTED:
"Credits use exponential encoding:
- cfg_initial_credit = 4 → 16 credits (2^4)
- cfg_initial_credit = 8 → 256 credits (2^8)
- cfg_initial_credit = 15 → ∞ credits (unlimited)
See projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md for encoding table."
```

### ❌ Anti-Pattern 2: Insufficient SRAM Depth

```systemverilog
❌ WRONG:
.SRAM_DEPTH(16)  // Too small for realistic packets

✅ CORRECTED:
"SRAM depth should match typical packet sizes.
Recommended: 1024-4096 entries depending on data width and packet sizes."
```

### ❌ Anti-Pattern 3: No MonBus Downstream Handling

```systemverilog
❌ WRONG:
assign monbus_pkt_ready = 1'b1;  // Always ready = potential packet loss

✅ CORRECTED:
"Connect to FIFO or proper consumer:
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(256)) u_mon_fifo (
    .i_valid(monbus_pkt_valid),
    .i_data(monbus_pkt_data),
    .o_ready(monbus_pkt_ready),
    ...
);"
```

### ❌ Anti-Pattern 4: Testing Individual Blocks in Isolation

```systemverilog
❌ WRONG:
"Only test scheduler without descriptor engine"

✅ CORRECTED:
"RAPIDS blocks are tightly coupled. Always test:
1. FUB tests for basic block functionality
2. Integration tests for block interactions
3. System tests for complete flows"
```

---

## Debugging Workflow

### Issue: Scheduler Not Processing Descriptors

**Check in order:**
1. ✅ Credit configuration correct? (Remember exponential encoding!)
2. ✅ Descriptors loaded via AXIL4?
3. ✅ RAPIDS enabled? (`ADDR_ENABLE = 1`)
4. ✅ Reset properly deasserted?
5. ✅ Descriptor engine FIFO not empty?

**Debug commands:**
```bash
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v -s  # Verbose test
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ --vcd=debug.vcd
gtkwave debug.vcd  # Inspect FSM state transitions
```

### Issue: Data Path Stalls

**Check in order:**
1. ✅ SRAM depth sufficient?
2. ✅ Downstream interfaces ready?
3. ✅ AXI4 backpressure handling?
4. ✅ Network flow control?
5. ✅ Buffer overflow/underflow detection?

**Waveform Analysis:**
- Check SRAM read/write pointers
- Verify AXI4 handshakes
- Inspect Network TREADY signals

### Issue: MonBus Packets Not Generated

**Check in order:**
1. ✅ Operations completing successfully?
2. ✅ MonBus ready signal asserted?
3. ✅ MonBus reporter enabled?
4. ✅ Downstream FIFO not full?

---

## Testing Guidance

### Test Organization

```
projects/components/rapids/dv/tests/
├── fub_tests/                  # Individual block tests
│   ├── scheduler/
│   │   ├── test_scheduler.py   # FSM, credit management
│   │   └── conftest.py
│   ├── descriptor_engine/
│   │   ├── test_desc_engine.py # FIFO, parsing
│   │   └── conftest.py
│   ├── program_engine/
│   ├── network_interfaces/
│   └── simple_sram/
│
├── integration_tests/          # Multi-block scenarios
│   ├── test_scheduler_desc.py  # Scheduler + Descriptor Engine
│   ├── test_sink_path.py       # Complete sink data path
│   └── test_source_path.py     # Complete source data path
│
└── system_tests/               # Full RAPIDS operation
    ├── test_full_dma.py        # Complete DMA transfer
    └── test_bidirectional.py   # Simultaneous sink/source
```

### Running Tests

```bash
# Single block test
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ -v

# All FUB tests
pytest projects/components/rapids/dv/tests/fub_tests/ -v

# Integration tests
pytest projects/components/rapids/dv/tests/integration_tests/ -v

# System tests
pytest projects/components/rapids/dv/tests/system_tests/ -v

# All RAPIDS tests
pytest projects/components/rapids/dv/tests/ -v

# With waveforms
pytest projects/components/rapids/dv/tests/fub_tests/scheduler/ --vcd=waves.vcd
```

### Test Coverage Status

**Current Status:** ~80% functional coverage

| Component | Coverage | Status |
|-----------|----------|--------|
| Scheduler | ~90% | Exponential credit encoding implemented |
| Descriptor Engine | ~80% | Basic tests passing |
| Program Engine | ~85% | Alignment tested |
| Sink Data Path | ~75% | Basic flows working |
| Source Data Path | ~70% | Basic flows working |
| Integration | ~60% | More stress testing needed |

---

## Key Documentation Links

### Always Reference These

**Primary Technical Specification:**
- `projects/components/rapids/docs/rapids_spec/miop_index.md` - Complete specification index
- `projects/components/rapids/docs/rapids_spec/ch01_overview/` - Architecture overview
- `projects/components/rapids/docs/rapids_spec/ch02_blocks/` - Block specifications
- `projects/components/rapids/docs/rapids_spec/ch03_interfaces/` - Interface specifications
- `projects/components/rapids/docs/rapids_spec/ch04_programming_models/` - Programming model
- `projects/components/rapids/docs/rapids_spec/ch05_registers/` - Register definitions

**This Subsystem:**
- `projects/components/rapids/PRD.md` - Requirements overview
- `projects/components/rapids/README.md` - Quick start guide (if exists)
- `projects/components/rapids/TASKS.md` - Current work items
- `projects/components/rapids/known_issues/` - Bug tracking

**Validation:**
- `docs/RAPIDS_Validation_Status_Report.md` - Test results and status

**Root:**
- `/PRD.md` - Master requirements
- `/CLAUDE.md` - Repository guide

---

## Quick Commands

```bash
# View complete specification
cat projects/components/rapids/docs/rapids_spec/miop_index.md
cat projects/components/rapids/docs/rapids_spec/ch02_blocks/01_01_scheduler.md

# Check known issues
ls projects/components/rapids/known_issues/
cat projects/components/rapids/known_issues/scheduler.md

# Run tests
pytest projects/components/rapids/dv/tests/fub_tests/ -v
pytest projects/components/rapids/dv/tests/integration_tests/ -v

# Lint
verilator --lint-only projects/components/rapids/rtl/rapids_fub/scheduler.sv

# Search for modules
find projects/components/rapids/rtl/rapids_fub/ -name "*.sv" -exec grep -H "^module" {} \;
```

---

## Verification Patterns and Best Practices

### Pattern: Continuous Background Monitoring

**Problem:** When testing components that output data asynchronously (descriptors, packets, etc.), tests that only check outputs at specific points will miss data that arrives during other operations.

**Solution:** Use continuous background monitoring coroutines that run throughout the test.

**Example - Descriptor Engine Testing:**

```python
class DescriptorEngineTB(TBBase):
    async def run_apb_only_test(self, num_packets: int, profile: DelayProfile):
        """Test with continuous descriptor monitoring"""
        descriptors_collected = []  # Shared list
        monitor_active = True  # Control flag

        # Background coroutine monitors continuously
        async def descriptor_monitor():
            """Continuously monitor for descriptors throughout the test"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.descriptor_valid.value) == 1:
                    desc_data = int(self.dut.descriptor_packet.value)
                    descriptors_collected.append(desc_data)
                    if len(descriptors_collected) % 5 == 1:
                        self.log.info(f"📦 Descriptor {len(descriptors_collected)}: 0x{desc_data:X}")

        # Start background monitor
        monitor_task = cocotb.start_soon(descriptor_monitor())

        # Send all requests (monitor captures outputs during this phase)
        for i in range(num_packets):
            # Send APB request
            self.dut.apb_valid.value = 1
            self.dut.apb_addr.value = test_addr
            await self.wait_clocks(self.clk_name, 1)
            # ... wait for ready ...
            self.dut.apb_valid.value = 0

        # Wait for final descriptors (monitor still running)
        for cycle in range(final_window):
            await self.wait_clocks(self.clk_name, 1)
            if len(descriptors_collected) >= num_packets:
                break

        # Stop background monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)  # Let monitor finish

        # Verify results
        return len(descriptors_collected) == num_packets
```

**Key Points:**
1. **Shared State:** Use list/dict accessible from both main test and monitor coroutine
2. **Control Flag:** `monitor_active` allows clean shutdown
3. **Background Task:** `cocotb.start_soon()` runs monitor concurrently
4. **Continuous Capture:** Monitor checks every clock cycle, never missing data
5. **Clean Shutdown:** Set flag to False, wait for monitor to finish

**When to Use:**
- ✅ Asynchronous output interfaces (descriptors, packets, responses)
- ✅ Tests with rapid-fire input operations
- ✅ Multi-stage pipelines where outputs don't align with inputs
- ❌ Simple synchronous request-response patterns

**Benefits:**
- 100% capture rate (no missed transactions)
- Decouples input stimulus from output monitoring
- Realistic timing coverage (captures outputs at any point)

**Results:** Descriptor engine tests improved from 42% success (5/12 descriptors) to 100% success (14/14 tests passing) by applying this pattern.

### Pattern: Using Existing CocoTBFramework Components

**Critical Rule:** Always search for existing components before creating new ones.

**Framework Structure:**
```
bin/CocoTBFramework/
├── components/           # Protocol-specific BFMs and drivers
│   ├── axi4/            # Complete AXI4 infrastructure
│   ├── axil4/           # AXI4-Lite components
│   ├── apb/             # APB drivers and monitors
│   ├── axis4/           # AXI-Stream components
│   └── rapids/            # RAPIDS-specific BFMs
├── tbclasses/           # Reusable testbench classes
│   ├── amba/            # AMBA testbenches
│   ├── rapids/            # RAPIDS testbenches
│   └── shared/          # Common utilities (TBBase, etc.)
└── scoreboards/         # Transaction checkers
```

**Decision Tree: Create New BFM vs Use Existing?**

```
Need to model protocol behavior?
├─ Is it a standard protocol (AXI4, APB, AXIS)?
│  └─ YES → Use components/axi4/, components/apb/, etc.
│           ✅ DO NOT create new implementation
│
├─ Is it RAPIDS-specific custom behavior?
│  ├─ Is it >100 lines?
│  │  └─ YES → Extract to components/rapids/
│  └─ Is it <50 lines and test-specific?
│     └─ YES → Keep embedded in testbench
│
└─ Is it generic helper (not protocol-specific)?
   └─ Add to tbclasses/shared/utilities.py
```

**Example - Descriptor Engine AXI Responder:**

```python
# ❌ WRONG: Creating new AXI4 read responder BFM
# File: components/rapids/axi_read_responder_bfm.py
class AXIReadResponderBFM:
    """New AXI4 read responder - DON'T DO THIS!"""
    # ... 200 lines of AXI4 protocol implementation ...

# ✅ CORRECT: Use existing AXI4 components
# File: tbclasses/rapids/descriptor_engine_tb.py
async def axi_read_responder(self):
    """Simple test-specific responder - 50 lines, embedded"""
    while True:
        await self.wait_clocks(self.clk_name, 1)
        if int(self.dut.ar_valid.value) == 1 and int(self.dut.ar_ready.value) == 1:
            # Generate response data
            self.dut.r_valid.value = 1
            self.dut.r_data.value = response_data
            # ... wait for r_ready ...
            self.dut.r_valid.value = 0
```

**Why This Matters:**
- **Existing AXI4 components:** Comprehensive, tested, feature-complete
- **Simple embedded responder:** Test-specific, minimal protocol simulation
- **No duplication:** Framework already has robust AXI4 infrastructure

**BFM Extraction Criteria:**

| Factor | Extract to BFM | Keep Embedded |
|--------|---------------|---------------|
| Lines of code | >100 lines | <50 lines |
| Complexity | Complex protocol logic | Simple stimulus/response |
| Reusability | Used across multiple tests | Test-specific |
| Protocol | Custom RAPIDS-specific | Standard protocol (use framework) |
| Dependencies | Standalone | Tightly coupled to one test |

**Examples:**

**✅ Extracted to BFM:** `DataMoverBFM` (components/rapids/data_mover_bfm.py)
- 150+ lines
- Complex RAPIDS data mover protocol
- Used across scheduler tests
- Reusable for integration tests

**✅ Kept Embedded:** AXI read responder in descriptor engine
- 50 lines
- Simple test-specific behavior
- Framework already has full AXI4 support
- No need for extraction

### Test Scalability Patterns

**Principle:** Tests should scale from basic validation to comprehensive stress testing.

**Pattern: Delay Profiles for Timing Coverage**

```python
class DelayProfile(Enum):
    """Delay profiles for comprehensive timing coverage"""
    FAST_PRODUCER = "fast_producer"      # Producer faster than consumer
    FAST_CONSUMER = "fast_consumer"      # Consumer faster than producer
    FIXED_DELAY = "fixed_delay"          # Predictable timing
    MINIMAL_DELAY = "minimal_delay"      # Stress test - minimal delays
    BACKPRESSURE = "backpressure"        # Heavy backpressure scenarios

# Test method scales with profile
async def run_apb_only_test(self, num_packets: int, profile: DelayProfile):
    """Scalable test with configurable timing"""
    params = self.delay_params[profile]

    for i in range(num_packets):
        # Apply profile-specific delays
        producer_delay = self.get_delay_value(params['producer_delay'])
        await self.wait_clocks(self.clk_name, producer_delay)

        # Send request...

        # Profile-specific backpressure
        if random.random() < params.get('backpressure_freq', 0.1):
            backpressure_cycles = random.randint(5, 25)
            await self.wait_clocks(self.clk_name, backpressure_cycles)
```

**Pattern: Hierarchical Test Levels**

```python
# Test runner with multiple levels
@pytest.mark.parametrize("test_level", ["basic", "medium", "full"])
def test_descriptor_engine(test_level, ...):
    """Hierarchical test levels for different coverage needs"""

    if test_level == "basic":
        # Quick validation: 10 packets, simple timing
        num_packets = 10
        test_class = TestClass.APB_ONLY

    elif test_level == "medium":
        # Moderate coverage: 3 packets × 4 profiles
        num_packets = 3
        test_classes = [TestClass.APB_ONLY, TestClass.RDA_ONLY, TestClass.MIXED]

    elif test_level == "full":
        # Comprehensive: 5 packets × all profiles × all test classes
        num_packets = 5
        test_classes = [TestClass.APB_ONLY, TestClass.RDA_ONLY, TestClass.MIXED]
```

**Benefits:**
- **Basic:** Quick smoke tests (CI/CD)
- **Medium:** Developer validation
- **Full:** Comprehensive regression

**Pattern: Parametrized Test Generation**

```python
def generate_test_params():
    """Generate comprehensive parameter combinations"""
    params = []

    # Basic configurations
    for num_channels in [8, 32, 64]:
        for data_width in [64, 512]:
            for addr_width in [32, 64]:
                params.append((num_channels, data_width, addr_width))

    return params

# Pytest automatically runs all combinations
@pytest.mark.parametrize("num_channels, data_width, addr_width", generate_test_params())
def test_scheduler(num_channels, data_width, addr_width):
    """Test scales across all parameter combinations"""
    # ...
```

**Test Success Criteria:**

**⚠️ CRITICAL:** All tests must achieve 100% success rate.

```python
# ❌ WRONG: Accepting partial success
success_rate = (descriptors_received / total_sent) * 100
return success_rate >= 70  # "Mostly good" - NOT ACCEPTABLE

# ✅ CORRECT: Require 100% success
success_rate = (descriptors_received / total_sent) * 100
return success_rate >= 100  # Must receive ALL expected outputs
```

**Why 100% Required:**
- Partial success indicates bugs, not acceptable tolerance
- RTL should be deterministic - 100% success is achievable
- Lower thresholds mask real issues

---

## Documentation Generation

### Generating PDF/DOCX from Specification

**Tool:** `/mnt/data/github/rtldesignsherpa/bin/md_to_docx.py`

Use this tool to convert the linked specification index into a single all-inclusive PDF or DOCX file.

**Basic Usage:**

```bash
# Generate DOCX from rapids_spec index
python bin/md_to_docx.py \
    projects/components/rapids/docs/rapids_spec/rapids_index.md \
    -o projects/components/rapids/docs/RAPIDS_Specification_v0.25.docx \
    --toc \
    --title-page

# Generate both DOCX and PDF
python bin/md_to_docx.py \
    projects/components/rapids/docs/rapids_spec/rapids_index.md \
    -o projects/components/rapids/docs/RAPIDS_Specification_v0.25.docx \
    --toc \
    --title-page \
    --pdf

# With custom template (optional)
python bin/md_to_docx.py \
    projects/components/rapids/docs/rapids_spec/rapids_index.md \
    -o projects/components/rapids/docs/RAPIDS_Specification_v0.25.docx \
    -t path/to/template.dotx \
    --toc \
    --title-page \
    --pdf
```

**Key Features:**
- **Recursive Collection:** Follows all markdown links in the index file
- **Heading Demotion:** Automatically adjusts heading levels for included files
- **Table of Contents:** `--toc` flag generates automatic ToC
- **Title Page:** `--title-page` flag creates title page from first heading
- **PDF Export:** `--pdf` flag generates both DOCX and PDF
- **Image Support:** Resolves images relative to source directory
- **Template Support:** Optional custom DOCX/DOTX template via `-t` flag

**Common Workflow:**

```bash
# 1. Update version number in index file (rapids_index.md)
# 2. Generate documentation
cd /mnt/data/github/rtldesignsherpa
python bin/md_to_docx.py \
    projects/components/rapids/docs/rapids_spec/rapids_index.md \
    -o projects/components/rapids/docs/RAPIDS_Specification_v0.25.docx \
    --toc --title-page --pdf

# 3. Output files created:
#    - RAPIDS_Specification_v0.25.docx
#    - RAPIDS_Specification_v0.25.pdf (if --pdf used)
```

**Debug Mode:**

```bash
# Generate debug markdown to see combined output
python bin/md_to_docx.py \
    projects/components/rapids/docs/rapids_spec/rapids_index.md \
    -o output.docx \
    --debug-md

# This creates debug.md showing the complete merged content
```

**Tool Requirements:**
- Python 3.6+
- Pandoc installed and in PATH
- For PDF generation: LaTeX (e.g., texlive) or use Pandoc's built-in PDF writer

**📖 See:** `/mnt/data/github/rtldesignsherpa/bin/md_to_docx.py` for complete implementation details

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/rapids/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/rapids/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the rapids_spec index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## Remember

1. 🎛️ **MANDATORY: Use BFMs** - GAXI Master/Slave for custom valid/ready, protocol-specific BFMs for AXI4/APB/AXIS/Network
2. 📖 **Link to detailed spec** - `projects/components/rapids/docs/rapids_spec/` has complete architecture docs
3. 🔢 **Exponential credit encoding** - Remember: 0→1, 1→2, 2→4, not linear!
4. 🐛 **Check known issues** - Before diagnosing bugs
5. 🔗 **Block interactions** - RAPIDS blocks are tightly coupled
6. 🧪 **Multi-layered testing** - FUB → Integration → System tests
7. 🏗️ **Testbench reuse** - Always create TB classes in `bin/CocoTBFramework/tbclasses/rapids/`
8. 🎯 **Continuous monitoring** - Use background coroutines for asynchronous output capture
9. 🔍 **Search first** - Use existing CocoTBFramework components before creating new ones
10. 📊 **100% success** - All tests must achieve 100% success rate, no exceptions
11. 🏛️ **Three-layer architecture** - TB (infrastructure) + Test (intelligence) + Scoreboard (verification)
12. 🎪 **Queue-based verification** - Use `monitor._recvQ.popleft()` for simple tests, not memory models

---

**Version:** 1.2
**Last Updated:** 2025-10-14
**Maintained By:** RTL Design Sherpa Project
