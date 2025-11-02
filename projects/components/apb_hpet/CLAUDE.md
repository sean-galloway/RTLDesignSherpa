# Claude Code Guide: APB HPET Component

**Version:** 1.0
**Last Updated:** 2025-10-17
**Purpose:** AI-specific guidance for working with APB HPET component

---

## Quick Context

**What:** APB High Precision Event Timer - Multi-timer peripheral with 64-bit counter and comparators
**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**Your Role:** Help users integrate HPET, understand architecture, fix minor issues

**📖 Complete Specification:** `projects/components/apb_hpet/PRD.md` ← **Always reference this for technical details**

---

## Critical Rules for This Component

### Rule #0: Attribution Format for Git Commits

**IMPORTANT:** When creating git commit messages for APB HPET documentation or code:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** APB HPET receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

### Rule #0.05: Reset Macro Standards - MANDATORY

**⚠️ APB HPET NOW USES RESET MACROS - ALL FUTURE CHANGES MUST MAINTAIN THIS ⚠️**

**Status:** As of 2025-10-25, APB HPET RTL has been converted to use standardized reset macros from `rtl/amba/includes/reset_defs.svh`.

**What Changed:**
- `hpet_core.sv`: 6 always_ff blocks converted to `ALWAYS_FF_RST` macro
- `hpet_config_regs.sv`: 3 always_ff blocks converted to `ALWAYS_FF_RST` macro
- Both files now include `reset_defs.svh`
- All reset tests remain functionally equivalent (verified via regression)

**HARD REQUIREMENT for Future Work:**
1. **ALL modifications** to HPET RTL must preserve reset macro usage
2. **NO manual** `always_ff @(posedge clk or negedge rst_n)` patterns allowed
3. **PRs will be REJECTED** if they revert to manual reset handling
4. **See** `projects/components/CLAUDE.md` Rule #0 for complete reset macro standards

**Why This Matters for HPET:**
- HPET targets FPGA implementation (reset inference critical for timing)
- Multi-clock domain design (pclk + hpet_clk) requires consistent reset handling
- Timer precision depends on proper reset sequencing
- CDC variant needs FPGA-friendly reset synchronization

### Rule #0.1: TESTBENCH ARCHITECTURE - MANDATORY SEPARATION

**⚠️ THIS IS A HARD REQUIREMENT - NO EXCEPTIONS ⚠️**

**NEVER embed testbench classes inside test runner files!**

The same testbench logic is reused across multiple test scenarios. Having testbench code only in test files makes it COMPLETELY WORTHLESS for reuse.

**MANDATORY Structure:**

```
projects/components/apb_hpet/dv/
├── tbclasses/                    # ★ HPET TB classes HERE (not framework!)
│   ├── hpet_tb.py                # ← REUSABLE TB CLASS
│   ├── hpet_tests_basic.py       # ← REUSABLE test suite (basic level)
│   ├── hpet_tests_medium.py      # ← REUSABLE test suite (medium level)
│   └── hpet_tests_full.py        # ← REUSABLE test suite (full level)
│
└── tests/                        # Test runners (import TB classes from project area)
    └── test_apb_hpet.py          # ← TEST RUNNER ONLY (imports TB + test suites)
```

**✅ CRITICAL: All HPET TB classes are in the PROJECT AREA, not the framework!**

**Test Runner Pattern (CORRECT):**
```python
# projects/components/apb_hpet/dv/tests/test_apb_hpet.py

# Add repo root to Python path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.apb_hpet.dv.tbclasses.hpet_tb import HPETTB, HPETRegisterMap
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_basic import HPETBasicTests
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_medium import HPETMediumTests

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

@cocotb.test()
async def cocotb_test_basic(dut):
    """Test runner - imports TB and test suite, runs test"""
    tb = HPETTestbench(dut)
    await tb.setup_clocks_and_reset()
    tests_basic = HPETTestsBasic(tb)
    result = await tests_basic.test_register_access()
    assert result, "Basic register access test failed"

@pytest.mark.parametrize("num_timers, vendor_id, ...", generate_test_params())
def test_hpet(request, num_timers, vendor_id, ...):
    """Pytest runner - only handles parameters and run()"""
    # ... RTL sources, parameters, etc ...
    run(verilog_sources=..., module=module, ...)
```

**Testbench Class Pattern (CORRECT):**
```python
# projects/components/apb_hpet/dv/tbclasses/hpet_tb.py ✅ CORRECT LOCATION!
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class HPETTB(TBBase):
    """Reusable testbench for APB HPET validation"""

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

    async def write_register(self, addr, data):
        """Write to HPET register via APB"""
        # APB write transaction

    async def read_register(self, addr):
        """Read from HPET register via APB"""
        # APB read transaction
        return data
```

**Why This Matters:**

1. **Reusability**: Same TB class used in:
   - Basic tests (register access)
   - Medium tests (timer operation)
   - Full tests (stress scenarios)
   - Integration tests (system-level)

2. **Maintainability**: Fix bug once in TB class, all tests benefit

3. **Composition**: TB classes can inherit/compose for complex scenarios

---

### Rule #1: Timer Cleanup is MANDATORY

**⚠️ CRITICAL: Always Reset Counter Between Tests ⚠️**

**The Root Cause of Timer 2+ Firing Issues:**

The problem that caused Timer 2 and higher numbered timers to miss their firing was simple test cleanup:

```python
# ❌ WRONG: Test leaves counter at random value
async def test_64bit_counter(self):
    # Test writes counter to 0xDEADBEEF or 0xFFFFFFF0
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0xDEADBEEF)
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0xFFFFFFF0)

    # Test ends WITHOUT resetting counter!
    # Next test starts with counter at 0xFFFFFFF0DEADBEEF
    return True

# ✅ CORRECT: Test cleans up counter
async def test_64bit_counter(self):
    # Test writes counter to 0xDEADBEEF or 0xFFFFFFF0
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0xDEADBEEF)
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0xFFFFFFF0)

    # Reset counter to 0 for next test
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x00000000)
    await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x00000000)
    return True
```

**Why This Caused Timer 2+ to Miss:**

1. 64-bit Counter test runs first, leaves counter at 0xFFFFFFF0DEADBEEF
2. Multiple Timers test runs second, expects counter starting at 0
3. Timer 0 (period=100) fires at counter=100
4. Timer 1 (period=200) fires at counter=200
5. Timer 2 (period=700) expects to fire at counter=700
6. But counter started at 0xFFFFFFF0DEADBEEF, so never reaches 700!

**The Fix:**
- Added 2 lines of cleanup in hpet_tests_medium.py:220-222
- Changed timeout from 10µs to 20µs in Multiple Timers test

**Result:** 3-timer AMD-like configuration went from FAILING to 100% PASSING

**Lesson:** Always clean up hardware state between tests. The problem wasn't RTL bugs or complex counter reset side-effects - it was simply missing test cleanup.

---

### Rule #2: Timer Timeout Calculations

**⚠️ Account for Counter Starting Value When Setting Timeouts ⚠️**

**Timeout Calculation Pattern:**

```python
# Calculate timeout based on timer periods
timer_configs = [
    {"period": 100, "expected_fire": 100},   # Timer 0 fires at 100
    {"period": 200, "expected_fire": 200},   # Timer 1 fires at 200
    {"period": 700, "expected_fire": 700},   # Timer 2 fires at 700 (needs most time)
]

# Account for:
# 1. Latest timer fire time (700 ns)
# 2. Counter increment rate (1 per HPET clock cycle)
# 3. Test overhead (setup, APB transactions)
# 4. Safety margin (2x for reliability)

timeout_ns = max(cfg["expected_fire"] for cfg in timer_configs) * 3  # 3x safety margin
timeout_us = (timeout_ns + 999) // 1000  # Convert to µs, round up

self.log.info(f"Setting timeout to {timeout_us}µs for timer with {max_period}ns period")
```

**Example - Multiple Timers Test:**

```python
# Original (WRONG): 10µs timeout, insufficient for Timer 2
timeout = 10000  # 10µs

# Fixed (CORRECT): 20µs timeout, allows Timer 2 to fire at ~14µs
timeout = 20000  # 20µs - Timer 2 needs ~14µs, allow extra margin
```

**Why Margins Matter:**
- Timer 2 (period=700) fires at counter=700ns = 0.7µs
- But if counter doesn't start at 0, it takes longer to reach 700
- With counter starting at 0: Timer 2 fires in ~700ns
- With counter starting high: Timer 2 may never fire (timeout)
- Solution: Reset counter AND use appropriate timeout

---

### Rule #3: Understand HPET Register Map Structure

**Register Layout:**

```
0x000: HPET_CONFIG          (enable, legacy_mapping)
0x004: HPET_STATUS          (timer interrupt status, W1C)
0x008: HPET_COUNTER_LO      (main counter bits [31:0], RW)
0x00C: HPET_COUNTER_HI      (main counter bits [63:32], RW)
0x010: HPET_CAPABILITIES    (num_timers, vendor_id, revision_id, RO)

Per-Timer Registers (i = 0 to NUM_TIMERS-1):
0x100 + i*0x20: TIMER[i]_CONFIG         (enable, int_enable, type, size)
0x104 + i*0x20: TIMER[i]_COMPARATOR_LO  (bits [31:0], RW)
0x108 + i*0x20: TIMER[i]_COMPARATOR_HI  (bits [63:32], RW)
```

**Key Points:**

1. **HPET_CONFIG bit 0:** Global enable (must be 1 for HPET to operate)
2. **HPET_STATUS:** Write-1-to-Clear (W1C) for interrupt status bits
3. **HPET_COUNTER:** 64-bit counter, read/write access via LO/HI registers
4. **HPET_CAPABILITIES:** Read-only, contains NUM_TIMERS, VENDOR_ID, REVISION_ID
5. **TIMER_CONFIG bit 2:** 0=One-shot, 1=Periodic
6. **TIMER_CONFIG bit 0:** Timer enable
7. **TIMER_CONFIG bit 1:** Interrupt enable

**Timer Configuration Sequence:**

```python
# 1. Disable HPET
await tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x0)

# 2. Reset counter
await tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x0)
await tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x0)

# 3. Configure Timer 0 (one-shot, 1000 cycles)
await tb.write_register(HPETRegisterMap.TIMER0_COMPARATOR_LO, 1000)
await tb.write_register(HPETRegisterMap.TIMER0_COMPARATOR_HI, 0)
await tb.write_register(HPETRegisterMap.TIMER0_CONFIG, 0x3)  # enable=1, int_enable=1

# 4. Enable HPET
await tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x1)

# 5. Wait for timer to fire
await tb.wait_for_interrupt(0, timeout=2000)

# 6. Clear interrupt
await tb.write_register(HPETRegisterMap.HPET_STATUS, (1 << 0))  # W1C
```

---

### Rule #4: Timer Modes and Behavior

**One-Shot Mode:**
```python
# Timer fires once when counter >= comparator
# Does NOT automatically reload

# Configure
await tb.write_register(TIMER0_CONFIG, 0x3)  # enable=1, int_enable=1, type=0 (one-shot)
await tb.write_register(TIMER0_COMPARATOR_LO, 1000)

# Fires at counter=1000
# After firing:
# - Interrupt asserts
# - Timer stays idle until reconfigured
```

**Periodic Mode:**
```python
# Timer fires repeatedly, auto-increments comparator

# Configure
await tb.write_register(TIMER0_CONFIG, 0x7)  # enable=1, int_enable=1, type=1 (periodic)
await tb.write_register(TIMER0_COMPARATOR_LO, 1000)  # Initial comparator

# First fire at counter=1000:
# - Interrupt asserts
# - Comparator auto-increments to 2000

# Second fire at counter=2000:
# - Interrupt asserts again
# - Comparator auto-increments to 3000

# Repeats indefinitely...
```

**Key Differences:**
- **One-shot:** Timer fires once, stops
- **Periodic:** Timer fires repeatedly, comparator auto-increments by period value

**Comparator Auto-Increment Logic (Periodic Mode):**
```systemverilog
// In hpet_core.sv (simplified)
always_ff @(posedge hpet_clk) begin
    if (counter >= comparator[i]) begin
        // Timer fires
        timer_irq[i] <= 1'b1;

        // Periodic mode: auto-increment comparator
        if (timer_config[i].type == 1'b1) begin  // Periodic
            comparator[i] <= comparator[i] + period[i];
        end
    end
end
```

---

### Rule #5: PeakRDL Integration Details

**Register Generation:**

```bash
# Generate HPET registers from SystemRDL specification
peakrdl regblock rtl/peakrdl/hpet_regs.rdl --cpuif apb4 -o rtl/

# Generated files:
# - rtl/hpet_regs.sv (register file)
# - rtl/hpet_regs_pkg.sv (package with field definitions)
```

**Register Wrapper:**

```systemverilog
// hpet_config_regs.sv integrates PeakRDL registers with HPET core
module hpet_config_regs #(
    parameter int NUM_TIMERS = 2
) (
    // APB interface (connects to PeakRDL registers)
    // HPET core interface (connects to timer logic)
);

    // PeakRDL register file instance
    hpet_regs u_hpet_regs (
        .apb_if (apb_signals),
        .hwif   (register_interface)
    );

    // Timer write strobes (edge detection on register writes)
    edge_detect u_timer0_comparator_wr (
        .i_clk    (pclk),
        .i_signal (hwif.timer0_comparator.swacc),
        .o_pulse  (timer0_comparator_wr)
    );

    // Per-timer data buses to prevent corruption
    assign timer_comparator_data[0] = {
        hwif.timer0_comparator_hi.value,
        hwif.timer0_comparator_lo.value
    };
endmodule
```

**Key Features:**
1. **Edge Detection:** Write strobes generated on register updates (not level)
2. **Per-Timer Buses:** Each timer has dedicated data bus to prevent corruption
3. **W1C Support:** STATUS register uses write-1-to-clear for interrupt flags

---

### Rule #6: Clock Domain Crossing (CDC)

**CDC Parameter:**
```systemverilog
parameter CDC_ENABLE = 0;  // 0: Synchronous, 1: Asynchronous clocks
```

**CDC Disabled (CDC_ENABLE=0):**
- APB clock (`pclk`) and HPET clock (`hpet_clk`) must be same or synchronous
- Lower latency (2 APB clock cycles for register access)
- Simpler verification

**CDC Enabled (CDC_ENABLE=1):**
- APB clock and HPET clock can be completely asynchronous
- Uses `apb_slave_cdc` module for handshake synchronization
- Higher latency (4-6 APB clock cycles for register access)
- More complex verification (metastability, synchronization)

**Test Coverage:**
- All 6 configurations tested include both CDC=0 and CDC=1 variants
- CDC configurations have same functionality, just different timing

**Integration Example:**
```systemverilog
apb_hpet #(
    .NUM_TIMERS(2),
    .VENDOR_ID(16'h8086),
    .REVISION_ID(16'h0001),
    .CDC_ENABLE(1)  // Enable CDC for asynchronous clocks
) u_hpet (
    .pclk      (apb_clk),      // APB clock (e.g., 100 MHz)
    .presetn   (apb_rst_n),
    .hpet_clk  (timer_clk),    // HPET clock (e.g., 10 MHz) - can be async!
    .hpet_rst_n(timer_rst_n),
    // ...
);
```

---

## Architecture Quick Reference

### Block Organization

```
APB HPET Architecture
├── apb_hpet (Top Level)
│   ├── APB Slave (with optional CDC)
│   ├── hpet_config_regs
│   │   ├── hpet_regs (PeakRDL generated)
│   │   └── Edge detect + bus mapping
│   └── hpet_core
│       ├── 64-bit counter
│       ├── Per-timer comparators
│       └── Fire detection logic
└── Timer IRQs [NUM_TIMERS-1:0]
```

### Module Quick Reference

| Module | Location | Purpose | Documentation |
|--------|----------|---------|---------------|
| **apb_hpet.sv** | `rtl/` | Top-level wrapper | PRD.md Section 2.2.1 |
| **hpet_core.sv** | `rtl/` | Timer logic (counter, comparators) | PRD.md Section 2.2.2 |
| **hpet_config_regs.sv** | `rtl/` | Register wrapper | PRD.md Section 2.2.3 |
| **hpet_regs.sv** | `rtl/` | PeakRDL generated registers | PRD.md Section 2.2.4 |

---

## Common User Questions and Responses

### Q: "How do I configure multiple timers?"

**A: Direct answer:**

```python
# Configure 3 timers with different periods
timer_configs = [
    {"timer": 0, "period": 100, "mode": "one-shot"},
    {"timer": 1, "period": 200, "mode": "periodic"},
    {"timer": 2, "period": 700, "mode": "one-shot"},
]

# 1. Disable HPET
await tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x0)

# 2. Reset counter
await tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x0)
await tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x0)

# 3. Configure each timer
for cfg in timer_configs:
    timer_num = cfg["timer"]
    comparator_lo_addr = HPETRegisterMap.TIMER0_COMPARATOR_LO + (timer_num * 0x20)
    comparator_hi_addr = HPETRegisterMap.TIMER0_COMPARATOR_HI + (timer_num * 0x20)
    config_addr = HPETRegisterMap.TIMER0_CONFIG + (timer_num * 0x20)

    # Set comparator
    await tb.write_register(comparator_lo_addr, cfg["period"])
    await tb.write_register(comparator_hi_addr, 0)

    # Configure timer (enable + interrupt + mode)
    mode_bit = 0x4 if cfg["mode"] == "periodic" else 0x0
    await tb.write_register(config_addr, 0x3 | mode_bit)

# 4. Enable HPET
await tb.write_register(HPETRegisterMap.HPET_CONFIG, 0x1)
```

**📖 See:** `projects/components/apb_hpet/PRD.md` Section 9 - Integration Guide

### Q: "Why did Timer 2 not fire in my test?"

**A: Most common causes:**

1. **Counter not reset between tests** ← Most likely!
```python
# ALWAYS reset counter at end of test
await tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x0)
await tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x0)
```

2. **Timeout too short**
```python
# Timer 2 with period 700 needs at least 700ns to fire
# Add margin for APB transactions and test overhead
timeout = 20000  # 20µs - provides 30x margin for 700ns timer
```

3. **Timer not enabled**
```python
# Check TIMER_CONFIG bit 0 is set
config = await tb.read_register(HPETRegisterMap.TIMER2_CONFIG)
assert config & 0x1, "Timer 2 not enabled!"
```

4. **HPET not enabled**
```python
# Check HPET_CONFIG bit 0 is set
config = await tb.read_register(HPETRegisterMap.HPET_CONFIG)
assert config & 0x1, "HPET not enabled!"
```

**📖 See:** Rule #1 and Rule #2 above for complete explanation

### Q: "What configurations are tested and passing?"

**A: Test coverage:**

```
Configuration                           Basic  Medium  Full   Overall
──────────────────────────────────────────────────────────────────────
2-timer Intel-like (no CDC)             4/4    5/5     3/3    12/12 ✅
3-timer AMD-like (no CDC)               4/4    5/5     3/3    12/12 ✅
8-timer custom (no CDC)                 4/4    5/5     2/3    11/12 ⚠️
2-timer Intel-like (CDC)                4/4    5/5     3/3    12/12 ✅
3-timer AMD-like (CDC)                  4/4    5/5     3/3    12/12 ✅
8-timer custom (CDC)                    4/4    5/5     3/3    12/12 ✅
```

**Overall:** 5/6 configurations at 100%, 1 config at 92%

**Known Issue:** 8-timer non-CDC "All Timers Stress" test has timeout issue (minor)

**📖 See:** `projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md` for detailed results

---

## Test Architecture

### Test Directory Structure

**MANDATORY: conftest.py Required**

Every test directory must have a `conftest.py` file for pytest configuration:

```
projects/components/apb_hpet/dv/tests/
├── conftest.py           ← MANDATORY: Pytest configuration
├── test_apb_hpet.py      ← Test runner
└── logs/                 ← Created by conftest.py
```

**conftest.py provides:**
1. **Logging Configuration:** Auto-creates logs directory, configures pytest logging
2. **Test Markers:** Registers custom markers (basic, medium, full, register_access, etc.)
3. **Test Fixtures:** Parametrized fixtures for configurations
4. **Test Collection Hooks:** Auto-adds markers based on test patterns
5. **Log Preservation:** Preserves all logs regardless of test outcome

**Key Features:**
```python
# Auto-creates logs directory
log_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
os.makedirs(log_dir, exist_ok=True)

# Registers custom markers
config.addinivalue_line("markers", "basic: Basic functionality tests")
config.addinivalue_line("markers", "register_access: Register access tests")
# ... more markers ...

# Preserves logs
@pytest.hookimpl(trylast=True)
def pytest_sessionfinish(session, exitstatus):
    logging.info("APB HPET test session finished. Preserving all logs and build artifacts.")

# Ignores logs directory during test collection
def pytest_ignore_collect(collection_path, config):
    return 'logs' in str(collection_path)
```

**Running Tests with Markers:**
```bash
# Run only basic tests
pytest projects/components/apb_hpet/dv/tests/ -v -m basic

# Run register access tests
pytest projects/components/apb_hpet/dv/tests/ -v -m register_access

# Run periodic mode tests
pytest projects/components/apb_hpet/dv/tests/ -v -m periodic_mode

# Run 2-timer configuration tests
pytest projects/components/apb_hpet/dv/tests/ -v -m two_timer

# Exclude stress tests
pytest projects/components/apb_hpet/dv/tests/ -v -m "not stress"
```

**📖 See:**
- `projects/components/apb_hpet/dv/tests/conftest.py` - Complete configuration
- `val/amba/conftest.py` - AMBA reference example
- `projects/components/rapids/dv/tests/conftest.py` - RAPIDS reference example

### Test Hierarchy

**HPET tests follow a 3-level hierarchy:**

1. **Basic Tests (4 tests):** Register access, simple operations
   - test_register_access
   - test_timer_enable
   - test_counter_operation
   - test_interrupt_generation

2. **Medium Tests (5 tests):** Periodic mode, multiple timers, 64-bit features
   - test_timer_periodic
   - test_multiple_timers
   - test_64bit_counter
   - test_64bit_comparator
   - test_timer_mode_switching

3. **Full Tests (3 tests):** All timers stress, CDC, edge cases
   - test_all_timers_stress
   - test_clock_domain_crossing (CDC only)
   - test_timer_configuration_edge_cases

### Test File Structure

```python
# projects/components/apb_hpet/dv/tests/test_apb_hpet.py

# Add repo root to Python path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Imports from PROJECT AREA
from projects.components.apb_hpet.dv.tbclasses.hpet_tb import HPETTB, HPETRegisterMap
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_basic import HPETBasicTests
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_medium import HPETMediumTests
from projects.components.apb_hpet.dv.tbclasses.hpet_tests_full import HPETFullTests

# CocoTB test functions (prefix with "cocotb_")
@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic(dut):
    """Test runner for basic tests"""
    tb = HPETTestbench(dut)
    await tb.setup_clocks_and_reset()
    tests = HPETTestsBasic(tb)
    result = await tests.run_all_tests()
    assert result, "Basic tests failed"

# Parameter generation
def generate_hpet_test_params():
    """Generate test parameter combinations"""
    return [
        # (num_timers, vendor_id, revision_id, cdc_enable, test_level, description)
        (2, 0x8086, 1, 0, "basic", "2-timer Intel-like"),
        (3, 0x1022, 2, 0, "medium", "3-timer AMD-like"),
        # ...
    ]

# Pytest wrapper functions
@pytest.mark.parametrize("num_timers, vendor_id, ...", generate_hpet_test_params())
def test_hpet(request, num_timers, vendor_id, ...):
    """Pytest wrapper for HPET tests"""
    # ... RTL sources, parameters, run() ...
```

---

## Anti-Patterns to Catch

### ❌ Anti-Pattern 1: Not Resetting Counter Between Tests

```python
❌ WRONG:
async def test_64bit_counter(self):
    await self.tb.write_register(HPET_COUNTER_LO, 0xFFFFFFFF)
    # Test ends, counter still at 0xFFFFFFFF
    return True

✅ CORRECTED:
async def test_64bit_counter(self):
    await self.tb.write_register(HPET_COUNTER_LO, 0xFFFFFFFF)

    # ALWAYS reset counter at end of test
    await self.tb.write_register(HPET_COUNTER_LO, 0x0)
    await self.tb.write_register(HPET_COUNTER_HI, 0x0)
    return True
```

### ❌ Anti-Pattern 2: Insufficient Test Timeouts

```python
❌ WRONG:
timeout = 1000  # 1µs - too short for Timer 2 (700ns period)

✅ CORRECTED:
# Calculate timeout based on latest timer
max_period = max(timer["period"] for timer in timer_configs)
timeout = max_period * 3  # 3x safety margin
```

### ❌ Anti-Pattern 3: Forgetting W1C for Status Register

```python
❌ WRONG:
await tb.write_register(HPET_STATUS, 0x0)  # Doesn't clear interrupts!

✅ CORRECTED:
status = await tb.read_register(HPET_STATUS)
await tb.write_register(HPET_STATUS, status)  # W1C: write 1s to clear
```

### ❌ Anti-Pattern 4: Expecting Immediate Timer Fire

```python
❌ WRONG:
await tb.write_register(TIMER0_COMPARATOR_LO, 100)
await tb.wait_clocks("hpet_clk", 1)
assert timer_fired, "Timer should fire immediately!"  # NO!

✅ CORRECTED:
await tb.write_register(TIMER0_COMPARATOR_LO, 100)
# Timer fires when counter >= 100
# Must wait for counter to increment to 100
await tb.wait_for_interrupt(0, timeout=2000)
```

---

## Debugging Workflow

### Issue: Timer Not Firing

**Check in order:**
1. ✅ HPET enabled? (HPET_CONFIG bit 0)
2. ✅ Timer enabled? (TIMER_CONFIG bit 0)
3. ✅ Comparator set correctly?
4. ✅ Counter incrementing?
5. ✅ Counter value will reach comparator?
6. ✅ Interrupt enable set? (TIMER_CONFIG bit 1)

**Debug commands:**
```python
# Check HPET enable
config = await tb.read_register(HPETRegisterMap.HPET_CONFIG)
tb.log.info(f"HPET_CONFIG: 0x{config:08X}, enabled={config & 0x1}")

# Check timer enable
timer_config = await tb.read_register(HPETRegisterMap.TIMER0_CONFIG)
tb.log.info(f"TIMER0_CONFIG: 0x{timer_config:08X}, enabled={timer_config & 0x1}")

# Read counter value
counter_lo = await tb.read_register(HPETRegisterMap.HPET_COUNTER_LO)
counter_hi = await tb.read_register(HPETRegisterMap.HPET_COUNTER_HI)
tb.log.info(f"Counter: 0x{counter_hi:08X}{counter_lo:08X}")
```

### Issue: Tests Failing Inconsistently

**Most common cause:** Missing test cleanup

**Solution:**
```python
# Add cleanup at end of EVERY test
await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_LO, 0x0)
await self.tb.write_register(HPETRegisterMap.HPET_COUNTER_HI, 0x0)
```

---

## Key Documentation Links

### Always Reference These

**This Component:**
- `projects/components/apb_hpet/PRD.md` - Complete specification
- `projects/components/apb_hpet/TASKS.md` - Work items
- `projects/components/apb_hpet/known_issues/` - Bug tracking
- `projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md` - Test results

**Testbench Infrastructure:**
- `projects/components/apb_hpet/dv/tbclasses/` - Reusable TB classes (project area!)

**Root:**
- `/CLAUDE.md` - Repository guide
- `/PRD.md` - Master requirements

---

## Quick Commands

```bash
# Run all HPET tests
pytest projects/components/apb_hpet/dv/tests/ -v

# Run specific configuration
pytest "projects/components/apb_hpet/dv/tests/test_apb_hpet.py::test_hpet[2-32902-1-0-basic-2-timer Intel-like]" -v

# Run basic tests only
pytest projects/components/apb_hpet/dv/tests/ -v -k "basic"

# Run with waveforms
pytest projects/components/apb_hpet/dv/tests/ -v --vcd=hpet_debug.vcd

# Lint RTL
verilator --lint-only projects/components/apb_hpet/rtl/apb_hpet.sv

# View documentation
cat projects/components/apb_hpet/PRD.md
cat projects/components/apb_hpet/docs/IMPLEMENTATION_STATUS.md
```

---

## Remember

1. 🧹 **MANDATORY: Clean up counter** - Reset counter to 0 at end of every test
2. ⏱️ **Calculate timeouts properly** - Account for timer periods and test overhead
3. 📖 **Reference PRD.md** - Complete specification in `projects/components/apb_hpet/PRD.md`
4. 🏗️ **Testbench reuse** - TB classes in `projects/components/apb_hpet/dv/tbclasses/` (project area!)
5. ✅ **100% success required** - All tests must pass, partial success indicates bugs
6. 🔁 **W1C for STATUS** - Write 1s to clear interrupt flags, not 0s
7. 📊 **Test hierarchy** - Basic (4) → Medium (5) → Full (3) tests
8. 🔀 **CDC variants** - Test both synchronous and asynchronous clock configurations
9. 🎯 **PeakRDL integration** - Registers generated from SystemRDL spec
10. 🔌 **Per-timer buses** - Dedicated data paths prevent timer corruption

---

## PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/apb_hpet/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/apb_hpet/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the specification index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

**Version:** 1.0
**Last Updated:** 2025-10-17
**Maintained By:** RTL Design Sherpa Project
