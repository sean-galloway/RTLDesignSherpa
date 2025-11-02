# RTL Design Sherpa Testing Guide

**Version:** 1.0
**Last Updated:** 2025-10-26
**Purpose:** Comprehensive testing guide for RTL and verification

---

## Table of Contents

1. [Test Environment Variables](#test-environment-variables)
2. [VCD Waveform Generation](#vcd-waveform-generation)
3. [Test Levels (REG_LEVEL)](#test-levels-reg_level)
4. [Running Tests](#running-tests)
5. [Test Structure](#test-structure)
6. [Writing New Tests](#writing-new-tests)

---

## Test Environment Variables

All tests in this repository support consistent environment variables for controlling test behavior.

### WAVES - VCD Waveform Generation

**Purpose:** Enable VCD waveform generation for debugging

**Usage:**
```bash
# Enable VCD waveforms for specific test
WAVES=1 pytest val/amba/test_axi4_master_rd.py -v

# Enable VCD for all tests in directory
WAVES=1 pytest val/amba/ -v

# Disable VCD (default)
pytest val/amba/test_axi4_master_rd.py -v
```

**Waveform Location:**
- VCD files are generated in the test's `sim_build/` directory
- File naming: `dump.vcd` or `<module_name>.vcd`
- View with: `gtkwave sim_build/dump.vcd`

**Performance Impact:**
- VCD generation adds ~20-50% to test runtime
- VCD files can be large (10MB - 1GB depending on test duration)
- **Recommendation:** Only enable WAVES=1 when debugging specific failures

### REG_LEVEL - Test Regression Level

**Purpose:** Control test thoroughness vs runtime tradeoff

**Levels:**
- **GATE** - Quick smoke test (~30s per module, 2-5 operations)
- **FUNC** - Functional coverage (~2-3min per module, 10-30 operations) **[DEFAULT]**
- **FULL** - Comprehensive validation (~10-30min per module, 100+ operations)

**Usage:**
```bash
# Quick smoke test (GATE)
REG_LEVEL=GATE pytest val/amba/test_axi4_master_rd.py -v

# Standard functional test (default)
pytest val/amba/test_axi4_master_rd.py -v

# Comprehensive validation (FULL)
REG_LEVEL=FULL pytest val/amba/test_axi4_master_rd.py -v
```

**When to Use Each Level:**
- **GATE**: Pre-commit checks, quick verification after small changes
- **FUNC**: Standard development, CI/CD pipelines, most debugging
- **FULL**: Pre-release validation, comprehensive regression, thorough debugging

### TEST_LEVEL - Alternative Test Level Control

Some tests (especially integration tests) use `TEST_LEVEL` instead of `REG_LEVEL`:

**Levels:**
- **basic** - Quick validation (~30s, minimal operations)
- **medium** - Moderate coverage (~90s, typical scenarios)
- **full** - Comprehensive testing (~180s+, stress testing)

**Usage:**
```bash
TEST_LEVEL=basic pytest projects/components/stream/dv/tests/integration/ -v
TEST_LEVEL=full pytest projects/components/stream/dv/tests/integration/ -v
```

### Combining Environment Variables

```bash
# Debug full regression with waveforms
WAVES=1 REG_LEVEL=FULL pytest val/amba/ -v

# Quick smoke test without waveforms
REG_LEVEL=GATE pytest val/amba/ -v

# Standard functional test with waveforms for debugging
WAVES=1 pytest val/amba/test_axi4_master_rd.py -v
```

---

## VCD Waveform Generation

### Standard Pattern for Test Files

All CocoTB test files should support the `WAVES` environment variable using this pattern:

```python
import os
import pytest
from cocotb_test.simulator import run

def test_module_basic(request):
    """Basic test for module."""

    # Test parameters
    module = "my_module"
    toplevel = module
    sim_build = "sim_build/test_module_basic"

    # VCD waveform generation support via WAVES environment variable
    # Set WAVES=1 to enable VCD tracing for debugging
    compile_args = []
    if int(os.environ.get('WAVES', '0')) == 1:
        compile_args.extend([
            "--trace",                  # VCD tracing
            "--trace-depth", "99",      # Full depth
            "--trace-max-array", "1024" # Array tracing
        ])

    # Run simulation
    run(
        # ... other parameters ...
        compile_args=compile_args,
        extra_args=['--trace-fst'] if compile_args else [],  # FST as fallback
        waves=False,  # Use compile_args instead of cocotb-test's waves parameter
    )
```

### Why This Pattern?

1. **VCD over FST**: VCD format is more reliable and widely supported than FST
2. **Environment Variable**: Consistent `WAVES=1` across all tests
3. **Full Depth**: `--trace-depth 99` captures all signal levels
4. **Conditional**: No performance impact when WAVES=0 (default)
5. **Array Support**: `--trace-max-array 1024` for memory tracing

### Example: Adding WAVES Support to Existing Test

**Before:**
```python
def test_axi4_master(request):
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        waves=False,  # Hardcoded!
    )
```

**After:**
```python
def test_axi4_master(request):
    # VCD waveform generation support via WAVES environment variable
    compile_args = []
    if int(os.environ.get('WAVES', '0')) == 1:
        compile_args.extend([
            "--trace",
            "--trace-depth", "99",
            "--trace-max-array", "1024"
        ])

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=toplevel,
        module=module,
        compile_args=compile_args,
        waves=False,  # Use compile_args for better control
    )
```

### Viewing Waveforms

```bash
# Run test with waveforms
cd val/amba
WAVES=1 pytest test_axi4_master_rd.py::test_axi4_master_rd_basic -v

# View waveforms (after test completes)
gtkwave sim_build/test_axi4_master_rd_basic/dump.vcd

# Or if test names the VCD file differently:
find sim_build -name "*.vcd" -exec gtkwave {} \;
```

---

## Test Levels (REG_LEVEL)

### Implementation Pattern

Tests should support `REG_LEVEL` environment variable to control test thoroughness:

```python
import os

@pytest.mark.parametrize("scenario", generate_test_params())
def test_axi4_master(request, scenario):
    """Test with configurable regression level."""

    # Get regression level from environment
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    # Configure test based on level
    if reg_level == 'GATE':
        num_transactions = 5
        timeout_cycles = 1000
    elif reg_level == 'FUNC':
        num_transactions = 20
        timeout_cycles = 5000
    elif reg_level == 'FULL':
        num_transactions = 100
        timeout_cycles = 50000
    else:
        pytest.fail(f"Unknown REG_LEVEL: {reg_level}")

    # Run test with configured parameters
    # ...
```

### Guidelines for Test Levels

| Level | Operations | Timeout | Runtime | Purpose |
|-------|-----------|---------|---------|---------|
| GATE | 2-5 | Short (1K cycles) | ~30s | Smoke test, quick verification |
| FUNC | 10-30 | Medium (5K cycles) | ~2-3min | Standard development, CI/CD |
| FULL | 100+ | Long (50K+ cycles) | ~10-30min | Comprehensive regression |

---

## Running Tests

### Single Test

```bash
# Run specific test function
pytest val/amba/test_axi4_master_rd.py::test_axi4_master_rd_basic -v

# Run with waveforms
WAVES=1 pytest val/amba/test_axi4_master_rd.py::test_axi4_master_rd_basic -v

# Run with full regression level
REG_LEVEL=FULL pytest val/amba/test_axi4_master_rd.py::test_axi4_master_rd_basic -v
```

### Directory of Tests

```bash
# Run all tests in directory
pytest val/amba/ -v

# Run in parallel (faster)
pytest val/amba/ -n auto -v

# Run with specific worker count
pytest val/amba/ -n 8 -v
```

### Subsystem Tests

```bash
# AMBA subsystem
pytest val/amba/ -v

# Common subsystem
pytest val/common/ -v

# STREAM project
pytest projects/components/stream/dv/tests/fub_tests/ -v

# RAPIDS project
pytest projects/components/rapids/dv/tests/fub_tests/ -v
```

### Regression Suites

Each subsystem may have Makefile targets for regression testing:

```bash
# AMBA regressions
cd val/amba
make run-amba-gate-parallel    # Quick smoke test
make run-amba-func-parallel    # Standard functional (default)
make run-amba-full-parallel    # Comprehensive validation

# HPET regressions
cd projects/components/apb_hpet/dv/tests
make run-all-basic             # Quick validation
make run-all-full              # Comprehensive validation
```

### Test Output Control

```bash
# Verbose output
pytest test_module.py -v

# Show print statements
pytest test_module.py -s

# Show only failures
pytest test_module.py -v --tb=short

# Show minimal traceback
pytest test_module.py -v --tb=line

# Capture logging
pytest test_module.py -v --log-cli-level=DEBUG
```

---

## Test Structure

### Directory Organization

```
rtldesignsherpa/
├── val/                        # Validation tests for rtl/
│   ├── common/                 # Tests for rtl/common/
│   │   ├── test_counter_bin.py
│   │   ├── test_fifo_sync.py
│   │   └── ...
│   ├── amba/                   # Tests for rtl/amba/
│   │   ├── test_axi4_master_rd.py
│   │   ├── test_axi4_slave_wr.py
│   │   └── ...
│   └── ...
│
├── projects/components/        # Project tests
│   ├── stream/dv/tests/
│   │   ├── fub_tests/          # Functional Unit Block tests
│   │   │   ├── test_scheduler.py
│   │   │   ├── test_descriptor_engine.py
│   │   │   └── ...
│   │   └── integration_tests/  # Multi-block integration
│   │       └── test_stream_integration.py
│   ├── rapids/dv/tests/
│   │   └── fub_tests/
│   └── ...
│
└── bin/CocoTBFramework/        # Shared testbench infrastructure
    ├── components/             # Protocol drivers (AXI, APB, etc.)
    ├── tbclasses/              # Reusable testbench classes
    └── scoreboards/            # Transaction checkers
```

### Test File Naming

- **Test files**: `test_<module_name>.py`
- **Test functions**: `test_<module_name>_<scenario>()`
- **Testbench classes**: `<ModuleName>TB`

Examples:
- `test_axi4_master_rd.py` → `test_axi4_master_rd_basic()`
- `test_scheduler.py` → `test_scheduler_descriptor_fetch()`

### Testbench Class Location

**CRITICAL: Project-specific testbench classes must be in project area**

```
✅ CORRECT:
projects/components/stream/dv/tbclasses/scheduler_tb.py
projects/components/rapids/dv/tbclasses/descriptor_engine_tb.py

❌ WRONG:
bin/CocoTBFramework/tbclasses/stream/scheduler_tb.py  # Don't put in framework!
```

**Framework is only for truly shared code (AXI drivers, APB monitors, etc.)**

---

## Writing New Tests

### Testbench Class Template

```python
"""
Testbench class for my_module.

Purpose: Brief description of what this testbench validates.

Author: your_name
Created: YYYY-MM-DD
"""

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

from CocoTBFramework.tbclasses.shared.tbbase import TBBase


class MyModuleTB(TBBase):
    """Testbench for my_module."""

    def __init__(self, dut):
        """Initialize testbench."""
        super().__init__(dut)
        self.dut = dut
        self.clk = dut.clk
        self.clk_name = 'clk'
        self.rst_n = dut.rst_n

    async def setup_clocks_and_reset(self):
        """Complete initialization - clocks and reset."""
        # Start clock
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Initialize inputs
        self.dut.input_valid.value = 0
        self.dut.input_data.value = 0

        # Reset sequence
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert reset signal."""
        self.rst_n.value = 0

    async def deassert_reset(self):
        """Deassert reset signal."""
        self.rst_n.value = 1

    async def send_transaction(self, data):
        """Send a single transaction."""
        self.dut.input_valid.value = 1
        self.dut.input_data.value = data
        await RisingEdge(self.clk)
        self.dut.input_valid.value = 0
```

### Test Runner Template

```python
"""
Test runner for my_module.

Purpose: Validate my_module functionality.

Author: your_name
Created: YYYY-MM-DD
"""

import cocotb
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

from projects.components.myproject.dv.tbclasses.my_module_tb import MyModuleTB


@cocotb.test()
async def test_my_module_basic(dut):
    """Basic functionality test."""
    # Initialize testbench
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()

    # Run test
    await tb.send_transaction(0x1234)

    # Verify results
    assert tb.dut.output_valid.value == 1
    assert tb.dut.output_data.value == 0x1234


@cocotb.test()
async def test_my_module_multiple(dut):
    """Multiple transaction test."""
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()

    # Get regression level
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    num_trans = {'GATE': 5, 'FUNC': 20, 'FULL': 100}[reg_level]

    # Run transactions
    for i in range(num_trans):
        await tb.send_transaction(i)

    print(f"Completed {num_trans} transactions")
```

---

## Best Practices

### 1. Always Support WAVES

Every test should support the WAVES environment variable for debugging.

### 2. Use REG_LEVEL for Scalability

Configure test thoroughness based on REG_LEVEL to balance coverage vs runtime.

### 3. Testbench Classes in Project Area

Project-specific testbench classes belong in `projects/<name>/dv/tbclasses/`, not in the framework.

### 4. Three Required Methods

All testbench classes must implement:
- `async def setup_clocks_and_reset(self)` - Complete initialization
- `async def assert_reset(self)` - Assert reset
- `async def deassert_reset(self)` - Deassert reset

### 5. Descriptive Test Names

Use clear, descriptive names: `test_axi4_master_rd_burst_aligned()` not `test1()`.

### 6. Independent Tests

Each test should be independent and able to run in any order.

### 7. Cleanup

Tests should not leave persistent state that affects other tests.

---

## Troubleshooting

### Test Hangs/Timeout

```bash
# Enable verbose logging
WAVES=1 pytest test_module.py -v -s --log-cli-level=DEBUG

# View waveforms to see where it's stuck
gtkwave sim_build/dump.vcd
```

### VCD Not Generated

Check that:
1. `WAVES=1` is set
2. `compile_args` includes `--trace`
3. Test completed (VCD written at end)
4. Simulator is Verilator (Icarus uses different flags)

### Test Fails Only in FULL

Likely a corner case or timing issue exposed by more operations:
```bash
# Run with waveforms to debug
WAVES=1 REG_LEVEL=FULL pytest test_module.py -v -s
```

### Import Errors

Check that repo root is added to Python path:
```python
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)
```

---

## Quick Reference

```bash
# Standard functional test
pytest test_module.py -v

# Debug with waveforms
WAVES=1 pytest test_module.py -v

# Quick smoke test
REG_LEVEL=GATE pytest test_module.py -v

# Comprehensive validation with waveforms
WAVES=1 REG_LEVEL=FULL pytest test_module.py -v

# Run all tests in parallel
pytest val/amba/ -n auto -v

# View waveforms
gtkwave sim_build/test_name/dump.vcd
```

---

**Version:** 1.0
**Last Updated:** 2025-10-26
**Maintained By:** RTL Design Sherpa Project
