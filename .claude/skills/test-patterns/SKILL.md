---
name: test-patterns
description: "Test structure for this repo: Pattern A (val/) vs Pattern B (projects/components/), the mandatory cocotb_test_* prefix, pytest function naming, the three required TB methods, and the gate/func/full level convention. Use before writing or changing any test."
---

# Test patterns

Moved out of the root `CLAUDE.md`, which loaded all of this into every session
whether or not a test was in scope. `/GLOBAL_REQUIREMENTS.md` remains the
enforcement authority and wins on conflict.

## Writing Tests

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
2. Import appropriate BFMs from `bin/TBClasses/`
3. Target >95% functional coverage
4. Document test methodology in file header
5. Include waveform dumps for debugging

**Test File Location:**
- `val/common/test_{module}.py` for rtl/common/
- `val/math/test_{module}.py` for rtl/math/
- `val/amba/test_{module}.py` for rtl/amba/
- `projects/components/{name}/dv/tests/` for project-specific tests (RAPIDS, STREAM, bridge, ...)

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
        'rtl_stream_fub': '../../../../rtl/fub',
    })

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dmas/stream/rtl/filelists/fub/sram_controller.f'
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

See `projects/components/dmas/stream/dv/tests/fub/test_sram_controller.py` for reference implementation.

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

## Test Naming and Organization

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

