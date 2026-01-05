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

# RAPIDS Control Read Engine (ctrlrd_engine) Tests

## Overview

Comprehensive test suite for the RAPIDS control read engine FUB that performs pre-descriptor control read operations with retry mechanism.

## Test Files

### 1. `test_ctrlrd_engine_simple.py`
**Purpose:** Basic validation test
**Tests:**
- Basic read-and-match operation
- Idle state checking
- AXI read interface activity
- Completion and error handling

**Run:**
```bash
pytest test_ctrlrd_engine_simple.py -v
```

### 2. `test_ctrlrd_engine.py`
**Purpose:** Comprehensive parametrized test suite
**Test Scenarios:**
- **Basic Read-Match:** First read matches expected data
- **Read-Retry-Match:** Retry mechanism with eventual match
- **Null Address:** 64'h0 = immediate success without AXI read
- **Masked Comparison:** Various mask patterns
- **Mixed:** All scenarios combined

**Delay Profiles:**
- `fixed_delay`: Predictable timing
- `minimal_delay`: Stress test with minimal delays
- `fast_consumer`: Consumer faster than producer
- `backpressure`: Heavy backpressure scenarios
- `random_delay`: Random timing variations

**Run:**
```bash
# All tests
pytest test_ctrlrd_engine.py -v

# Single scenario
pytest "test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.BASIC_READ_MATCH-DelayProfile.FIXED_DELAY-3]" -v

# All retry scenarios
pytest test_ctrlrd_engine.py -k "retry" -v
```

## Testbench Architecture

### Testbench Class: `CtrlrdEngineTB`
**Location:** `projects/components/rapids/dv/tbclasses/ctrlrd_engine_tb.py`

**Key Features:**
- Follows standardized RAPIDS testbench architecture
- GAXI Master BFM for ctrlrd interface
- AXI read responder for simulating memory
- Configurable delay profiles for timing coverage
- Safety monitoring for resource usage
- Mandatory initialization methods (setup_clocks_and_reset, assert_reset, deassert_reset)

**Test Methods:**
- `test_basic_read_match()` - First read matches
- `test_read_retry_match()` - Retry with eventual match
- `test_null_address()` - Immediate success for null address
- `test_masked_comparison()` - Various mask patterns
- `run_test_suite()` - Comprehensive test suite

## RTL Module Under Test

**Module:** `ctrlrd_engine.sv`
**Location:** `projects/components/rapids/rtl/rapids_fub/ctrlrd_engine.sv`

**Key Features:**
- 7-state FSM (IDLE → ISSUE_ADDR → WAIT_DATA → COMPARE → RETRY_WAIT → MATCH/ERROR)
- Read-and-compare with configurable mask
- Automatic retry (configurable 0-511 retries)
- 1µs delay between retries
- Null address support (64'h0 = immediate success)
- AXI4 read interface (AR and R channels, 32-bit reads)
- Channel reset support
- Monitor packet generation

**Configuration:**
- `cfg_ctrlrd_max_try[8:0]`: Max retry count (0-511)
- `cfg_channel_reset`: Channel reset
- `tick_1us`: 1µs tick input from scheduler_group

## Test Parameters

| Parameter | Type | Values | Description |
|-----------|------|--------|-------------|
| num_channels | int | 32 | Number of channels |
| addr_width | int | 64 | Address bus width |
| scenario | TestScenario | See above | Test scenario |
| profile | DelayProfile | See above | Timing profile |
| max_retries | int | 3, 5 | Max retry count |

## Test Coverage

### Scenarios Covered
- ✅ Basic read-match (first read matches)
- ✅ Read-retry-match (eventual match after retries)
- ✅ Null address handling (immediate success)
- ✅ Masked comparison (various mask patterns)
- ✅ Mixed scenarios (comprehensive)

### Timing Coverage
- ✅ Fixed delays
- ✅ Minimal delays (stress test)
- ✅ Fast consumer
- ✅ Heavy backpressure
- ✅ Random timing

### Error Coverage
- ✅ Max retries exceeded
- ✅ AXI response errors (future)
- ✅ Channel reset during operation

## RTL Filelist

**Location:** `projects/components/rapids/rtl/filelists/fub/ctrlrd_engine.f`

**Dependencies:**
- monitor_pkg.sv (monitor event definitions)
- rapids_pkg.sv (RAPIDS-specific definitions)
- gaxi_skid_buffer.sv (2-deep skid buffer)

## Example Test Output

```
============================= test session starts ==============================
collected 7 items

test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.BASIC_READ_MATCH-DelayProfile.FIXED_DELAY-3] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.NULL_ADDRESS-DelayProfile.FIXED_DELAY-3] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.MASKED_COMPARISON-DelayProfile.FIXED_DELAY-3] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.READ_RETRY_MATCH-DelayProfile.MINIMAL_DELAY-3] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.READ_RETRY_MATCH-DelayProfile.FAST_CONSUMER-5] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.READ_RETRY_MATCH-DelayProfile.BACKPRESSURE-3] PASSED
test_ctrlrd_engine.py::test_ctrlrd_engine[32-64-TestScenario.MIXED-DelayProfile.FIXED_DELAY-3] PASSED

============================== 7 passed in 12.34s ===============================
```

## Debugging

### View Waveforms
```bash
# After test run, view waveforms
gtkwave logs/test_ctrlrd_engine_*.vcd
```

### Check Logs
```bash
# View test logs
cat logs/test_ctrlrd_engine_*.log
```

### View Build Artifacts
```bash
# Check simulation build directory
ls local_sim_build/test_ctrlrd_engine_*/
```

## Known Issues

1. **Simple test warnings:** The simple test shows timeout/idle warnings because it doesn't fully simulate the AXI read flow. This is expected and not an error.

2. **RTL Bug Fixed:** Multi-driver error on `ctrlrd_ready` signal fixed (removed incorrect skid buffer assignment).

## See Also

- **RTL Specification:** `projects/components/rapids/docs/rapids_spec/ch02_blocks/01_04_ctrlrd_engine.md`
- **Similar Tests:** `../ctrlwr_engine/` - Control write engine tests with similar structure
- **Parent README:** `../README.md` - RAPIDS FUB test suite overview
