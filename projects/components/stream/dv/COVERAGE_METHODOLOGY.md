# STREAM Coverage Methodology

This document describes the coverage collection methodology for the STREAM component,
designed to be replicated across all test levels (FUB, Macro, Top).

## Overview

The STREAM coverage infrastructure collects two types of coverage:

1. **Protocol Coverage**: AXI/APB transaction-level coverage (what the tests exercise)
2. **Line Coverage**: Verilator code coverage (what RTL paths are executed)

Coverage is configured with "legal coverage" mode that filters for only the
variations STREAM actually supports (vs. full AXI4 protocol space).

## Directory Structure

Each test level has identical coverage infrastructure:

```
dv/tests/{fub,macro,top}/
├── conftest.py              # Pytest hooks for coverage aggregation
├── coverage_data/
│   ├── per_test/            # Individual test coverage files
│   │   ├── test_name_protocol.json
│   │   └── test_name_summary.json
│   ├── merged/              # Aggregated coverage
│   │   └── latest_merged_coverage.json
│   └── reports/             # Human-readable reports
│       └── latest_coverage_report.md
└── logs/                    # Test logs
```

## Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `COVERAGE=1` | Enable coverage collection | 0 (disabled) |
| `COVERAGE_LEGAL=1` | Use legal coverage filtering | 0 (full protocol) |
| `TEST_LEVEL` | Test complexity: gate/func/full | gate |

## Running Tests with Coverage

```bash
# Run FUB tests with coverage
PYTHONPATH=/path/to/bin:$PYTHONPATH \
SIM=verilator \
WAVES=0 \
COVERAGE=1 \
COVERAGE_LEGAL=1 \
TEST_LEVEL=basic \
python -m pytest test_scheduler.py -v

# Run macro tests with coverage
PYTHONPATH=/path/to/bin:$PYTHONPATH \
SIM=verilator \
WAVES=0 \
COVERAGE=1 \
COVERAGE_LEGAL=1 \
TEST_LEVEL=func \
python -m pytest test_stream_core.py -v

# Run top tests with coverage
PYTHONPATH=/path/to/bin:$PYTHONPATH \
SIM=verilator \
WAVES=0 \
COVERAGE=1 \
COVERAGE_LEGAL=1 \
TEST_LEVEL=full \
python -m pytest test_stream_top.py -v
```

## Coverage Collection API

### 1. Get Coverage Helper in Testbench

```python
from projects.components.stream.dv.stream_coverage import CoverageHelper

class MyTestBench(TBBase):
    def __init__(self, dut, ...):
        super().__init__(dut, ...)

        # Initialize coverage with test name
        self.coverage = CoverageHelper.get_instance(
            test_name="test_my_module_basic",
            log=self.log
        )
```

### 2. Sample Protocol Coverage

```python
# Sample AXI read transaction
self.coverage.sample_axi_read(
    burst_type=1,    # INCR
    burst_size=64,   # 64 bytes (size_64)
    burst_len=16,    # 16 beats
    is_okay=True,    # OKAY response
    is_first=True,   # First beat of burst
    is_last=True     # Last beat of burst
)

# Sample AXI write transaction
self.coverage.sample_axi_write(
    burst_type=1,    # INCR
    burst_size=64,   # 64 bytes
    burst_len=8,     # 8 beats
    is_okay=True,
    is_first=True,
    is_last=True
)

# Sample APB transaction
self.coverage.sample_apb_read(is_error=False)   # Successful read
self.coverage.sample_apb_write(is_error=False)  # Successful write
self.coverage.sample_apb_read(is_error=True)    # Error response

# Sample functional scenarios
self.coverage.sample_scenario("concurrent_rw")      # Concurrent read/write
self.coverage.sample_scenario("backpressure")       # Backpressure applied
self.coverage.sample_scenario("descriptor_chain")   # Descriptor chaining
self.coverage.sample_scenario("max_outstanding")    # Max transactions in flight
self.coverage.sample_scenario("empty_desc")         # Empty descriptor handling
```

### 3. Save Coverage at Test End

```python
# In testbench cleanup or at end of test
self.coverage.save()
```

## Legal Coverage Points

The legal coverage configuration (`stream_legal_coverage.yaml`) defines what
coverage points are valid for STREAM. Only these points count toward the
coverage percentage when `COVERAGE_LEGAL=1`.

### Legal AXI Burst Sizes
- `size_64`: 64-byte bursts (512-bit data width)
- Matches STREAM's minimum supported data width

### Legal AXI Burst Types
- `INCR`: Incrementing bursts (primary transfer mode)
- FIXED and WRAP are NOT supported by STREAM

### Legal Burst Lengths
- `len_1` through `len_256`: All AXI4 burst lengths

### Legal Scenarios
- `basic_transfer`: Single descriptor transfer
- `concurrent_rw`: Concurrent read and write
- `backpressure`: Applied backpressure handling
- `descriptor_chain`: Multiple chained descriptors
- `channel_reset`: Channel reset handling
- `timeout`: Timeout detection
- `irq`: Interrupt generation
- `max_outstanding`: Maximum outstanding transactions
- `full_pipeline`: Full pipeline utilization
- `empty_desc`: Empty descriptor handling
- `narrow_transfer`: Narrow (non-full-width) transfers
- `wrap_burst`: Wrapping burst (if supported)
- `descriptor_error`: Descriptor error injection

## Coverage Aggregation

The `conftest.py` in each test directory aggregates coverage at session end:

1. **Per-test collection**: Each test saves `{test_name}_summary.json`
2. **Session finish**: `pytest_sessionfinish` hook calls `_aggregate_coverage()`
3. **Merge**: All per-test files merged into `latest_merged_coverage.json`
4. **Report**: Human-readable `latest_coverage_report.md` generated

## Coverage Report Format

```markdown
# STREAM Component Coverage Report

**Generated:** 2025-01-10 18:23:47
**Tests Run:** 16

## Summary

| Metric | Coverage | Target | Status |
|--------|----------|--------|--------|
| Protocol Coverage | 85.4% | 80% | PASS |
| Line Coverage | 100.0% | 80% | PASS |

## Protocol Coverage by Group

| Group | Covered | Total | Percentage |
|-------|---------|-------|------------|
| axi_read_burst_size | 1 | 1 | 100.0% |
| axi_read_burst_type | 1 | 1 | 100.0% |
| scenarios | 13 | 13 | 100.0% |
...

## Coverage Gaps

The following coverage points were NOT hit:
- **apb_transactions**: read_error (0 hits)
...
```

## Adding Coverage to New Tests

### Step 1: Import CoverageHelper

```python
from projects.components.stream.dv.stream_coverage import CoverageHelper
```

### Step 2: Initialize in Testbench

```python
class StreamCoreTB(TBBase):
    def __init__(self, dut, ...):
        super().__init__(dut, ...)

        # Get test name from environment
        test_name = os.environ.get('TEST_NAME', 'test_stream_core')
        self.coverage = CoverageHelper.get_instance(test_name, log=self.log)
```

### Step 3: Sample During Test Execution

```python
async def run_test(self):
    # Sample AXI transactions as they happen
    for txn in self.axi_transactions:
        self.coverage.sample_axi_read(...)

    # Sample functional scenarios when they occur
    if self.is_concurrent_rw():
        self.coverage.sample_scenario("concurrent_rw")
```

### Step 4: Save at End

```python
async def cleanup(self):
    self.coverage.save()
```

## Testbench Integration Pattern

The recommended pattern integrates coverage sampling directly into the
testbench's transaction handling:

```python
class SchedulerTB(TBBase):
    """Scheduler testbench with integrated coverage."""

    def __init__(self, dut, ...):
        super().__init__(dut, ...)
        self.coverage = CoverageHelper.get_instance(
            test_name=os.environ.get('TEST_NAME', 'scheduler'),
            log=self.log
        )

    async def test_basic_flow(self):
        """Basic descriptor flow test."""
        # Sample handshakes
        self.coverage.sample_handshake("read_request")
        self.coverage.sample_handshake("read_response")

        # Sample AXI transactions
        self.coverage.sample_axi_read(
            burst_type=1, burst_size=64, burst_len=16,
            is_okay=True, is_first=True, is_last=True
        )

        # Sample APB configuration
        self.coverage.sample_apb_write(is_error=False)

        # Sample scenario
        self.coverage.sample_scenario("basic_transfer")

        # ... test logic ...

        # Save coverage
        self.coverage.save()
```

## Replicating to Other Components

To add coverage to a new component:

1. **Copy stream_coverage package**:
   ```
   cp -r stream/dv/stream_coverage <new_component>/dv/<component>_coverage
   ```

2. **Update package name and imports**

3. **Create legal coverage YAML** for component-specific variations

4. **Add conftest.py coverage hooks** to each test directory

5. **Integrate CoverageHelper** into testbenches

## Coverage Targets

| Metric | Target | Rationale |
|--------|--------|-----------|
| Protocol Coverage | 80% | All supported protocol variations exercised |
| Line Coverage | 80% | All reachable code paths executed |

## Known Limitations

1. **Toggle coverage**: Verilator toggle coverage counts each bit of multi-bit
   signals separately, making 100% toggle coverage difficult for wide data paths

2. **Line coverage for dead code**: Some RTL paths may be unreachable due to
   parameter configurations (e.g., disabled features)

3. **Cross-coverage**: Current infrastructure does not support cross-coverage
   between protocol dimensions (e.g., burst_type × burst_size)

## Troubleshooting

### No coverage data generated
- Verify `COVERAGE=1` is set
- Check test log for coverage save messages
- Verify `coverage_data/per_test/` directory exists

### Coverage report shows 0%
- Check that `CoverageHelper.save()` is called at test end
- Verify coverage sampling calls are executed during test

### Legal coverage lower than expected
- Review `stream_legal_coverage.yaml` for missing legal points
- Check test is sampling the expected coverage points

### Aggregation not running
- Verify `pytest_sessionfinish` hook in conftest.py
- Check pytest session completes normally (no crashes)
