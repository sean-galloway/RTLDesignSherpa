# Task: TASK-017 - Add WaveDrom Support to APB Monitor Tests

## Priority
**P2 - Medium**

## Status
**🔴 Not Started**

## Description

Add minimal WaveDrom timing diagram generation to APB monitor tests, following the pattern established in GAXI buffer tests. Generate clean, focused waveforms showing key APB protocol scenarios.

## Background

**Successful Pattern:** GAXI buffer tests (sync/async) now have WaveDrom integration:
- Separate wavedrom test functions (non-intrusive)
- Segmented capture for clean scenarios
- ENABLE_WAVEDROM flag for opt-in generation
- Generates WaveJSON → PNG/SVG via wavedrom-cli

**Reference Implementation:**
- `val/amba/test_gaxi_buffer_sync.py` (lines 163-682)
- `val/amba/test_gaxi_buffer_async.py` (lines 200-572)
- `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md`

**Goal:** Apply same pattern to APB monitors for protocol visualization and documentation.

## Prerequisites

- [x] WaveDrom framework functional in CocoTBFramework
- [x] GAXI WaveDrom integration complete (reference implementation)
- [ ] APB monitor tests functional

## Deliverables

### 1. APB Protocol Field Configuration

**File:** `bin/CocoTBFramework/tbclasses/wavedrom_user/apb.py` (create if needed)

**Functions to Create:**
```python
def get_apb_field_config(addr_width=16, data_width=32):
    """
    Create FieldConfig for APB protocol signals.

    APB Protocol Fields:
    - paddr: Address field (hex format)
    - psel: Select signal (binary)
    - penable: Enable signal (binary)
    - pwrite: Write direction (binary)
    - pwdata: Write data (hex format)
    - prdata: Read data (hex format)
    - pready: Ready signal (binary)
    - pslverr: Error response (binary)
    """
    # Return FieldConfig with APB-specific formatting

def create_apb_wavejson_generator(field_config, signal_prefix=""):
    """Create WaveJSON generator configured for APB protocol"""
    # Return WaveJSONGenerator
```

### 2. APB Monitor WaveDrom Test

**File:** `val/amba/test_apb_monitor.py` (modify existing)

**Add Imports:**
```python
from CocoTBFramework.tbclasses.wavedrom_user.apb import (
    get_apb_field_config,
    create_apb_wavejson_generator,
)
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver,
    TemporalConstraint,
    TemporalEvent,
    SignalTransition,
    TemporalRelation
)
```

**Add CocoTB Test Function:**
```python
@cocotb.test(timeout_time=5, timeout_unit="sec")
async def apb_wavedrom_test(dut):
    """
    WaveDrom timing diagram generation for APB monitor.

    Generates 3 key scenarios:
    1. Basic read transaction
    2. Basic write transaction
    3. Error response (PSLVERR)
    """
    # Check if enabled
    enable_wavedrom = int(os.environ.get('ENABLE_WAVEDROM', '0'))
    if not enable_wavedrom:
        dut._log.info("⏭️  WaveDrom disabled, skipping")
        return

    # Setup testbench
    # Setup WaveDrom with auto-binding
    # Define 3 scenario constraints
    # Run segmented capture
```

**Add Pytest Parametrized Test:**
```python
def generate_apb_wavedrom_params():
    """Generate parameters for APB WaveDrom tests"""
    return [
        # addr_width, data_width, clk_period
        (16, 32, 10),  # Standard configuration
    ]

@pytest.mark.parametrize("addr_width, data_width, clk_period",
                         generate_apb_wavedrom_params())
def test_apb_monitor_wavedrom(request, addr_width, data_width, clk_period):
    """APB monitor wavedrom test - generates timing diagrams."""
    # Setup RTL sources
    # Set ENABLE_WAVEDROM=1
    # Run with testcase="apb_wavedrom_test"
```

### 3. APB Protocol Scenarios

**Scenario 1: Basic Read Transaction**
- Constraints: psel=1 → penable=1 → pready=1 (read cycle)
- Shows: Address setup, enable, ready, data return
- Edge annotations: paddr → prdata

**Scenario 2: Basic Write Transaction**
- Constraints: psel=1, pwrite=1 → penable=1 → pready=1
- Shows: Address setup, write data, enable, ready
- Edge annotations: paddr → pwdata → completion

**Scenario 3: Error Response**
- Constraints: psel=1 → penable=1 → pslverr=1
- Shows: Transaction with error response
- Edge annotations: Highlight error path

**Expected Output:**
```
val/amba/WaveJSON/
├── test_apb_monitor_aw16_dw32_read_transaction.wavejson
├── test_apb_monitor_aw16_dw32_write_transaction.wavejson
└── test_apb_monitor_aw16_dw32_error_response.wavejson
```

### 4. Documentation Updates

**File:** `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md` (update existing)

Add section:
```markdown
## APB Monitor WaveDrom Integration

### test_apb_monitor.py
**Status:** ✅ Complete
**Generates:** 3 WaveJSON files

**Scenarios:**
1. Basic read transaction
2. Basic write transaction
3. Error response (PSLVERR)

**Run:**
```bash
pytest test_apb_monitor.py::test_apb_monitor_wavedrom -v
```
```

## Testing

**Run WaveDrom Test:**
```bash
cd val/amba
pytest test_apb_monitor.py::test_apb_monitor_wavedrom -v
```

**Generate Images:**
```bash
cd val/amba/WaveJSON
for json in test_apb_monitor*.wavejson; do
    wavedrom-cli -i "$json" -s ../PNG/"${json%.wavejson}.png"
    wavedrom-cli -i "$json" -s ../SVG/"${json%.wavejson}.svg"
done
```

**Verify Output:**
- [ ] 3 WaveJSON files generated
- [ ] Clean, readable waveforms
- [ ] Proper APB protocol timing shown
- [ ] Edge annotations present

## Success Criteria

- [ ] APB field configuration created
- [ ] WaveDrom test function added to test_apb_monitor.py
- [ ] Pytest parametrized test added
- [ ] 3 WaveJSON files generated successfully
- [ ] Images generated (PNG/SVG)
- [ ] Documentation updated
- [ ] Original functional tests still pass

## Design Decisions

1. **Minimal Scenarios:** Only 3 scenarios (not exhaustive)
   - Focus on core protocol visualization
   - Keep test execution fast

2. **Separate Test:** WaveDrom test separate from functional tests
   - Non-intrusive to existing tests
   - Opt-in via test name

3. **Standard Configuration:** Single addr/data width combination
   - 16-bit address, 32-bit data (common)
   - Can expand later if needed

4. **Reuse Framework:** Use existing WaveDrom infrastructure
   - TemporalConstraintSolver
   - Auto-binding
   - Segmented capture

## References

- **Pattern:** `val/amba/test_gaxi_buffer_sync.py` (reference implementation)
- **Framework:** `bin/CocoTBFramework/components/wavedrom/`
- **Summary:** `val/amba/WAVEDROM_INTEGRATION_SUMMARY.md`
- **APB Spec:** ARM IHI0024 (APB Protocol Specification)

## Related Tasks

**Prerequisites:**
- GAXI WaveDrom integration (complete) - provides pattern

**Related:**
- TASK-018: AXI4 WaveDrom support
- TASK-019: AXIS WaveDrom support
- TASK-020: Identify other tests needing waves

---

**Task Owner:** TBD
**Created:** 2025-10-06
**Target Completion:** TBD
**Estimated Effort:** 3-4 hours
