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

# Scheduler Group AXI Signal Naming Conflicts

**Status:** Known Issue - Workaround Available
**Component:** `projects/components/rapids/rtl/rapids_macro/scheduler_group.sv`
**Severity:** Medium
**Date Identified:** 2025-10-15

---

## Issue Description

The `scheduler_group` module has internal signals (`desc_valid`, `desc_ready`) connecting descriptor_engine to scheduler that conflict with external AXI port names (`desc_ar_valid`, `desc_ar_ready`).

When using AXI factory functions with pattern matching (e.g., `create_axi4_slave_rd()` with `prefix="desc_"`), the factory finds **multiple matches**:
- `desc_valid` (internal wire)
- `desc_ar_valid` (external AXI AR channel port)

This causes factory initialization to fail with: "Signal conflicts for AR_Slave: i_valid matches desc_valid, desc_ar_valid"

### Affected Signals

**Descriptor Engine Interface:**
- **Internal:** `desc_valid`, `desc_ready` (lines 175-176)
- **External:** `desc_ar_valid`, `desc_ar_ready`, `desc_r_valid`, `desc_r_ready` (lines 81-96)

**Program Engine Interface:**
- **Internal:** `prog_valid`, `prog_ready` (lines 188-189)
- **External:** `prog_aw_valid`, `prog_aw_ready`, `prog_w_valid`, `prog_w_ready`, `prog_b_valid`, `prog_b_ready` (lines 103-124)

---

## Root Cause

The issue arises from overlapping naming conventions:
1. **Internal protocol:** Simple `{block}_valid` / `{block}_ready` handshake
2. **External AXI:** Standard `{block}_{channel}_valid` / `{block}_{channel}_ready` pattern

When the factory searches for `desc_*valid`, it finds BOTH internal and external signals, causing ambiguity.

---

## Workarounds

### Option 1: Use Credit Encoding Test (✅ Recommended)

The credit encoding validation test works correctly and validates the critical scheduler functionality:

```bash
timeout 180 python -m pytest \
  projects/components/rapids/dv/tests/integration_tests/test_scheduler_group_integration.py::test_credit_counter_exponential_encoding \
  -v
```

**Test Coverage:**
- ✅ Credit counter exponential encoding (0→1, 1→2, 2→4, ..., 14→16384, 15→0)
- ✅ Scheduler state machine initialization
- ✅ Configuration signal handling

### Option 2: Explicit Signal Mapping (⚠️ Complex)

Use explicit `signal_map` parameter to bypass pattern matching:

```python
desc_ar_signal_map = {
    'i_valid': 'desc_ar_valid',
    'o_ready': 'desc_ar_ready',
    'i_addr': 'desc_ar_addr',
    # ... all AR channel signals ...
    'o_valid': 'desc_r_valid',
    'i_ready': 'desc_r_ready',
    'o_data': 'desc_r_data',
    # ... all R channel signals ...
}

desc_axi_slave = create_axi4_slave_rd(
    dut=dut,
    clock=clk,
    prefix="",  # No prefix with explicit mapping
    signal_map=desc_ar_signal_map,
    ...
)
```

**Status:** Partially working - requires complete signal map for all AXI channels

### Option 3: Manual AXI Responders (✅ Simple Tests)

For simple validation, create lightweight manual responders:

```python
async def desc_axi_responder(self):
    """Simple AXI read responder for descriptor fetches"""
    while True:
        await self.wait_clocks(self.clk_name, 1)
        if int(self.dut.desc_ar_valid.value) == 1:
            # Generate descriptor read response
            self.dut.desc_r_valid.value = 1
            self.dut.desc_r_data.value = descriptor_data
            # ... handshaking ...
            self.dut.desc_r_valid.value = 0
```

---

## Long-Term Solutions

### Solution 1: Rename Internal Signals (⚠️ RTL Change)

Rename internal signals to avoid conflicts:
- `desc_valid` → `desc_to_sched_valid`
- `desc_ready` → `desc_to_sched_ready`
- `prog_valid` → `prog_to_sched_valid`
- `prog_ready` → `prog_to_sched_ready`

**Impact:** Requires RTL modifications and re-verification of all internal connections

### Solution 2: Enhanced Factory Signal Resolution

Improve AXI factories to handle hierarchical signal conflicts:
- Prioritize exact matches over partial matches
- Add `exclude_patterns` parameter
- Support signal disambiguation hints

**Impact:** Framework enhancement, but benefits all future tests

### Solution 3: Test at Higher Integration Level

Test `scheduler_group` as part of larger integration (e.g., within `scheduler_group_array` or full RAPIDS):
- External AXI signals connect to actual system components
- Internal signals hidden within hierarchy
- Factory pattern matching works correctly at top level

**Impact:** Requires building larger integration tests first

---

## Current Status

- ✅ **Credit encoding test PASSES** - validates core scheduler functionality
- ⚠️ **Comprehensive test FAILS** - due to AXI factory signal conflicts
- 📝 **Workaround:** Use credit encoding test for scheduler_group validation

### Test Results

```
✅ PASS: test_credit_counter_exponential_encoding
   - Validates: Credit initialization with exponential encoding
   - Status: 100% success rate

❌ FAIL: test_basic_scheduler_group_operation_comprehensive
   - Issue: AXI factory signal conflicts
   - Workaround: Use credit encoding test or manual responders
```

---

## Related Issues

- `projects/components/rapids/known_issues/scheduler.md` - Credit counter exponential encoding (FIXED)
- AXI factory pattern matching limitations (Framework enhancement)

---

## References

- RTL: `projects/components/rapids/rtl/rapids_macro/scheduler_group.sv` (lines 81-189)
- Testbench: `bin/CocoTBFramework/tbclasses/rapids/scheduler_group_tb.py` (lines 238-271)
- Tests: `projects/components/rapids/dv/tests/integration_tests/test_scheduler_group_integration.py`

---

**Priority:** P2 (Medium) - Workarounds available, core functionality validated
**Assigned To:** TBD
**Target:** Framework enhancement or RTL cleanup in future release
