# Known Issue: Orphan Error Packet Flood

**Status:** ✅ FIXED (2025-10-03)
**Severity:** HIGH - Blocks monitor operation
**Date Reported:** 2025-10-02
**Date Fixed:** 2025-10-03
**Affects:** `axi_monitor_base.sv` (specifically `axi_monitor_reporter.sv`)

---

## Summary

The AXI monitor generates duplicate orphan error packets continuously (every clock cycle) after detecting an orphan data transaction, flooding the monitor bus and preventing legitimate completion packets from being generated.

---

## Symptoms

1. **Continuous packet generation**: After detecting an orphan data beat, the monitor generates identical error packets every clock cycle
2. **Monitor bus saturation**: Orphan error packets dominate the monitor bus output
3. **Completion packet starvation**: Legitimate transaction completion packets are blocked or delayed
4. **Test failures**: Zero-delay stress tests fail because expected completion packets are not generated

---

## Affected Configurations

- **All configurations** with orphan detection enabled
- **Particularly severe** with:
  - ID_WIDTH=8 (larger ID space = more potential orphan IDs)
  - MAX_TRANSACTIONS=2 (smaller table = more orphan conditions)
  - High transaction rate (stress tests)

---

## Reproduction

### Test Case: `test_axi4_monitor[4-32-2-True-True-table]`

**Configuration:**
- ID_WIDTH=4
- ADDR_WIDTH=32
- MAX_TRANSACTIONS=2
- Protocol: AXI4 Read

**Test Sequence:**
1. Run orphan detection test (Test 4)
2. Call `send_orphan_data(txn_id=12)` and `send_orphan_data(txn_id=13)`
3. Observe continuous error packet generation

**Expected Behavior:**
- 2 orphan error packets (one per orphan data beat)

**Actual Behavior:**
- Continuous stream of duplicate error packets:
  ```
  [14] [PROTOCOL_AXI_PktTypeError] UNKNOWN_EVENT_2 | Ch:0D | Data:000000000
  [15] [PROTOCOL_AXI_PktTypeError] UNKNOWN_EVENT_2 | Ch:0D | Data:000000000
  [16] [PROTOCOL_AXI_PktTypeError] UNKNOWN_EVENT_2 | Ch:0D | Data:000000000
  ... (continues every cycle)
  ```

**Time Window in Waveform:**
- Log file: `val/amba/logs/test_axi_monitor_table_iw4_aw32_mt2_axi4_rd.log`
- Test start: Search for "TEST 4: Orphan Detection"
- Packet flood starts: ~packet #14
- Flood continues: Through Test 5, Test 6, until simulation end

---

### Test Case: `test_axi4_monitor[8-32-8-True-True-id_space]`

**Configuration:**
- ID_WIDTH=8
- ADDR_WIDTH=32
- MAX_TRANSACTIONS=8
- Protocol: AXI4 Read

**Observed:**
- 988 duplicate orphan error packets for Channel ID 0x3D
- Completely blocks completion packets during zero-delay stress test
- Test assertion fails: `assert (8 - 8) >= 90` (expected 90+ packets, got 0)

**Time Window in Waveform:**
- Log file: `val/amba/logs/test_axi_monitor_id_space_iw8_aw32_mt8_axi4_rd.log`
- Orphan flood visible: Search for "Ch:3D" starting around packet #890
- Test 6 failure: Search for "TEST 6: Zero-Delay Stress" followed by "FAIL"

---

## Root Cause Analysis

### Hypothesis

The orphan detection logic in `axi_monitor_trans_mgr.sv` or `axi_monitor_reporter.sv` likely:

1. **Sets an orphan error flag** when detecting orphan data
2. **Fails to clear the flag** after generating the error packet
3. **Continuously reports** the same error every cycle while flag is set

### Likely Location

**File:** `rtl/amba/shared/axi_monitor_reporter.sv` or `rtl/amba/shared/axi_monitor_trans_mgr.sv`

**Look for:**
- Orphan detection logic (likely checks for data_valid without matching cmd)
- Error flag generation for orphan events
- Missing flag clear after packet generation
- Missing single-cycle pulse logic for orphan events

**Search patterns:**
```bash
# Find orphan detection logic
grep -n "orphan" rtl/amba/shared/axi_monitor_*.sv

# Find error event generation
grep -n "UNKNOWN_EVENT_2\|orphan.*error" rtl/amba/shared/axi_monitor_*.sv

# Check event_reported feedback
grep -n "event_reported" rtl/amba/shared/axi_monitor_*.sv
```

---

## Impact

### Test Results

**7/11 tests pass** with workaround (tests that don't trigger orphan conditions)

**4/11 tests fail** due to orphan packet flood:
- `test_axi4_monitor[8-32-8-True-True-id_space]` - FAIL
- `test_axi4_monitor[8-32-16-True-True-id_space]` - FAIL
- `test_axi4_monitor[8-64-8-True-True-addr64]` - FAIL
- `test_axi4_monitor[8-64-16-True-True-combined]` - FAIL

**Pattern:** All failures have ID_WIDTH=8 (larger ID space increases probability of orphan conditions)

### System Impact

- **Monitor bus congestion**: Prevents legitimate event reporting
- **Performance monitoring failure**: Can't track completion events
- **Error analysis corruption**: Real errors masked by orphan flood
- **Downstream processing overload**: Consumer must filter flood

---

## Workaround

### Short-term

**Test-level workaround:**
- Avoid orphan data injection in tests
- Use only valid transaction IDs within table range

**System-level workaround:**
- Disable orphan detection (`cfg_error_enable=0`)
- OR implement downstream packet filter to drop duplicates

### Example Filter (Python/Testbench)
```python
last_orphan_id = {}
def filter_orphan_duplicates(packet):
    if packet.event_code == UNKNOWN_EVENT_2:  # Orphan error
        key = (packet.channel_id, packet.event_data)
        if key in last_orphan_id:
            return False  # Drop duplicate
        last_orphan_id[key] = packet
    return True
```

---

## Fix Strategy

### Required Changes

1. **Add orphan error flag clearing** in `axi_monitor_reporter.sv`:
   ```systemverilog
   // Detect orphan and generate single pulse
   logic orphan_detected;
   logic orphan_reported;

   always_ff @(posedge aclk) begin
       if (!aresetn) begin
           orphan_reported <= '0;
       end else if (orphan_detected && !orphan_reported) begin
           // Generate error packet
           orphan_reported <= 1'b1;  // Set flag
       end else if (orphan_reported && monbus_valid && monbus_ready) begin
           orphan_reported <= 1'b0;  // Clear after packet sent
       end
   end
   ```

2. **Leverage event_reported feedback** (similar to fix in axi_monitor_reporter.md):
   - Use `w_event_reported_flags` to clear orphan error state
   - Ensure orphan errors are single-shot, not continuous

3. **Add orphan error rate limiting**:
   - Track reported orphan IDs
   - Only report each unique orphan once
   - Reset tracking on monitor disable/reset

---

## Verification

### Verification Plan

1. **Unit test**: Inject single orphan data beat, verify exactly 1 error packet
2. **Stress test**: Inject multiple orphan beats with different IDs, verify packet count matches
3. **Persistence test**: Verify no additional packets after initial orphan report
4. **Regression**: Re-run all 11 test configurations, verify 11/11 pass

### Success Criteria

- ✅ Orphan detection generates exactly 1 packet per unique orphan event
- ✅ No duplicate orphan packets on subsequent cycles
- ✅ Completion packets generated normally after orphan event
- ✅ All 11 test configurations pass (currently 7/11)
- ✅ Zero-delay stress test completes with expected packet count

---

## Related Issues

- `axi_monitor_reporter.md` - Event reported feedback bug (FIXED)
  - Similar issue where events weren't cleared after reporting
  - Fix added `event_reported_flags` feedback mechanism
  - Orphan error likely needs similar treatment

---

## Fix Implementation

### Changes Made (2025-10-03)

**File:** `rtl/amba/shared/axi_monitor_reporter.sv`
**Lines:** 295-307

**Root Cause Confirmed:**
The `w_events_to_mark` combinational logic only checked for `TRANS_ERROR` or `TRANS_COMPLETE` states, completely excluding `TRANS_ORPHANED` state. This caused orphaned transactions to be continuously detected and reported every cycle without ever being marked as reported.

**Fix Applied:**
```systemverilog
// BEFORE (lines 295-297):
if ((r_trans_table_local[idx].state == TRANS_ERROR ||
        r_trans_table_local[idx].state == TRANS_COMPLETE) &&
        !r_event_reported[idx] && w_fifo_wr_valid && w_fifo_wr_ready) begin

// AFTER (lines 295-298):
if ((r_trans_table_local[idx].state == TRANS_ERROR ||
        r_trans_table_local[idx].state == TRANS_ORPHANED ||
        r_trans_table_local[idx].state == TRANS_COMPLETE) &&
        !r_event_reported[idx] && w_fifo_wr_valid && w_fifo_wr_ready) begin

// BEFORE (lines 301-302):
if (r_trans_table_local[idx].state == TRANS_ERROR) begin
    w_error_events[idx] = 1'b1;

// AFTER (lines 302-304):
if (r_trans_table_local[idx].state == TRANS_ERROR ||
    r_trans_table_local[idx].state == TRANS_ORPHANED) begin
    w_error_events[idx] = 1'b1;
```

**Verification Results:**
- ✅ All 11 test configurations now pass (previously 7/11)
- ✅ Orphan detection generates exactly 1 packet per unique orphan event
- ✅ No duplicate orphan packets on subsequent cycles
- ✅ Completion packets generated normally after orphan events
- ✅ Zero-delay stress test completes successfully with expected packet counts

**Test Results:**
```
Config [4-32-2-True-True-table]:   6/6 tests passed, 293 packets (271 compl, 22 errors)
Config [8-32-8-True-True-id_space]: 6/6 tests passed, 315 packets (294 compl, 21 errors)
Config [8-32-16-True-True-id_space]: 6/6 tests passed, 313 packets (295 compl, 18 errors)
Config [8-64-8-True-True-addr64]:  6/6 tests passed, 313 packets (292 compl, 21 errors)
Config [8-64-16-True-True-combined]: 6/6 tests passed, 313 packets (295 compl, 18 errors)
...and all other configs PASS
```

---

## Version History

| Date       | Status | Notes |
|------------|--------|-------|
| 2025-10-03 | ✅ FIXED | Added TRANS_ORPHANED to w_events_to_mark logic, all 11 tests passing |
| 2025-10-02 | 🔴 ACTIVE | Initial bug report with detailed reproduction |

---

**Fixed By:** Claude AI (Assistant)
**Priority:** HIGH
**Verification:** Complete - 11/11 tests passing
