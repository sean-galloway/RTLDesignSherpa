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

# Sink Data Path - Known RTL Issues

## AXI Timeout Detection Missing

**Severity**: Medium
**Impact**: Timeout errors not detected or reported
**Status**: Missing functionality - placeholder implementation
**Discovery Date**: During RTL review

### Description

AXI timeout detection is not implemented in the sink data path, with only a placeholder assignment that always returns false.

### Location

**File**: `projects/components/dmas/rapids/rtl/macro_beats/snk_data_path_beats.sv` (issue was filed against the retired pre-beats sink_data_path.sv line 283; re-verify against the beats module)

### Current Code (Incomplete)
```systemverilog
assign error_axi_timeout = 1'b0;  // TODO: Add timeout detection from AXI engine
```

### Impact on Functionality

1. **Error Detection**: AXI transaction timeouts are not detected
2. **System Monitoring**: No visibility into stuck AXI transactions
3. **Error Recovery**: Timeout-based recovery mechanisms cannot operate
4. **Debug Capability**: Cannot identify slow or hanging AXI transactions

### Root Cause

Timeout detection logic was not implemented in the initial version, leaving only a placeholder that disables timeout reporting.

### Required Implementation

The timeout detection should:
1. Monitor AXI transaction duration
2. Compare against configurable timeout threshold
3. Assert error when threshold exceeded
4. Provide timeout event reporting via monitor bus

### Fix Priority

**Medium Priority** - Required for robust error handling and system monitoring in production environments with potential AXI slave latency issues.

### Additional Notes

- Error signal is properly connected to higher-level error reporting
- Infrastructure exists for timeout error handling
- Only the detection logic itself is missing

### Re-verified against the beats RTL (2026-09-25) -- THE CITED SIGNAL IS GONE

This entry asks to "re-verify against the beats module". Done, and the result is
that the code it describes no longer exists:

- `error_axi_timeout` -- **0 occurrences** anywhere under `rapids/rtl/`.
- `timeout_detect` -- 0 occurrences.
- `snk_data_path_beats.sv` (280 lines) contains no timeout signalling and no
  `error_*` assigns at all.
- The pre-beats `sink_data_path.sv` the placeholder was filed against is retired
  and absent from the tree.

So the specific defect as written -- "only a placeholder assignment that always
returns false" -- cannot be reproduced, because the placeholder is not there.

**What IS true, stated precisely so this is not mistaken for "fixed".** The sink
data path still has no AXI timeout detection; the gap is real, the cited
implementation is not. Note the word is overloaded here exactly as it was in
STREAM: `scheduler_beats.sv:105-107` DOES carry a full scheduler timeout
(`cfg_sched_timeout_cycles` / `_limit` / `_enable`, `r_timeout_counter`), and the
four `axi_timeout` hits in rapids are all `cfg_axi_timeout_mask`, a MONITOR
packet mask (`monbus_axil_group_2in.sv:107`, `scheduler_group_array_beats.sv:925`).
Neither is sink-path AXI timeout detection. Two mechanisms sharing a word is how
STREAM's monitor timeout went untested for so long.

Needs re-filing against the beats RTL with a current location before it can be
mapped or fixed.
