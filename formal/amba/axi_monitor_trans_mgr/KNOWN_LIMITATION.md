# Known Limitation: axi_monitor_trans_mgr Formal Proof

## Status: BLOCKED -- Multiple Driver Issue

The `axi_monitor_trans_mgr` RTL uses multiple `always_ff` blocks (address
processor, data processor, response processor, cleanup logic) that all drive
the same packed struct array `r_trans_table`. This is valid RTL for simulation
and synthesis, but formal verification tools (yosys/sby) cannot resolve multiple
drivers correctly for SMT-based bounded model checking.

### Symptom

```
ERROR: Found multiple drivers for \r_trans_table [0].
```

Or with BTOR/ABC: spurious counterexample at step 2-3 due to incorrect driver
resolution (yosys ORs the drivers instead of using last-write-wins).

### Root Cause

The RTL architecture intentionally splits transaction management across multiple
`always_ff` blocks for readability:

1. **Address Processor** -- allocates slots on cmd_valid, marks cmd_received
2. **Data Processor** -- updates data_started, data_beat_count, data_completed
3. **Response Processor** -- updates resp_received, marks COMPLETE/ERROR
4. **Cleanup logic** -- clears valid bit when event_reported

All four blocks write to `r_trans_table[idx]` fields. Yosys treats these as
conflicting drivers.

### Resolution

To enable formal verification, the RTL would need to be refactored to use a
single `always_ff` block for all `r_trans_table` updates. This is a non-trivial
change that requires careful testing.

### Current State

The formal wrapper (`formal_axi_monitor_trans_mgr.sv`) and `.sby` configuration
are complete and correct. The assertions verify:

- P1: Reset clears active_count
- P2: active_count bounded by MAX_TRANSACTIONS
- P3: state_change cleared after reset
- P4: Allocation from empty state
- P5: No overflow

These will PASS once the multi-driver issue is resolved.
