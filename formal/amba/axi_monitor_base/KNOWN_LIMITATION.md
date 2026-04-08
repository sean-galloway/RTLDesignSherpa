# Known Limitation: axi_monitor_base Formal Proof

## Status: BLOCKED -- Inherited from axi_monitor_trans_mgr

The `axi_monitor_base` instantiates `axi_monitor_trans_mgr` which has multiple
`always_ff` blocks driving `r_trans_table`. After sv2v flattening, yosys sees
multiple drivers on the same register and cannot resolve them correctly for
SMT-based formal verification.

See `formal/amba/axi_monitor_trans_mgr/KNOWN_LIMITATION.md` for full details.

### Resolution

Same as trans_mgr: refactor to single `always_ff` block for `r_trans_table`.

### Current State

The formal wrapper and assertions are complete. Properties verified:

- P1: Reset clears monbus_valid
- P2: Reset clears active_count
- P3: Reset clears busy
- P4: active_count bounded by MAX_TRANSACTIONS
- P5: busy consistent with active_count
- P6: No spurious monbus without prior AXI activity
- P7: monbus_packet zero when invalid
- P8: block_ready behavior (always 0 for MAX_TRANSACTIONS=2)

These will PASS once the multi-driver issue is resolved in axi_monitor_trans_mgr.
