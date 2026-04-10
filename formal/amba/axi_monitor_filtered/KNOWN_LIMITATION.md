# Known Limitation: axi_monitor_filtered Formal Proof

## Status: BLOCKED -- Inherited from axi_monitor_trans_mgr

`axi_monitor_filtered` instantiates `axi_monitor_base` which instantiates
`axi_monitor_trans_mgr`. The `trans_mgr` has multiple `always_ff` blocks
driving `r_trans_table`, which yosys/sby cannot resolve for SMT-based
bounded model checking.

### Symptom

```
ERROR: Found multiple drivers for \dut.u_axi_monitor_base.trans_mgr.r_trans_table [280].
```

### Resolution

Same as the trans_mgr limitation: refactor `axi_monitor_trans_mgr` to use a
single `always_ff` block for all `r_trans_table` updates. See
`formal/amba/axi_monitor_trans_mgr/KNOWN_LIMITATION.md` and
`formal/amba/axi_monitor_base/KNOWN_LIMITATION.md`.

### Current State

The formal wrapper and assertions are complete. Properties specified:

- P1: Reset clears monbus_valid
- P2: Reset clears active_count
- P3: Reset clears busy
- P4: active_count bounded by MAX_TRANSACTIONS
- P5: busy <=> (active_count > 0)
- P6: monbus_valid handshake -- held until monbus_ready
- P7: cfg_conflict_error is |(pkt_mask & err_select) (combinational)

These will PASS once the multi-driver issue in axi_monitor_trans_mgr is
resolved.
