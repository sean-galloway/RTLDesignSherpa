# Deferred: axi4_interconnect_2x2_mon Formal Proof

## Status: DEFERRED -- Too many dependencies and incomplete RTL

## Reasons for Deferral

### 1. Depends on _mon_cg (clock-gated) variants, not _mon

The interconnect instantiates `axi4_master_wr_mon_cg` (line 391), not the
plain `axi4_master_wr_mon`. The CG variants have documented RTL bugs
(dead clock gating code, synthesis-unsafe combinational clock suppression)
that make them unsuitable for formal verification until fixed. See:

    formal/amba/axi4_master_rd_mon_cg/KNOWN_LIMITATION.md

### 2. Incomplete port connections

The RTL has a comment "Similar routing logic would be needed for all other
channels..." (line 372). Only the AW channel routing and partial ready
back-propagation are implemented. The W, B, AR, and R channel routing
logic is missing, meaning the module is not functionally complete.

### 3. Uses `reset_defs.svh` macros with `ALWAYS_FF_RST`

The arbiter logic (line 448) uses the `ALWAYS_FF_RST` macro, which adds
an sv2v preprocessing complication on top of the already complex
dependency chain.

### 4. Large dependency tree

Would need all 4 `axi4_*_mon_cg` modules (each pulling in their own
AXI wrapper + axi_monitor_filtered + full monitor infrastructure), plus
the `amba_clock_gate_ctrl` module, plus internal routing logic. The
resulting flat Verilog would be very large for tractable BMC.

## Prerequisites for Unblocking

1. Fix CG wrapper bugs (dead clock gating, synthesis-unsafe ICG)
2. Complete the interconnect routing logic (W, B, AR, R channels)
3. Create formal proofs for `axi4_*_mon_cg` wrappers first
4. Then create the interconnect proof as a composition

## What Was Proven Instead

The 4 non-CG _mon wrappers were formally proven (prove + cover PASS):

| Module | Prove | Cover | Prove Time | Cover Time |
|--------|-------|-------|------------|------------|
| `axi4_master_rd_mon` | PASS | PASS | 2m11s | 7m55s |
| `axi4_master_wr_mon` | PASS | PASS | 5m15s | 0m51s |
| `axi4_slave_rd_mon`  | PASS | PASS | 4m05s | 1m32s |
| `axi4_slave_wr_mon`  | PASS | PASS | 5m30s | 4m54s |

Properties verified on each:
- P1: Reset clears monbus_valid
- P2: Reset clears busy (with AXI valid signals constrained to 0 during reset)
- P3: Protocol field is AXI (3'b000) when monbus_valid
- P4: active_transactions bounded by MAX_TRANSACTIONS
- P5: cfg_conflict_error is combinational: |(pkt_mask & err_select)

These cover the core monitor integration path that the interconnect
would compose.
