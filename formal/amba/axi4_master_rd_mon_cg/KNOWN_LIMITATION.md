# Known Limitation: axi4_master_rd_mon_cg Formal Proof

## Status: BLOCKED -- Inherits multi-driver issue from axi_monitor_trans_mgr

The `axi4_master_rd_mon_cg` module instantiates `axi4_master_rd_mon`, which
in turn instantiates `axi_monitor_base` -> `axi_monitor_trans_mgr`. That
lowest module is known-BLOCKED in formal due to multiple `always_ff`
blocks driving a shared transaction table; see:

    formal/amba/axi_monitor_trans_mgr/KNOWN_LIMITATION.md

Until the underlying trans-mgr multi-driver issue is resolved, the
monitor-enabled CG wrappers cannot be formally proven end-to-end.

## Additional bugs found during CG review (2026-04-02)

While investigating the CG wrapper for formal proofs, TWO real RTL bugs
were identified in this file that should be tracked and fixed:

### BUG #1 -- Clock gating is entirely dead code

Lines 182-184 declare `aclk_monitor`, `aclk_reporter`, `aclk_timers`,
and lines 271-317 compute them conditionally based on activity, but
line 339 hardwires the inner monitor instance to the ungated `aclk`:

```systemverilog
) axi4_master_rd_mon_inst (
    .aclk                    (aclk),        <-- SHOULD BE aclk_monitor
    ...
```

The gated clocks are NEVER connected to the inner module. All of the
clock-gating logic is unreachable dead code. `cg_monitor_gated`,
`cg_reporter_gated`, `cg_timers_gated`, `cg_cycles_saved` are purely
cosmetic outputs -- they report the intent of gating but no clock is
actually gated.

### BUG #2 -- Clock-gating implementation is synthesis-unsafe

Even if the outputs were wired up, lines 276-282 (and the reporter /
timer equivalents) gate the clock via a pure `always_comb` AND:

```systemverilog
always_comb begin
    if (cg_monitor_en && !monitor_activity) begin
        aclk_monitor = 1'b0;     <-- combinational clock suppression
        cg_monitor_gated = 1'b1;
    end else begin
        aclk_monitor = aclk;
        cg_monitor_gated = 1'b0;
    end
end
```

This is NOT a valid clock gate. Real ICG cells (see `rtl/common/icg.sv`)
use a latch on the enable signal to prevent glitches on the gated clock.
The combinational AND used here will glitch every time `cg_monitor_en`
or `monitor_activity` changes during a high clock phase. If this path
were wired in, it would cause metastability and unpredictable FF
behaviour.

### Fix recommendation

Replace the hand-rolled gating in lines 271-317 with
`amba_clock_gate_ctrl` (the same primitive used by the non-mon CG
wrappers), and actually connect its `clk_out` to the inner monitor
instance's `.aclk` port.

## Why no formal assertions are shipped

Because the module inherits the BLOCKED multi-driver issue, sby/yosys
cannot load the design at all. A formal wrapper would fail during
`read -formal` / `prep` before any property could be exercised. The
bugs above are documented here so the fix is not lost, and a future
formal proof can be added once trans_mgr is un-BLOCKED and the gating
is rewired.
