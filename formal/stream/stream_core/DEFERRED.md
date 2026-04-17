# stream_core -- DEFERRED

## Status: DEFERRED (sv2v builds, yosys flatten name collision)

## Fixed (2026-04-17)

1. **descriptor_engine multi-driver on r_descriptor_error** -- FIXED
   Consolidated APB address-0 error detection into main FSM block.

2. **Constant-driven ruser/buser ports** -- FIXED
   Changed `stream_core.sv` to assign channel ID to `fub_rd_axi_ruser` and
   `fub_wr_axi_buser` instead of tying to `'0`.

## Remaining Blocker: yosys flatten name collision

After the above fixes, sv2v and yosys `prep` succeed through hierarchy/proc/opt,
but the SMT2 backend reports:

```
ERROR: Found multiple drivers for \fub_rd_axi_aruser.
```

### Root cause

After yosys flattens two `axi4_master_rd` instances (desc and rd data paths),
the internal `fub_axi_aruser` wire names collide. The desc monitor ties
`.fub_axi_aruser(1'b0)` while the data path ties `.fub_axi_aruser(fub_rd_axi_aruser)`.
Yosys flatten merges these into one wire with two drivers.

### Files created

All formal infrastructure files are complete and ready for use once the blocker
is resolved:

- `Makefile` -- sv2v with sed preprocessing for monitor_pkg imports
- `stream_core.sby` -- SymbiYosys configuration (depth 15 BMC)
- `formal_stream_core.sv` -- Formal wrapper with properties

### Properties defined (ready to verify)

- P1: Reset clears system_idle to 1
- P2: Reset clears per-channel idle signals (scheduler_idle, descriptor_engine_idle)
- P3: Reset clears all AXI output valid signals
- P4: Reset clears scheduler error flags
- P5: Reset clears monitor bus valid
- P6: system_idle implies all scheduler_idle bits set

### Resolution path

1. Fix `descriptor_engine.sv` multi-driver on `r_descriptor_error`
   (consolidate into single always_ff block)
2. Fix constant-driven `ruser`/`buser` ports by adding proper user signal
   passthrough in `axi4_master_rd.sv` and `axi4_master_wr.sv`, or by
   setting `AXI_USER_WIDTH` >= 2 in the formal wrapper

### sv2v workaround for monitor_pkg

The Makefile includes a sed preprocessing step that replaces `import monitor_pkg::*`
with individual sub-package imports to work around sv2v's typedef re-export
ambiguity. This workaround is proven to work (the flat file builds successfully).
