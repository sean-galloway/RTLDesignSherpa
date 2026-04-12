# stream_core -- DEFERRED

## Status: DEFERRED (sv2v builds, yosys flatten fails)

## Blocker: Constant-driven output ports during yosys flatten

The sv2v flattening succeeds (7108 lines of Verilog), but yosys fails during
the `flatten` pass with:

```
ERROR: Cell port stream_core.u_rd_axi_skid.fub_axi_ruser (axi4_master_rd) is connected to constants: 1'0
```

### Root cause

stream_core instantiates `axi4_master_rd` with `AXI_USER_WIDTH=1`. Internally,
the AXI skid buffer has a `fub_axi_ruser` output that gets constant-optimized
to 1'b0 when the user width is minimal. Yosys's `flatten` pass treats this as
a hard error (output port driving constants).

Additionally, `descriptor_engine` has a multi-driver issue where
`r_descriptor_error` is written from two separate `always_ff` blocks (lines
651 and 807 in the RTL).

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
