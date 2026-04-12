# stream_core_mon -- DEFERRED

## Status: DEFERRED (sv2v builds, yosys flatten fails)

## Blocker: Same as stream_core -- constant-driven output ports during yosys flatten

stream_core_mon has the same architecture as stream_core but with AXI monitors
always enabled (no USE_AXI_MONITORS toggle). It encounters the same yosys
`flatten` error from constant-driven `ruser`/`buser` ports and the same
`descriptor_engine` multi-driver issue.

### Files created

All formal infrastructure files are complete:

- `Makefile` -- sv2v with sed preprocessing (adds axi4_master_wr_mon.sv deps)
- `stream_core_mon.sby` -- SymbiYosys configuration (depth 15 BMC)
- `formal_stream_core_mon.sv` -- Formal wrapper with properties

### Properties defined (ready to verify)

- P1: Reset clears per-channel idle signals
- P2: Reset clears all AXI output valid signals
- P3: Reset clears monitor bus valid

### Resolution path

Same as stream_core -- see `formal/stream/stream_core/DEFERRED.md`
