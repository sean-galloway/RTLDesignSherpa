---
title: Registers by name
summary: PeakRDL regmaps; hardcoded offsets are forbidden everywhere.
---

# Registers are accessed by NAME

- Every register access - sim TB, host program, board script - goes through
  the generated regmap (`*_regmap.py`) via
  TBClasses.apb.register_map.RegisterMap. Hardcoded offsets are forbidden:
  they broke silently when the monitor block moved to 0x1000, and
  by-name access is what makes address-map changes split-proof.
- Regenerate ONLY via `bin/peakrdl_generate.py` - it emits RTL + docs +
  regmap in lockstep; raw `peakrdl regblock` desyncs the regmap.
- RDL gotcha: `f[N]` means width N; a single bit at position 8 is `f[8:8]`.
- This rule is what lets one host program run identically in sim and on the
  FPGA ([[uart-harness]] in fpga/) - the harness resolves names at runtime,
  so sim and silicon cannot disagree about the map.

## Case: the bridge stress flow's three constants (2026-09-26)

`projects/components/bridge/dv/tests/monitor_stress_common.py` programmed
the regblock fixture's MON_GROUP window at `0x90/0x94/0x98`, written by
poking `s_cfg_axil_*` by hand. It passed for weeks because nothing above
those registers changed. Swapping the bridge monitors for the lite dropped
the perf-window registers from the generated RDL, every register below
moved down by one, the constants wrote the wrong three registers, and the
fixture's monitor test failed with an empty trace path -- no error named
an address, the symptom was "no packets".

Two halves to the fix, both required. The GENERATOR now emits
`<bridge>_cfg_regmap.py` beside every regblock it produces
(`cfg_rdl_generator._emit_regmap`, through `bin/peakrdl_generate.py
--regmap`), so a by-name map exists for generated register blocks too. The
FLOW loads it with `RegisterMap` and writes through the AXI-Lite master BFM
(`create_axil4_master_wr(..., prefix='s_cfg_axil_')`). A generated register
block with no regmap is a block nobody can address by name, and a test that
pokes valid/ready is a test that will be wrong about timing one day
([[bfm-usage]]).
