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
