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

`projects/components/fabric-gen-ip/bridge/dv/tests/monitor_stress_common.py` programmed
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

## Trap: a field named `count`

`RegisterMap._initialize_state` treats a register entry with a `count` key as
an ARRAY (`[default] * count`), so an RDL field named `count` makes the
generated regmap fail to load with `int() argument must be ... not 'dict'`
(reed-solomon loop harness, 2026-09-30: `INJ_CFG.count` became `errors`).
The same goes for any field named like the entry's own keys: `name`, `offset`,
`address`, `size`, `sw`, `type`, `default`. Pick another name.

## Trap: an RDL `singlepulse` is NOT one cycle through the APB shim

`peakrdl_to_cmdrsp` HOLDS the register-block request until the block acks, on
purpose: its header records that reducing it to a one-cycle strobe broke every
read through the bridge (2026-08-17, reverted). So a `singlepulse` field
written through `apb4_to_peakrdl` can be asserted for more than one cycle, and
any consumer that wants exactly one cycle must take the RISING EDGE in the
harness.

What it cost (reed-solomon loop harness, 2026-09-30): CTRL.start arms the
pattern generator and its checker from the same wire. Held two cycles, the
generator left IDLE on the first and began advancing its LFSR while the
checker reloaded its seed again on the second. In bypass mode, where the two
sit on the same cycle, that desynchronised them and every beat mismatched. The
codec paths hid it, because the decoder's latency means no beat reaches the
checker until long after the pulse. A harness that only tests through its DUT
will not see this; the bypass path is what exposed it.

