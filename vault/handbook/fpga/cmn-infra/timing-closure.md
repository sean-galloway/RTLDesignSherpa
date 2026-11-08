---
title: Timing closure triage
summary: The order to look when timing fails - and what each signature means.
---

# When timing fails, look in THIS order

1. Magnitude sanity. WNS worse than ~2x period is almost never real
   routing: it is either cross-clock analysis or a monster logic cone.
   Do not start floorplanning.
2. report_clock_interaction. Names the offending clock pair immediately.
   Unrelated clocks timed together -> missing set_clock_groups. BUT verify
   before assuming: the -120 ns Genesys case LOOKED like constraints and
   was actually intra-clock ([[priority-logic-depth]] in design/) - the
   report is what settles it, not the hunch.
3. report_timing -max_paths and COUNT LOGIC LEVELS. Hundreds of levels =
   RTL structure (serialized scan, unfactored compare tree); fix the RTL,
   never wallpaper with multicycle/false paths on functional logic.
4. Only when paths are short but slow: congestion/routing. Established fix
   on this repo's A7 builds: pblock floorplanning (stream_char_top.xdc
   precedent, monbus-compressor CAM history) - not pipelining first.
5. Bucketize before fixing: [[timing-triage-tool]] groups thousands of
   endpoint fails into a handful of root cones so you fix causes, not
   symptoms.
6. Before optimizing a lookup on the worst path, ask whether the answer is
   already in the key. A structure that recovers information the signal
   already carries can be deleted outright, and deleting it beats any
   pipelining or depth cut.

*Case (2026-10-18, bridge W12): every shared slave adapter looked each
returning BID/RID up in a per-ID CAM to find the master. Registering the
CAM's free, then halving its depth to 8, each bought under 1 ns (-2.686 to
-1.44 ns on `bridge_mix_e`). The fabric ID was `{master index, id}` all
along, so the master was the ID's top bits. Routing from those bits, with
one outstanding counter, closed `bridge_2x2_axi3_slaves` (+0.001 ns),
took `bridge_mix_e` to -0.669 ns, and saved about 2k LUTs on each.*

Clock targets are a band, not a number: 60-100 MHz acceptable on
characterization builds - take the clean closure (owner rule).

## Closure is margin beyond the placement spread, not a WNS near zero (2026-11-08)

Owner: "the config placement should not be a coin flip. We must be able to
predict the timing." The case: granite's 100 MHz profile landed at +0.003,
0.000, -0.023, -0.159 and -0.013 ns on five builds of near-identical logic,
and each was reported as "closes" or "fails" by the sign. That is reading
the tool's noise. The same netlist moves within a band across placer runs;
on the Nexys A7 DDR2 builds the band measured about 0.2 ns (pumice sys75
SKU +0.083 .. +0.230, granite sys100 as above).

Rules:
- The band is PAID FOR IN THE CONSTRAINT: `set_clock_uncertainty -setup
  0.200` on the system clock in both board XDCs. A report is closed only
  when WNS >= 0 under it. A design that then lands at zero has no margin
  and the next placement will flip it; the fix is structural (shorten the
  binding cone), never another build.
- The band is RE-MEASURED, not assumed: the flow takes `PLACE_DIRECTIVE`
  (AltSpreadLogic_high default, ExtraTimingOpt, Explore); three builds of
  the same netlist give the band, and the kept `reports_*_budget_*`
  directories are where it is written down. When the band grows past the
  budget, the budget follows it.
- Write "closes by X ns under the 0.2 ns budget", never "closes" alone.

What this made of two of the night's results: pumice sys75 FPGA SKU at
+0.083 .. +0.230 is at the edge of the budget, not comfortably closed;
granite sys100 is not closed at all and its binding cone is the bank pick's
hold / select loop (MC-010 row 15). Both are tracked in MC-011.
