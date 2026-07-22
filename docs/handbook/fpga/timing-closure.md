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

Clock targets are a band, not a number: 60-100 MHz acceptable on
characterization builds - take the clean closure (owner rule).
