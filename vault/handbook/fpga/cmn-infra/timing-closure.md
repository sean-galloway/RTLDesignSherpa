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
