# ISSUE-004: one board config reports zero ingress starvation where every other reports ~200

**Status:** CLOSED 2026-09-28 (closing note at the end); was open 2026-09-27, split
out of ISSUE-001 when that closed.

`ch8_b4_bpoff_seed0xA5A5A5A5` reports `sin starv=0, util=1.000` while all 19
other configs in the same sweep report ~197-205. It reproduces EXACTLY across
two independent sweeps (deterministic, not jitter) and sits at position #7 of
20 (not first-arm-after-reset). The sink re-arm quirk documented in
`run_characterization.py` was the obvious suspect and the ordering does not
support it.

Since ISSUE-001's fix the ingress window closes on its own beat target, so the
~200-cycle tail is gone from every row; whether this config's zero was a
different mechanism (window never opening, meter cleared late, a re-arm race)
has to be re-measured on the board with the new harness before it is chased.
Do not paper over it: if it still reads differently from its neighbours after
the re-measurement, capture the meter CSRs and the observer counters for that
row and compare beat by beat.

---

**CLOSED 2026-09-28.** Re-measured on the Genesys 2 with the ISSUE-001 harness
(bitstream built from 3404a6d0a): the 20-config sweep that produced the zero
now reads `sin starv=1, util=0.970` on `ch8_b4_bpoff_seed0xA5A5A5A5`, exactly
like its three b4 neighbours, and every one of the 20 rows shows the same
single starvation cycle. Then an ILA capture on that configuration
(`tcl/capture_ila_issue004.tcl`, ILA build of the same design with the
observation-window nets marked, trigger on the GO pulse): GO at sample 128,
the ingress window arms at 129, the generator presents the first beat at 129,
the window opens at 130, 32 handshakes at line rate 129..160, the window
closes at 162, and the one starvation cycle is 161 -- the cycle between the
last accepted beat and the registered close. The sink's write side goes busy
at 318, 190 cycles later, which is the launch cost the old busy-keyed window
had been charging to ingress. Nothing about this row differs from its
neighbours; the old zero was the previous harness's window not opening on
that run, and the harness rewrite in ISSUE-001 removed that mechanism.

The single trailing starvation cycle is a property of the registered close
(the meter sees ready-and-idle for one cycle before the freeze lands). It is
bounded at 1 on every row and left as is.
