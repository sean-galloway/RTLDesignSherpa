<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — dropped (abandoned / superseded / won't do)

---

## TASK-082: build-obs timing margin has collapsed to 13 ps across three builds
**Status:** dropped 2026-09-19 — "Obs margin is fine" (Sean). Filed the same
day it was dropped; the owner's call is that a thin positive margin on this
build is acceptable, so it is not a risk to track.

Kept for the measurements, which are real and may save someone a rebuild.
build-obs post-route WNS across three builds:

| build date | WNS | post-route LUT |
|---|---|---|
| 2026-09-07 (`stable-obs`) | +2.191 ns | 183 257 = 89.92% |
| 2026-09-09 | +1.423 ns | — |
| 2026-09-19 | +0.013 ns | 184 135 = 90.35% |

Area grew ~878 LUTs (+0.43 pp) and timing endpoints moved 416 938 -> 417 064
(+0.03%) across that span. On the same day and the same RTL, build-mon closed
+0.816 ns at 69.44% LUT and build-perf +0.803 ns at 33.34% — only obs is
marginal, and obs is the build that enables BOTH observers with every monitor
cone, already pinned to 4 channels because 8 hit 99.33% LUT and could not
place ([[project_stream_genesys2_design_point]]). At 90% occupancy P&R
outcome is strongly stochastic; this run dipped to WNS -0.500 mid-route over
a 2h48m build before recovering.

One factual note recorded without recommendation: `make bitstream` does not
gate on timing — the only slack check is in `fpga/tcl/synth_only.tcl`, not
`build_all.tcl` — so a negative close writes a `.bit` and reads as success.
Anyone reading a board result off this build should check `make timing`
rather than infer closure from the build exiting 0.
