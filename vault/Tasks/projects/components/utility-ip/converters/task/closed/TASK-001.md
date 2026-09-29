# TASK-001: upsize paths now support mid-wide-word INCR burst starts

> Migrated 2026-09-27 from `vault/Tasks/projects/components/utility-ip/converters/closed.md` as **CONV-006** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-26 (opened 2026-08-25) — implemented, not just documented
**Priority:** was P2, raised on review: "if a narrow burst starts in the
middle of wide data, BEs must be used with the data being loaded in the
middle" — correct, and now the behavior.

What shipped (RED tests first on both paths):

- `axi_data_upsize` gained `start_lane`: a burst's first narrow beat
  lands at its ADDRESSED lane (data and WSTRB shifted; leading slots
  '0 = byte-disabled, not clobbered); later wide groups start at lane 0.
- `axi4_dwidth_converter_wr` (upsize): AWLEN counts the lane
  (ceil((lane + narrow_beats)/RATIO)), AWADDR passes through unaligned
  (legal AXI — first beat partial in its container), and an AW-lane
  queue feeds the packer. The queue pops on the NARROW side's last
  beat — a wide-side pop raced back-to-back bursts (burst B's first
  narrow beat sampling burst A's stale lane; caught by the bridge
  parallel_storm seed 1787764509, replayed deterministically).
- `axi_data_dnsize` gained `start_lane` (TRACK_BURSTS): the burst's
  first wide word slices from the addressed lane.
- `axi4_dwidth_converter_rd` (upsize): ARLEN counts the lane; issued
  address still aligns down (slave returns whole wide words); the
  burst-length FIFO carries {lane, len}.
- FIXED/WRAP keep the wide-aligned requirement, asserted in sim.

Pinned regressions: `test_unaligned_wide_start` in BOTH dwidth TBs
(lane-correct data + WSTRB + AWLEN/ARLEN; RED against the old RTL on
every upsize config). The DV bridge TB went back to master-width
addressing so unaligned upsize traffic is exercised end-to-end.

Gates: converters run-all-full-parallel 112/112, DV bridge suite 8/8
with storms hammered, RDS bridge suite green.

---
