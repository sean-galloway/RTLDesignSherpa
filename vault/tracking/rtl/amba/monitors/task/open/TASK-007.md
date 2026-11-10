# TASK-007: assess the monitor family for the FPGA-review treatment (jet_monlite, the monlite wrappers, the Ocelus monitors)

**Priority:** P3
**Status:** OPEN
**Owner:** TBD
**Filed:** 2026-11-10, owner direction while closing jet ISSUE-002.

## Why

The 2026-11 FPGA microarchitecture reviews of the memory controllers
(memory-controllers MC-004/005, granite -2,042 LUT) and of cache-ip
(common-ip TASK-001, jet TASK-003) found the same few things over and over:
arrays that an async reset dissolved into flops, combinational reads of
arrays that should have been RAM-shaped and registered, per-entry logic that
a shape change made free, and attributes that never reached the tool. Every
measured rig carries monitors -- `jet_monlite` and the `axi4_*_monlite`
wrappers on the cache-ip rigs, the full Ocelus `axi_monitor_*` family with
its transaction CAM and reporters on the STREAM/RAPIDS rigs -- and none of
them has been looked at with that eye. The owner, deciding jet ISSUE-002
(2026-11-10): leave the drop limit as the error bar, but find out whether the
monitors themselves would benefit from FPGA optimisation.

## What

An assessment first, fixes only where the measurement says so:

- Measure what the monitors cost on bitstreams that already exist:
  `area-measure-by-hierarchy` on the routed cache-ip rigs (jet bin 14 /
  amber bin 9 reports, `jet_monlite` + the rd/wr monlites + the monbus
  arbiter) and on a STREAM or RAPIDS Genesys2 build (Ocelus base, trans_mgr,
  trans_cam, the reporters, monbus groups). LUT / FF / LUTRAM / BRAM and
  whether any monitor path is on the critical list.
- Read each monitor module against the review checklist: storage arrays
  behind an async reset, combinational array reads, `ram_style` attributes,
  reset fan-out, one-hot vs encoded state, per-entry compare trees in the
  transaction CAM.
- For each candidate, a worktree A/B build with a golden-copy equivalence
  (the MC-004/005 method), the way the review did it; nothing changes without
  a before/after pair on the same tree.
- Write the findings into the module docs and `vault/handbook/fpga`; file a
  bug or task per real finding. If the measurement says the monitors are
  already cheap, say so with the numbers and close.

Scope: `rtl/amba/ocelus/*` (axi_monitor_base, _trans_mgr, _trans_cam,
reporters, axi_monitor_lite, axis_monitor_lite, cxs_monitor_lite,
axi4ace_snoop_monitor_lite), the `*_monlite` wrappers in axi4/axil4/axis4/cxs,
and `projects/components/cache-ip/jet-mesi-l1/rtl/fub/jet_monlite.sv`
(amber's monlite is the same shape). The observer rule holds throughout
([[observers-do-not-drive]]): no change may perturb the measured path, and the
present-vs-absent pins in the cache-ip DV stay green.

## Done when

- A cost table per monitor module on at least one cache-ip and one
  STREAM/RAPIDS bitstream, with the critical-path check.
- Each candidate either A/B-measured and fixed (own bug/task, closed) or
  recorded as not worth it with its number.
- jet ISSUE-002's error bar is unchanged by any of it (drop bin still named,
  commit width untouched unless this task's measurement reopens it).
