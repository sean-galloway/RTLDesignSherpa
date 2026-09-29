# TASK-034: Performance Characterization

> Migrated 2026-09-27 from `vault/Tasks/amba/open.md` as **TASK-014** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Priority:** P2
**Status:** CLOSED 2026-09-28
**Owner:** TBD

**Description:**
Characterize resource utilization and performance impact of monitors.

**Metrics to Collect:**
- [x] Area (LUT, FF, BRAM) per monitor type
- [x] Timing impact (critical path analysis)
- [x] Power consumption (if measurable) -- Vivado vectorless estimate only, reported as a ratio between variants and labelled as such
- [x] Comparison: AXI4 vs AXIL vs APB vs AXIS
- [x] Comparison: With vs without clock gating

**Deliverable:**
- [x] Performance characterization report
- [x] Recommendations for resource-constrained designs
- [x] Optimization opportunities identified

---

---

## CLOSED 2026-09-28

Report: `docs/markdown/rtl-amba/monitor/monitor_characterization.md`, from a
repeatable fixture at `rtl/amba/fpga/` (`tcl/monitor_synth.tcl`, the bridge
fixture's recipe plus `report_power` and a clock-port rule for `pclk`/`clk`;
`bin/monitor_synth_sweep.sh`, the matrix, N Vivados at a time;
`bin/summary_table.py`, the tables). 39 runs, none failed: 30 modules on the
Kintex-7 325T -2 at 6.667 ns and a 9-module subset on the Artix-7 100T -1 at
10 ns, each synthesized, placed and routed out of context; reports under
`rtl/amba/fpga/reports/`.

Headlines, at default parameters: the full AXI monitor is ~7,000 LUTs /
5,200 flops (16 slots) and the lite ~1,100 / 1,030 (8 slots), 6.3x and 5x, on
every AXI4/AXI5 wrapper; 3x on AXI-Lite. Every lite variant meets 6.667 ns
register to register on the Kintex-7 with 0.8-1.5 ns to spare; the 16-slot
full AXI4 monitors do not (CAM slot compare, -0.17 rd / -1.55 wr). Clock
gating costs 20-80 LUTs and 0.15-0.45 ns and buys nothing the vectorless
estimate can see. APB/WB monitors 570-620 LUTs; the four-client arbiter
1,800; a group 1,700-2,000 with 1.2-1.4 ns of slack after ISSUE-001. Every
out-of-context miss in the "incl. I/O" column is a `cfg_*` primary-input path
under the 30 % I/O budget, not the block. Recommendations in the report:
default to the lite, cut slots if the full monitor must run at 150 MHz,
budget the group once per subsystem, register cfg inputs beside the block,
leave `_cg` off unless idle power is the goal and measure that on silicon.

One finding filed: monitor-lite ISSUE-003, the AXIS lite misses 10 ns on the
Artix-7 register to register (events and drop count in one cycle, the shape
the AXI lite fixed under ISSUE-002). The whitepaper (TASK-036) links the
report from its cost section.
