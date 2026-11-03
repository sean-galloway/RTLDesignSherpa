# ISSUE-027: pumice HEAD no longer closes its 50 MHz shipping point -- the arbiter classify cone at -2.84 ns

> Source: pumice TASK-047 (2026-11-03), the A/B board builds for the dual-issue
> row lane. The HEAD side of every pair (text at `79788fd8e`, scratch
> `git archive` trees, clean Vivado runs) fails the board's own frequency.
> Related: pumice TASK-060 (the CAM rewrite that took the board from 75 to 50
> MHz; its 50 MHz bitstream closed at +0.029 ns on 2026-10-27, the build in
> `build-perf/fpga/reports/`), TASK-047 (results log), granite TASK-007 (the
> narrow pack, +331 LUT in the shared AXI plane, landed 2026-11-03).

**Priority:** P1 -- the shipped bitstream is from the 10-27 text; any new
pumice bitstream from HEAD fails timing at the board clock.
**Status:** CLOSED 2026-11-03 -- the arbiter's QoS max was a 16-stage serial
ripple at the end of the cone; a balanced tree closes 50 MHz at +0.057 ns
(see Resolution).
**Owner:** TBD

## What is seen

Nexys A7 (xc7a100t), `build-perf`, FR-FCFS core, four injectors, HEAD:

| build | WNS | failing endpoints | LUT / FF |
|---|---|---|---|
| 2026-10-27 shipped, `PUMICE_SYS_50=1` | +0.029 ns | 0 | -- |
| HEAD, `PUMICE_SYS_50=1` (combiner on, as shipped) | **-2.843 ns** | 24 | 45 652 / 35 387 |
| HEAD, `PUMICE_SYS_75=1`, combiner on | -9.794 ns | 4 283 | 45 853 / 35 350 |
| HEAD, `PUMICE_SYS_75=1`, `WR_MERGE_EN = RD_MERGE_EN = 0` | -9.951 ns | 2 385 | 44 561 / 35 108 |

All 24 failing endpoints at 50 MHz are in `g_arbiter.u_arbiter`, one path
family: `r_wr_pop` / `r_rd_pop` (STAGE-1a population) -> STAGE-1b `arg_sel`
-> the in-flight shadows -> classify -> `r_wr_col_q` / `r_wr_act_q` /
`r_wr_pre_q`, 27 logic levels. It is the route-bound cone TASK-060 measured at
22-24 levels (logic about 3 ns, route 12-16 ns), now three to five levels
deeper and failing at 20 ns.

## Magnitude and split (`bin/vivado_timing_failures.py`, 2026-11-03)

Every violation of each build's `timing_failing_setup_full.txt`, binned by
slack and grouped into cones by start / end instance:

| build | failing | worst | TNS | median | < -5 / -5..-2 / -2..-0.5 / -0.5..0 ns | route share |
|---|---|---|---|---|---|---|
| HEAD 50 MHz, combiner on | 24 | -2.843 | -65 | -2.75 | 0 / 24 / 0 / 0 | 83 % |
| HEAD 75 MHz, combiner on | 4 283 | -9.794 | -6 474 | -1.44 | 25 / 1 057 / 2 487 / 714 | 83 % |
| HEAD 75 MHz, combiner off | 2 385 | -9.951 | -1 477 | -0.35 | 24 / 14 / 843 / 1 504 | 86 % |
| 10-27 text 75 MHz, combiner on | 4 221 | -5.630 | -3 862 | -0.71 | 22 / 518 / 2 037 / 1 644 | 86 % |

**Route-dominated, with a small logic growth.** The worst cone in every build
is the arbiter to itself (`g_arbiter.u_arbiter -> g_arbiter.u_arbiter`, 51-56
endpoints at 75 MHz, all 24 at 50 MHz). Its worst path is **3.8 ns of logic
and 18.9-19.3 ns of route** at HEAD, against 3.3 ns logic / 15.5 ns route on
the 10-27 text: +0.5 ns of logic (23-24 levels to 27) and **+3.7 ns of
route**. Route is 82-84 percent of that cone's delay in every build and
83-86 percent of all failing delay. At 50 MHz this is the only cone that
fails, and it misses by 2.84 ns, so a few more levels of logic routed across
a 72 percent full part are enough.

Beyond the arbiter, the 75 MHz picture is the TASK-060 one: about 990 write
CAM endpoints from the arbiter's fire (-4.4 ns, 77 percent route) on the
combiner-on text; with the combiner off, rd CAM -> page policy (-2.1),
wr CAM -> rd CAM (-2.0) and bank timers -> arbiter (-1.9), all 74-85
percent route. The 10-27 75 MHz build failed the same cones, so the new
problem is the arbiter's own cone getting about 4 ns longer, not a new cone.

The workbooks (raw / bins / cones) are in the session scratchpad, `tb_h50.xlsx`,
`tb_h75c.xlsx`, `tb_h75nm.xlsx`; the inputs are clean scratch-tree builds of
`79788fd8e`, and the 10-27 input is `build-perf/fpga/reports_sys75_2026-10-27/`.

## What it is not

- Not the combiner decision: 75 MHz with both merge enables off fails the
  same cone by about the same amount (-9.95 against -9.79).
- Not the TASK-047 row lane: those builds are HEAD without it. With the lane
  the cone moves by under a nanosecond either way (50 MHz -3.689, 75 MHz
  combiner-off -9.391), inside place-and-route variance on this path.

## Next step

Bisect by build between the 10-27 text and HEAD (worktree per point, never
the shared build dir), at `PUMICE_SYS_50=1`. Candidates since 10-27: the
read combiner's rd CAM changes (TASK-060), close-on-drain predicate terms
(TASK-044 / granite TASK-003 items in the shared arbiter), the Ocelus plane
plumbing (TASK-062), and the narrow pack in the shared AXI plane (granite
TASK-007). Both grew: the bisect should look for the
commit that added the three levels (likely a classify or shadow term in the
shared arbiter) and for the LUT growth that stretched the routes; the
lasting fix for a cone that is 83 percent wire is the arbiter / CAM
restructure TASK-060 left as the owner's call.

## Resolution (2026-11-03)

Not bisected: the bucketing said the cone, so the cone was read. The arbiter
alone, synthesized to ASAP7 with its classify nets kept
(`projects/asic-trials/timing_characterization/work/synth_module.py`, TT,
1 ns), put the worst path at 3.27 ns over 118 cells: classify done at 1.12 ns
(`rd_col_me`), then 2.15 ns of one repeated compare-select pattern, 16 deep.
That is `qos_top` in `mc_cmd_arbiter`, the STAGE-1a QoS filter after
classify and the order overlay. It found the highest AxQOS with a serial
`if (q > best) best = q` walk over all 16 entries. `sched_qos_en_i` is a
runtime CSR, so the logic is built (and on the critical path) whether or not
QoS is on. The Vivado path's last ~15 LUT levels, inside the write CAM's
hierarchy where the QoS values come from, plus one CSR cell, were the same
walk.

**Fix:** a balanced pairwise max (clog2(NUM_ENTRIES) compare-select levels).
Proven equal to the walk with a yosys SAT miter for NUM_ENTRIES 16, 8, 5 and
3; a mutated tree fails the miter.

| measure | before | after |
|---|---|---|
| arbiter alone, ASAP7 TT, worst reg-to-reg | 3.27 ns, 118 cells | **1.83 ns, 62 cells** |
| board, 50 MHz, combiner on (the shipping point) | -2.843 ns, 24 failing | **+0.057 ns, 0 failing**, hold clean |
| board, 50 MHz, + TASK-047 lane | -3.689 ns, 40 failing | **+0.134 ns, 0 failing** |
| board, 75 MHz, combiner on | -9.794 ns, 4 283 failing | -5.158 ns, 2 480 failing |
| board LUT / FF (50 MHz) | 45 652 / 35 387 | 45 248 / 35 287 |

75 MHz is back to the 10-27 picture (-5.63 then): the arbiter
population -> STAGE-1b -> classify loop (65 endpoints, 3.9 ns logic / 14.5 ns
route) and the bank timers -> write CAM strobes TASK-060 named. The 50 MHz
margin is thin and on that same loop. The next cut is moving the STAGE-1b
selection's in-flight shadows (`w_if_*_sel`, the per-entry and tCCD terms) out
of classify into STAGE-1b against the pre-pick registers. Not done here.

Verification: pumice 222 / 222 at both geometries, common-ip macro 36 + 3
xfail, `formal/mc_common/mc_cmd_arbiter` prove / cover / dual / dual_cover
pass, lint clean.

