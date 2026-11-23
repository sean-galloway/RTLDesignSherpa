# TASK-007: Add and FPGA-optimize passive full-monitor observers

**Priority:** P2
**Status:** ACTIVE 2026-11-22 -- owner approved native execution.
**Owner:** Kimi Code
**Filed:** 2026-11-22
**Spec:** `docs/superpowers/specs/2026-11-22-full-monitor-fpga-observers-design.md` (commit `c334d64a0`)
**Plan:** `docs/superpowers/plans/2026-11-22-full-monitor-fpga-observers.md`

## Verification ledger

- Pre-extraction clean AXI observer FULL: **41/41 PASS** in 59.37 s
  (`task1-baseline.log` in the plan workspace).
- Post-extraction clean AXI observer FULL: **41/41 PASS** in 60.57 s;
  filelist registry PASS. Four initial hierarchy-probe failures were corrected
  by anchoring the sustained-consumer scenario to `u_core`.
- The misc observer Make targets live in `dv/tests/fub`, not the parent
  `dv/tests` directory; the latter discovers only `error_injector`.
- Full-monitor refusal accounting: clean FULL **3/3 PASS** at depths 4/8/16;
  unbanked and banked prove/cover PASS with all seven covers reached. Removing
  `cmd_ready` from the refusal equation fails `ap_held_command_not_refused`.
  Formal-only outputs carry the real pending/allocation predicates because
  Yosys treats hierarchical references as undriven implicit wires.
- Unoptimized full observer RTL baseline: `be7f8e891`. Clean gate **23/23 PASS**
  (17 existing lite cells plus six full register/traffic/all-cone cells).
- Full observer passivity/feature gate: initial **31/34**, then targeted fixes
  for test stimulus/runner structure passed **3/3**; all fixed-cycle saturation,
  ID-slice, same-cycle banked write, and clear/reuse behaviors passed. Base and
  filtered prove/cover PASS; base cover uses its passive-snoop configuration.
- Final all-level observer matrix: **82/82 PASS** in 340.08 s, including full
  performance/debug, full reset/reissue, all passivity configurations, and all
  banked same-cycle write levels. Final base/filtered clean prove/cover PASS.
- FPGA baseline `be7f8e891`: all **8/8 rows**, zero unrouted nets. Full feature
  master is 21,658 LUT / 16,876 FF / 444 LUTRAM / -1.046 ns on Kintex and
  21,976 / 16,866 / 444 / -3.868 ns on Artix. Deployment full is
  33,571 / 10,313 / 288 / -14.841 ns and 33,544 / 10,305 / 288 / -30.753 ns.
  Depth-8 hierarchy selects CAM logic first: 3,845 LUT read and 4,744 write;
  reporter snapshots are the second candidate. Full tables and reproduction
  commands are in `monitor_characterization.md`.
- Experiment 1 (CAM ID/payload reset removal): **REJECTED**. Kintex
  +379 LUT / -3 FF / +0.158 ns; Artix +457 LUT / +7 FF / -0.553 ns, with no
  LUTRAM change and zero unrouted nets. Candidate verification was CAM FULL
  7/7, trans-manager 3/3, and both prove/cover runs PASS; payload mutation
  fails the new clear/reuse test. RTL reverted, test and negative A/B retained.
- Experiment 2 (reporter snapshot reset removal): **REJECTED**. Kintex
  +35 LUT / +1 FF / +0.056 ns; Artix +44 LUT / +9 FF / -0.195 ns. Candidate
  reporter prove/cover and observer FULL **84/84 PASS**. A zero-clock reset
  mutation replayed stale completion; guarded source stayed quiet and recovered.
  RTL reverted, normal/zero-clock reset tests and negative A/B retained.
- Experiment 3 (lowest-set CAM allocation): **REJECTED**. Kintex
  +462 LUT / -3 FF / -0.034 ns; Artix +513 LUT / +6 FF / +0.550 ns. Golden
  equivalence PASS and highest-only golden-pick mutation FAIL; candidate CAM
  FULL 7/7, trans-manager 3/3, both prove/cover PASS. Timing is inconsistent
  and area rises sharply, so both RTL files were reverted. Directed boundaries,
  `formal/amba/monitor_trans_cam/`, and the negative A/B remain.

## Why

The current AXI interface observers use monitor-lite taps. The owner wants
separate full-feature observer variants and a same-configuration measurement
of whether FPGA optimization makes the full monitor efficient enough when its
performance-window and debug features are required. Existing lite consumers
stay unchanged.

## What

- Extract shared master/slave observer cores behind stable lite wrappers.
- Add `axi4_intf_master_observer_full` and `axi4_intf_slave_observer_full`.
- Add passive `axi4_rd_monfull_snoop` and `axi4_wr_monfull_snoop` taps that use
  actual bus handshakes and never feed `block_ready` into the observed bus.
- Plumb exact `cmd_refused` accounting through the full monitor and expose it
  through the existing observer loss-status path.
- Capture an unoptimized full observer baseline, then measure CAM payload reset
  removal, reporter snapshot reset removal, and lowest-set CAM allocation as
  independent keep-or-revert experiments.
- Run full observer/AMBA verification and the specified Kintex-7/Artix-7 OOC
  matrix. Publish absolute values, deltas, critical paths, and dispositions in
  `docs/markdown/rtl-amba/monitor/monitor_characterization.md`.

## Constraints

No existing project switches to the full variants. Full-before/full-after must
use identical parameters and cones; lite is context, not a feature-equivalent
control. Rejected optimizations are reverted and documented. Do not commit
generated formal flats, raw Vivado result churn, or unrelated shared-tree work.

## Done when

Both full variants pass feature/passivity/loss-accounting tests, existing lite
behavior stays green, every specified synthesis row has a result, every
experiment has a measured disposition, relevant formal and clean FULL AMBA/misc
regressions pass, and the final report states residual misses and where the
full variant is worth its cost.
