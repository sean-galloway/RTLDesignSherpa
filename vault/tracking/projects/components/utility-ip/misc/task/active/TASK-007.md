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
