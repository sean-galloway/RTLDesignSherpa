# TASK-023: the generator emits the write-only monbus group ([bridge.mon_group] write_only), default true -- the 1wr group is the default emitter

**Date:** 2026-10-25
**Priority:** P3
**Status:** CLOSED 2026-10-25
**Owner:** bridge
**Where:** `bin/bridge_pkg/config.py` (`MonGroupConfig.write_only`), the mon test configs, `bin/bridge_batch.csv`, GAS ch02 `04_monitor_and_cfg_keys.md`
**Found by:** the owner, 2026-10-25

## Why

(The INDEX's filing line: the generator emits the write-only monbus group;
the Genesys 2 _mon bridges move to monbus_axil4_group_1wr. The emission
key and fixtures landed in cfbf35bc1; this file's flip and the err-window
plumbing complete the task.)

The write-only monbus egress (`monbus_<p>_group_1wr`: no slave-read
drain; error-selected packets go to a memory error window, read back on
`mon_irq_out` + `err_rec_count`) is what stream, rapids and bridge-stress
standardized on (stream TASK-019 / rapids TASK-039) -- every consumer
outside the bridge's own test fixtures already sets `write_only = true`
explicitly. The two-port `monbus_axil4_axil4_group` survives only as the
unmarked default. The default should be the emitter the project uses.

## What to do

1. `MonGroupConfig.write_only` defaults to True. A toml that says nothing
   gets the 1wr group; `write_only = false` under `[bridge.mon_group]`
   keeps the existing two-port method.
2. Pin `write_only = false` in every legacy mon test config (they hold
   the two-port group's DV: the `s_mon_axil_*` drain), so regeneration is
   byte-identical.
3. Add `bridge_3x2_rw_mcdc_1wr` and `bridge_1x2_rd_regblock_1wr` to
   `bridge_batch.csv` -- the batch regenerates every monbus-group
   consumer (CRITICAL RULE #0).
4. GAS ch02: the default statement flips; the key reference gains
   TASK-023.
5. Unit tests: the default is the 1wr module name; explicit false is the
   two-port name; the existing `write_only = true` fixtures still emit
   1wr.

## What was done

`MonGroupConfig.write_only` defaults to True; the 20 legacy mon configs
are pinned to `write_only = false` (their DV drains the two-port group's
s_mon_axil_* surface); `bridge_3x2_rw_mcdc_1wr` and
`bridge_1x2_rd_regblock_1wr` joined `bridge_batch.csv`; GAS ch02's default
statement flipped. The regen also picked up the 1wr err-window plumbing
that was sitting uncommitted in the tree (the cfg RDL extension, the
field map, the j2 template, ip_closure, and monitor_stress_common's
err-window filter) -- complete and green, landed in the same commit by
the owner's call.

## Done when

- [x] the parser default is 1wr, the 20 legacy mon configs pinned to
      `write_only = false`, full regeneration clean (55 fixtures; churn
      only the pinned toml copies, the comment-neutralized .sv lines and
      the two new 1wr outputs), generator unit tests 257/257 green
