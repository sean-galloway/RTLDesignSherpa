# TASK-001: amber_pair_harness on monbus_axil4_group_1wr

**Date:** 2026-10-25
**Priority:** P3
**Status:** CLOSED 2026-10-25
**Owner:** amber

## Why

Owner 2026-10-25: every FPGA harness moves to the write-only ocelus group
(stream TASK-019's `monbus_axil4_group_1wr`). Amber's pair harness was the
last hand-written one on the two-port group; its drain side was already
tied off, so the swap is mechanical.

## What

`rtl/amber_pair_harness.sv`: `monbus_axil4_axil4_group` ->
`monbus_axil4_group_1wr`; the tied-off `s_axil_*` drain signals leave;
err_select masks stay 0 so the error window (strapped to a dead null
window) never receives a record and the tally record ingest sees the same
write stream as before. `rtl/filelists/amber_pair_genesys2_top.f` pulls
`monbus_axil4_group_1wr.f`. README names the new group.

## Done when

`dv/tests` (axil + uart) pass. NOTE: BUG-003 (seed-flaky "tally bins all
zero") predates this swap and reproduces identically on both groups --
it is tracked separately, not a regression of this task.

## What was done (2026-10-25)

`amber_pair_harness.sv` instantiates `monbus_axil4_group_1wr`; the tied-off
`s_axil_*` drain signals and their tie-offs are gone; the error window is
strapped to a dead null window (base 0, limit 0, flush watermark 3) with
err_select masks still 0, so no error record is ever written and the tally
record ingest sees the same write stream as before.
`rtl/filelists/amber_pair_genesys2_top.f` pulls `monbus_axil4_group_1wr.f`;
the README names the new group.

Verification: `dv/tests` axil + uart green modulo BUG-003 -- the closing
rerun went 3/4 with the one red cell (`axil[gate]`, SEED=74560) failing on
the pre-existing BUG-003 assertion, deterministic by seed and identical at
8854596d7; an unpinned rerun of the same cell passes. The build log shows
`monbus_axil4_group_1wr.sv` compiled in. Closed with BUG-003 open.
