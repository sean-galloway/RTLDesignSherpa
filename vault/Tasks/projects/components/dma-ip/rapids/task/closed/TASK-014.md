# TASK-014: control engines drain on channel reset instead of abandoning the AXI transaction

**Priority:** P2. Sean picked drain-on-reset over quiesce-then-reset (2026-09-27).
**Status:** CLOSED 2026-09-27 (closing note at the end); was open 2026-09-27. Raised when TASK-013 turned ctrlrd's channel-reset test
into a between-operations clear: the old mid-read version only passed because its
hand-rolled responder withdrew the R beat, which no real slave does.

## The gap

`cfg_channel_reset` is a soft, per-channel reset of the engine; it does not reach the
fabric. A reset with a read outstanding dropped ctrlrd to `READ_IDLE`, where `r_ready`
never rises, so the slave's R beat sat on the bus and the next read on the same ID
took it as its own answer. ctrlwr had the same shape on AW/W/B: a raised phase was
withdrawn (an AXI violation) or a B was left dangling.

## The change (RTL, both engines)

Drain flags captured on the reset cycle from the pre-reset state:
- ctrlrd: `r_drain_ar` holds a raised AR until accepted; `r_drain_pending` lifts
  `r_ready` for the owed beat and discards it.
- ctrlwr: `r_drain_aw` -> `r_drain_w` -> `r_drain_b` step the issued write through to
  its B, which is discarded; the write lands with its latched address and data.
While draining, `*_engine_idle` stays low and the request path stays closed. Formal
properties `no_new_request_while_draining` and `drain_holds_*` added under `ifdef FORMAL`.

## Verification

- `test_ctrlrd_engine_reset_mid_read` (AR raised / AR accepted) and
  `test_ctrlwr_engine_reset_mid_write` (AW raised / AW accepted / B owed), each ending
  with a fresh operation that must return or land its own data.
- Existing suites unchanged; clean full rapids regression after the tests land.

## Closing note (2026-09-27)

RTL in cd9d46c9f, tests in the commit after the dv hand-back.
`test_ctrlrd_engine_reset_mid_read` (AR raised / AR accepted with the beat owed) and
`test_ctrlwr_engine_reset_mid_write` (AW raised / AW accepted with W pending / W
accepted with B owed) pass on the new engines and, in an A/B swap against the
pre-change RTL, fail for exactly the reasons filed: a raised phase withdrawn, the owed
beat never taken, idle reported with it owed, the issued write never landing. Clean
full rapids regression after the tests, at the new 2250-cell FULL depth: fub 162,
fub_beats 1275, macro 36, macro_beats 747, top_beats 30, 0 failures. The earlier
"drain-on-reset backfired" note in CONTROL_ENGINE_INTEGRATION.md is explained there:
it fought the hand-rolled responders of the time, not the fabric.
