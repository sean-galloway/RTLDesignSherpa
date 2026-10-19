# TASK-029: Harden the snk_data_path_axis tests so a dropped beat or ignored backpressure fails them

**Priority:** P3
**Status:** open
**Owner:** sean galloway

## Why

rapids BUG-015 ran for a whole regression without failing a test: the
stress test dropped beats on a channel wedged in sticky `CH_ERROR`, and every
cell still passed. Three gaps let it hide.

## Items

1. **The stress test checks no memory.** `stress_test` scores an operation only
   on whether a send raised, so a beat the AXIS BFM drops after its 1000-cycle
   ready timeout never fails it. Compare each packet's bytes against
   `memory_model` (the per-packet check `_check_good_packet` already does this
   for the reset tests), and fail on any BFM ready timeout.
2. **`multi_channel_operation` over-queues and ignores the backpressure.** At
   full it sends 4 descriptors per channel and no data; the wrapper's port holds
   3 (FSM + the 2-deep rapids TASK-028 skid), so the 4th waits out the
   descriptor master's timeout on every channel and the test passes anyway.
   Either send each descriptor's data, or assert that the port refuses exactly
   at its capacity of 3.
3. **The wrapper's timeout turns a pacing slip into a whole-ingress cascade.**
   `snk_data_path_axis_test.sv` ties `cfg_sched_timeout_cycles=1000` and
   `cfg_sched_timeout_limit=1`, so one 1000-cycle wait makes a channel's
   `CH_ERROR` sticky, its beats then hold the shared ingress, and the stall
   spreads to every channel. Make the limit/cycles test-settable (ports or
   parameters driven per test), keep the escalation for the tests that
   exercise it, and loosen it elsewhere.

## Done when

- A deliberately dropped beat (or a re-introduced BUG-015 helper race) fails
  the stress test at func.
- `multi_channel_operation` shows 0 descriptor-port ready timeouts at full, or
  asserts the refusal it gets.
- `snk_data_path_axis_test` passes at gate, func and full with 0 BFM ready
  timeouts in any log.
