# TASK-029: Harden the snk_data_path_axis tests so a dropped beat or ignored backpressure fails them

**Priority:** P3
**Status:** closed -- 2026-10-18
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

## Closure (2026-10-18)

1. `stress_test` gives each operation its own 8 KB slot (random 64-byte
   offset, so a burst can still cross a 4 KB line), drains on `wait_drained`
   (every beat accepted, every scheduler idle) and compares every packet in
   memory; the 90% pass rate is gone.
2. `multi_channel_operation` runs rounds: one taken descriptor per channel,
   then each channel's packet, overlapping on the AXI port; every packet is
   checked in memory.
3. `snk_data_path_axis_test.sv` takes `cfg_sched_timeout_cycles/_limit/_enable`
   as ports. The TB defaults to 1000 cycles, limit 0 (never escalate); the new
   `test_sched_timeout` checks both settings: limit 0 only waits and completes,
   limit 2 escalates in window 2, stays sticky, and recovers on channel reset.

Also: every cocotb test asserts zero GAXI-master ready timeouts
(`assert_no_bfm_timeouts`), and a missed descriptor take now raises instead
of warning -- with escalation off, the BUG-015 race would otherwise only
slow a test down.

Mutations, each run at func, SEED=13275, then restored and cmp-verified:

| Mutation | Caught by |
|---|---|
| BUG-015 helper race (sample 2 clocks late) | missed-take assert |
| one beat dropped from op 5 | missed-take assert (the channel waits for it) |
| one beat corrupted, count unchanged | memory compare (31/32 verified) |
| the old multi_channel body at full | BFM-timeout assert (desc_ch0..3: 1 each) |

`snk_data_path_axis_test.py` from clean builds: gate 59/59, func 118/118,
full 177/177, 0 BFM ready timeouts and 0 missed takes in every log. func
runs in 3.6 min (was 10.5), full in 5.4 (was 12.8): the drain wait replaced
fixed sleeps.
