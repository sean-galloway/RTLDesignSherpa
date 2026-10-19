# TASK-030: Port the rapids TASK-029 hardening to the beats-tree snk_data_path_axis tests

**Priority:** P3
**Status:** closed -- 2026-10-19
**Owner:** sean galloway

## Why

rapids TASK-029 hardened the byte-tree `snk_data_path_axis_test` only. The
beats tree keeps its own copy (`snk_data_path_axis_test_beats_tb.py`,
`test_snk_data_path_axis_test_beats.py`, wrapper
`rtl/macro_beats/snk_data_path_axis_test_beats.sv`) with the same three gaps,
and the last full regression showed the cost: 144 GAXI-master ready timeouts
across 18 `multi_channel_operation` logs (desc_ch0..3, 36 each; 4 per cell at
func, 12 at full), every cell passing.

1. `multi_channel_operation` queued descriptors with no data. The beats
   scheduler has no descriptor skid, so it holds one; the rest waited out the
   descriptor master's 1000-cycle ready timeout and were dropped.
2. `stress_test` checked no memory and passed at a 90% send rate.
3. The wrapper tied `cfg_sched_timeout_limit=1`: any 1000-cycle wait became a
   sticky `CH_ERROR` that no check looked at.

## Done when

- A dropped descriptor, a corrupted beat and a wrapper-tied limit each fail a
  test at func.
- `test_snk_data_path_axis_test_beats.py` passes at gate, func and full with 0
  BFM ready timeouts and 0 missed takes in every log.

## Closure (2026-10-19)

The beats tree keeps its data-first contract (packet into the SRAM, then the
descriptor that drains it); only the pacing and the checks changed.

1. `multi_channel_operation` runs rounds: each channel's packet, then each
   channel's descriptor (waiting for its scheduler to take it), then a drain
   before the next round; every packet is checked in memory.
2. `stress_test` gives each operation its own 8 KB slot (random 64-byte
   offset), waits for each descriptor's take (ops land back to back on random
   channels, and the scheduler holds one), drains, and compares every packet;
   the 90% rate is gone.
3. The wrapper takes `cfg_sched_timeout_cycles/_limit/_enable` as ports, TB
   default 1000 cycles, limit 0. The new `test_sched_timeout` checks limit 0
   (waits, no error, completes once its data arrives) and limit 2 (escalates
   in window 2, stays sticky, other channels clean). The beats wrapper has no
   per-channel reset, so a full reset recovers it and a good transfer must
   then complete.

Also: the take counter (`_desc_takes`/`_wait_desc_taken`, edge-counted as in
TASK-029), `wait_drained` (AXIS master empty and every scheduler idle), and
`assert_no_bfm_timeouts` after every cocotb test.

Mutations at func, then restored and cmp-verified:

| Mutation | Caught by |
|---|---|
| the old multi_channel body (two bare descriptors per channel, no data) | drain timeout, 0/8 verified |
| one beat of stress op 5 corrupted in the expected data | memory compare |
| wrapper limit tied back to `8'd1` | `test_sched_timeout`: the channel escalates in the limit-0 phase and never takes the next descriptor |

`test_snk_data_path_axis_test_beats.py` from clean builds, REG_LEVEL=FULL
(gate + func + full, 56 cells each) on three random seed bases
(1855531636, 3110012786, 284102998): 168/168 each, 0 BFM ready timeouts and 0
missed takes in all 504 logs; about 4 minutes a run.
