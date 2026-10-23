# TASK-036: rapids-g at 16 channels (for the Hive)

**Priority:** P2
**Status:** open -- 2026-10-21; owner requirement, conditional: needed if the Hive uses rapids-g; waits on rapids TASK-034
**Owner:** sean galloway

## Why

Owner 2026-10-21: the Hive needs 16 channels if it uses rapids-g. rapids-g (rapids TASK-034) supports 4 or
8 channels (`rapids_seq_g` refuses others at elaboration); the product byte tree already builds 16
(`rapids_16ch_top`, the derived `rapids_regs_16ch` map).

## What

1. Sequencer shape (decide by measurement): one gatling per half with 4 slots per hart (hart h runs
   channels h, h+4, h+8, h+12), or two gatlings per half at 2 slots each. The first costs firmware
   latency (each hart's service loop covers twice the slots), the second about one more gatling per half.
2. `rapids_seq_g`: allow NUM_CHANNELS 16; `SCRATCH_WORDS` >= 64 x slots (256 at 4 slots); the 16 slot
   windows fill 0x1000_0000-0x1000_0FFF exactly, below SUMMARY at 0x1000_1000.
3. Firmware `rtl/fw_g/sched_g.S`: the slot loop and SUMMARY scan at 4 slots.
4. Register path: `rapids_g_top_reg_arb.svh` requires the 8-channel map (13-bit APB, half select on
   bit 12); pin each gatling to its half of the 16-channel map instead, and test it on `rapids_16ch_top`
   (-g variant from `bin/gen_rapids_g.py`). `CH_SCRATCH[16]` is already in the 16-channel map.
5. DV: the equivalence bench and the reused macro_g/top_g suites at 16 channels.
6. Measure: perf (the TASK-034 scenarios, 16 channels) and OOC area/WNS against `rapids_core` at 16
   channels shared (77.1k LUTs, +0.56 ns).

## Done when

A 16-channel rapids-g top passes the reused suites and the equivalence bench, and the HAS/MAS carry its
perf and area against the 16-channel product build.
