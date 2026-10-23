# TASK-036: rapids-g at 16 channels (for the Hive)

**Priority:** P2
**Status:** closed -- 2026-10-23; opened 2026-10-21; owner requirement, conditional: needed if the Hive uses rapids-g; waits on rapids TASK-034
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

## Closed 2026-10-23

Built although the Hive may not use rapids-g (owner 2026-10-23). One gatling per half; NUM_HARTS 4, 8
or 16 with at most 4 slots per hart; measured default 8 harts at 16 channels (2 slots). SCRATCH_WORDS
256 above 2 slots. Generated `rapids_g_16ch_top` / `rapids_g_16ch_cxs_top`. The register path needed
no change: the 16-channel map is also 13-bit with SRC at 0x0 and SNK at 0x1000. Found on the way:
`stream_top_ch8.sv` cast its idle vector to 8 bits, which `stream_top_ch16.sv` inherited (channel 13
never idled); both now use `STREAM_REGS_NCH`, ch16 regenerated, STREAM top 69/69.

- Full gate from `make clean-all`, 2026-10-23 (one run, every area at the full level):
  rapids fub_g 192, macro_g 270, top_g 183 (16-channel cells now run, 0 skipped; `test_rapids_g_regpath`
  failed 3/3 in that run because the new jump-table check in `bin/gen_rapids_g_fw.py` also applied to
  that test's own program; the check was scoped to the scheduler image and the test re-run 3/3 passed),
  fub 1,740, fub_beats 1,302, macro 843, macro_beats 774, top 183, top_beats 54; STREAM fub 510,
  macro 684 (+5 skipped: the 1-channel cells of the multi-channel test, by design), top 69. 0 failed.
- Perf at 16 channels (16/8/4 harts): HAS 0.93 Table 6.4.6 and MAS 0.83 Table 5.5.6.
- OOC P&R at 100 MHz: rapids-16ch 126,820 LUTs / 128 DSP / WNS +0.079; rapids-g-16ch 141,067 LUTs /
  0 DSP / WNS +0.050 (MAS Table 5.5.7, with 8-channel rows).
- No board build at 16 channels (the Genesys 2 harness is 8 channels).
