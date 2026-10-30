# TASK-007 — narrow AXI beats on the wide host return wrong data back to back

**State:** open · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
**Source:** found while closing TASK-003 item 6 (the DFI 1:4 proxy's "two
valids per read" was the host driving 8-byte beats on the 128-bit bus).
**Depends on:** nothing; the 1:4 128-bit host build (TASK-003 item 6) is the
geometry that shows it.

## What

On the DFI 1:4 build (`GRANITE_DFI4`: BL8, x16, 128-bit host AXI, one
AXI beat = one DRAM burst) a stream of **8-byte AXI beats** (AxSIZE 3 on a
16-byte bus: legal narrow transfers, two per 16-byte line) returns wrong
data when the beats are back to back:

| host beats | family | result (1:4 proxy, 2026-10-29) |
|---|---|---|
| 16-byte (full width) | incremental / row_major / col_ilv / col_major | 0 mismatched, 1135/1151, 1148/1148, 918/913, 666/713 MB/s of 1200 |
| 8-byte (narrow) | incremental | **1020 of 1024 beats wrong**, 568/575 MB/s |
| 8-byte (narrow) | col_major | 0 mismatched (page misses space the reads) |
| 4-byte (narrow) on the 64-bit 1:2 host | incremental / col_major | 0 mismatched |

Each narrow beat becomes its own BL8 read of the same 16-byte line (the
aligner probe counts one RD command and one valid per beat: 2048 for
1024 lines, nothing duplicated at the PHY), so the defect is in how the
read return path serves two same-line, adjacent reads to half-width
beats, not in the DFI plane. The 1:2 64-bit host with 4-byte beats (two
per 8-byte word) is clean, so it is specific to the 1:4 geometry
(BURST_WORDS 1, AXI_BEATS_PER_BURST 1) or to adjacent same-column reads.

On the board (1:4 ILA bitstream, 2026-10-29) the same narrow read gives
the same one-wrong-word-per-run as the full-width read (TASK-003 item 6),
and a **narrow write started after that mismatching read hangs the write
engine** until a soft reset (seen twice; full-width writes after a
mismatching read hang the same way -- so this half is likely the
harness's latched rd_error / engine state, not the controller; separate
it first).

## Repro

```
cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests
TEST_AXI_SIZE=3 TEST_AXI_DATA_WIDTH=128 TEST_DFI_RATE=4 TEST_DRAM_BL=8 \
TEST_DRAM_BEAT_BYTES=4 TEST_DRAM_DEVICE_BYTES=2 TEST_T_RDDATA_EN=1 \
TEST_FAMILIES=incremental PERF_ALWAYS_DIAG=1 pytest -q test_granite_char_perf.py
```
(`TEST_AXI_SIZE` forces the beat size; without it the proxy now drives
full-width beats at `TEST_AXI_DATA_WIDTH`.)

## Done when

Narrow beats at every legal AxSIZE on the 128-bit host return the right
data back to back (a directed core TB case per AxSIZE, and the proxy
line above clean), and the post-mismatch write hang is attributed.
