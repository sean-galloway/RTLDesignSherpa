# The write ceiling is the store's 8-entry pool, not a per-burst bubble (memory-controllers MC-015, sim half, 2026-11-13)

MC-014 left granite's writes at 686 / 687 MB/s on `col_major_interleaved` /
`row_thrash` with the row lane carrying the reads to 773 / 775, and the task
was filed as "one command slot per AXI burst at the intake" from the WR
stream's shape: seven WRs a cycle apart, then a gap of two, per 8-beat burst.
That framing was wrong. The period is eight because the write pool holds
eight entries, and an 8-beat BL8 burst happens to be eight BL4 sub-commands.
Same point as MC-014: granite perf proxy, 100 MHz MC / CK 200, DFI 1:2, x16
BL4, `t_phy_wrlat` 1, tREFI 772, TEST_TXN 1024, lane on (`TEST_DUAL=1`).

## The probe: every hop of the write path, per cycle

`PERF_W_HOPS=<path>` in `test_granite_char_perf.py` samples the valid/ready
pair of each hop from the controller's AXI port down to the plane's WR fire
(port, narrow pack, splitter, intake post-skid, AW push, data pop, the
store's AW head and data admission, fill done, `evt_wr`) and, per hop, counts
handshakes, the gaps between them, cycles with valid and no ready (the hop
below stalls) and cycles without valid (the hop above starves); the first 48
cycles come out raw with the store's gating terms beside them.
`col_major_interleaved_bl8`, one injector, 12 000 cycles from the first W
handshake:

| hop | handshakes | gap 1 | gap 2 | valid, no ready |
|---|---|---|---|---|
| AXI port AW (`s_axi_aw`) | 1 023 | -- | 1 002 at gap 9 | 8 488 |
| AXI port W | 8 192 | 7 167 | 1 007 | 1 333 |
| splitter / intake / AW push / data pop | 8 192 | 7 168 | 1 007 | 1 329-1 333 |
| store AW head (`aw_push` into `r_awh`) | 8 192 | 7 168 | 1 007 | 1 331 |
| store data (`wd_valid` / `wd_ready`) | 8 192 | 7 168 | 1 007 | 1 333 |
| WR fire (`evt_wr`) | 8 192 | 7 168 | 1 007 | -- |

Every hop carries the same 1 007 gaps of two, and every hop above the store
shows them as "valid, no ready": back-pressure from below, not starvation from
above. The raw window puts the stall at the store: one cycle in nine
`aw_push_valid_i` is high with `aw_push_ready_o` low, the next cycle
`wd_ready_o` is low (the fill order is empty because that AW did not fire),
and the cycle after the port's W stalls. On the stall cycle the store's
gating terms read `w_wr_have_free = 0` and everything else 1: **the pool has
no free slot.** Harness side (injector, address generator, N:1 merge, order
queue, skids), splitter, chopper, narrow pack and intake are bubble-free; the
earlier static reading of them was right and beside the point.

## Why eight in nine: Little's law on the pool

A write slot is allocated when the AW head fires into the pool and freed at
fetch-last, after its WR has been picked, fired, committed and its data
fetched out of the store toward the DFI path, every stage a register (the
100 MHz discipline of MC-011 and MC-014). Eight slots at 8/9 of a command per
cycle implies a nine-cycle turnaround, and 8/9 of the refresh-limited 781 is
the measured 686: the pool, not the slot. Reads do not pay it: at pool 8 they
already sit at 99 percent of the ideal, so a read slot turns around inside
the eight.

## The pool sized up, in sim

Lane on, same point, `TEST_NUM_ENTRIES` on the proxy (the board builds 8,
`granite_char_harness` `NUM_ENTRIES`):

| family (bl8) | pool 8 (MC-014) | pool 12 | pool 16 | model ideal | board 2026-11-12 (pool 8, lane on) |
|---|---|---|---|---|---|
| col_major_interleaved | 686 / 773 | 768 / 767 | **766 / 768** | 781 / 782 | 688 / 774 |
| row_thrash (4 gen) | 687 / 775 | -- | **769 / 769** | 779 / 782 (row-hit) | 688 / 774 |
| random (4 gen) | 627 / 722 | -- | **719 / 717** | 767 / 773 (row-hit) | 635 / 729 |
| col_major (control) | 414 / 516 | -- | 414 / 516 | 465 / 570 | timer-bound, unchanged |
| mixed (4 gen, bank cap 6) | 475 / 300 | -- | 473 / 267 | 363-370 (captured trace) | 487 / 300 (defaults preset) |

Zero mismatched beats everywhere. With the pool at 16 the W port's gap-2 count
on `col_major_interleaved` falls from 1 007 to 26 (12: to 8) and the writes
land within 2 percent of the ideal, level with the reads; the residue is
refresh. `random` writes gain 15 percent and its reads lose 1, the same-bank
row switches now binding both directions alike. `col_major` does not move.

**Pumice has the same pool.** Its proxy (`test_ddr2_char_perf.py`, lane on,
`TEST_WR_CAM_DEPTH` threaded through the pumice TB top and harness, default
8 unchanged): `col_major_interleaved` 682 / 767 -> **768 / 767**, `col_major`
410 / 472 -> 411 / 472. The "both controllers" in the task title holds, and
for the same reason.

## Mixed is the trade-off

The two-direction family loses reads with the deeper pool: 300 -> 267 at the
proxy's bank cap of 6 (`BANK_CAP_MIXED`, the per-bank occupancy limit while
the other direction holds entries). The direction register holds a direction
while it has pending columns, and sixteen write entries keep the write side
from running dry. Sweeping the cap at pool 16 is not monotonic:

| bank cap (pool 16) | mixed wr / rd |
|---|---|
| 3 | 120 / 120 |
| 4 | 277 / 513 |
| 6 (the board value) | 473 / 267 |
| 8 | 221 / 219 |

That is the mixed window's scheduling question (MC-016), not this task's; the
cap stays at 6 and the number is recorded.

## Method

- **A period equal to a burst length is not evidence of a per-burst
  mechanism.** The task was filed on "8 beats in 9 cycles" read as "one cycle
  per AXI burst"; the controller has three things of size eight on the write
  path (the burst, the pool, the bank count) and only the probe said which.
  Candidates listed in the task -- injector ordering, AW-meta FIFO gating,
  store admission -- were all read statically first and all cleared; the
  reading cost an hour and settled nothing the 12 000-cycle probe did not
  settle in three minutes, with the gating term named.
- **Sample every hop's valid AND ready, not the handshake alone.** The
  handshake count is identical at every hop (it has to be: one stream); the
  stall ownership is in which side is low. One statistic per hop -- valid
  without ready -- pointed down the chain to the store in the first run.
- Little's law before microarchitecture: slots / turnaround = throughput. The
  write pool's nine-cycle lifecycle is the sum of register stages this
  family's 100 MHz work put there deliberately; the fix is capacity, not a
  shorter pipe.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests   # env_python sourced
    export TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024 TEST_LEVEL=FUNC
    # the probe (granite, pool 8, lane on)
    TEST_DUAL=1 TEST_FAMILIES=col_ilv TEST_NUM_GEN=1 PERF_W_HOPS=$OUT/hops.json PERF_W_HOPS_CYCLES=12000 \
        python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
    # the pool sized up (rm the _dual sim_build between pool sizes: the tag does not carry it)
    TEST_DUAL=1 TEST_NUM_ENTRIES=16 TEST_FAMILIES=row_thrash TEST_NUM_GEN=4 python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
    TEST_DUAL=1 TEST_NUM_ENTRIES=16 TEST_BANK_CAP_MIXED=4 TEST_FAMILIES=mixed TEST_NUM_GEN=4 ...
    # pumice (its own sim_build tag per pool size)
    TEST_DUAL=1 TEST_WR_CAM_DEPTH=16 TEST_FAMILIES=col_ilv,col_major TEST_NUM_GEN=1 python3 -m pytest test_ddr2_char_perf.py::test_ddr2_char_perf -q

Board half: `board_mc015_write_pool_sku100_2026-11-13.md`.
