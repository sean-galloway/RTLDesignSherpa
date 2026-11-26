# MC-023 item 4: the hybrid mixed cell -- the entry behind the head is seen a slot after it lands

> memory-controllers MC-023, 2026-11-25 (second record of the day; the first is
> `model_mc023_ap_row_lag_refresh_drain_2026-11-25.md`). With the RTL's refresh
> drain (`ref_drain_pb`) and the new term `behind_lag` 1 together, `defaults`'
> mixed cell is in the RTL's two modes, in the RTL's proportion, with no third
> mode. Both stay knobs: the drain moves four bank_interleave cells out (item 3).
> Proxy: `test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, 4 generators, `mixed`
> bl8, tREFI 780, `TEST_REF_ALIGN`.

## 1. The proxy was not the SKU

`test_granite_char_perf` built `STORE_MERGE_EN` 1 (the research combiner) by
default; the FPGA SKU builds it 0 (owner, 2026-11-08). Every proxy record before
this one ran with the combiner on. Fixed: the default is now 0
(`TEST_STORE_MERGE_EN=1` runs the research build).

`defaults mixed_bl8`, TXN 8000, 8 offsets, fast-mode count:

| proxy build | fast offsets |
|---|---|
| combiner on, read path 4 / 0 (the old default) | 5 of 8 |
| combiner off (the SKU) | 2 of 8 |
| combiner off, the board's read path (rddata_en 6, rddata_delay 6, strict read latency 6) | 2 of 8 |

The board's read-path pair (6 / 6, from the init log) does not decode in the
lenient sim PHY (4096 mismatched); with `TEST_STRICT_READ_TIMING=1` every
latency 0 .. 12 reads clean, because the controller captures on the valid. The
SKU proxy at 16 offsets (0 .. 750, step 50): **slow 280 / 280 on 10, fast
301 .. 307 / 549 .. 559 on 6**.

## 2. What sets the mode on the RTL

A mode is a state of the direction register, set by where the refreshes walk
through the turns:

- Slow mode (the board's 277 / 276): every direction run exactly 256 columns
  (255 to the cap plus the leftover column that fires in the flip cycle). On the
  slow offsets, 1,000 read and 999 write runs, all 256.
- Fast mode: a refresh lands in the cap cycle, the demand block takes the
  leftover column, the read run ends at 255, and the turn phase is one column
  off. From then on the reads' PRE of a write's bank lands after the flip, the
  write's first command is past the 8-cycle idle hold, and a read column takes
  the bus back (cause-0 flips, write holds of 10 cycles). On the RTL this is
  real: offsets 200 and 300 break at cycles 1,458 and 11,711 with 255-column runs.
- The walk is a limit cycle: per turn pair the refresh moves ~45 cycles through
  the runs (R+45, +93, +133, +184, +222, +266, +310, then W+53 ..). Whether it
  reaches the cap window depends on what each refresh costs at the column it lands on.

## 3. The model's difference: the record of the entry behind the head

With the drain alone the model's slow mode broke at every GO phase (a 255-column
run with a REF 5 cycles after its last column, every ~42,000 cycles). Read-run
refresh cost by landing phase (mod the 19-cycle bank-0 / bank-1 read pattern):

| phase | RTL | model (drain alone) |
|---|---|---|
| 0 | 18 / 19 | 19 |
| 7 | 21 | 18 |
| 13 | 24 / 28 | 30 |
| 17 | 25 | 22 |

At phase 7, aligned (model cycle 3,917 = RTL 72 with identical queue depths),
the last column of bank 0's interrupted burst after the REF is the difference:
the RTL fires RD and closes the row with a PRE three cycles later, and the model
fires RDA. Both have the same entry count in bank 0's read queue (2). The pick
probe (`PERF_PICK_PROBE_FLIP`) shows the RTL head with `behind_empty` set: the
entry behind it was pushed the cycle before, counted in `r_rq_cnt` the next
cycle, and seen behind the head one cycle after that. With the bank "empty" and
the drain unarmed (the reopened row is the same row), the conflict-only hybrid
does not auto-precharge. The model saw the entry the slot it landed, read a
conflict, and auto-precharged.

Term `behind_lag` (`granite_sku_controller.cpp`, default 0): the first entry
behind a head counts toward `behind_vld` / `behind_same_row` only
`admit_lag + behind_lag` slots after acceptance. At 1 it is the RTL's timing.

## 4. Result

`granite_sku100 mixed_bl8`, 40 GO phases:

| model | at 8,000 txn | at the board's 32,000 |
|---|---|---|
| committed | -- | 278 / 278 x27, fast x13 (the first record) |
| `ref_drain_pb` | 293 / 410 and 301 / 56x, no slow mode | 293 / 408 x21, 301 / 569 x19 |
| `ref_drain_pb` + `behind_lag` 1 | **280 / 280 x20, 301 .. 302 / 540 .. 591 x20** | 280 / 280 x20, 301 / 55x x20 |
| `behind_lag` 1 alone | -- | 303 .. 308 / 61x x40 |
| RTL SKU proxy (16 offsets, 8,000) | 280 / 280 x10, fast x6 | -- |

On the slow phases the model now runs 1,999 direction runs, all 256, as the RTL
does. `open_page` with both terms: 280 / 280 x27, 302 / 579 x13, unchanged from
the drain alone. The two terms belong together: neither alone holds the hybrid.
Test: `test_behind_lag_with_the_refresh_drain_holds_the_hybrid_mixed_cell_in_the_slow_mode`
(the aligned GO phase 1554: 280 / 280 with both, reads > 330 with the drain alone).
Model tests 50 / 50.

## 5. Why the default does not move yet

Against the SKU board set with both terms (`all` on the four configs):
**53 in / 4 out**, largest delta 11.3 percent. Improved: `defaults` and
`open_page` col_major_interleaved / row_thrash (+0.7 -> +0.1 percent), the
mixed cells in the board's modes. Out: four bank_interleave write sides at
~518 (incremental_bl16, row_major_bl4 / bl8 / bl16). `behind_lag` does not
move them; the drain does. The board has that level (ISSUE-007's 583 / 566 /
~518 by refresh offset, MC-025 section 6), so the drain is what makes item 3
modelable, but the proportions are wrong. `row_major_bl8` on 40 GO phases with
both terms: writes 517 on 26 and 580 on 14 (board 518 on 2 of 8 offsets),
reads 574 / 566 / 569 / 518 (board 566 on 5, 583 on 3). The committed model has
582 / 590 at all 40, no levels at all.

## 6. Open

- Item 3: the bank_interleave levels with the drain on, the same method
  (aligned proxy run, refresh cost by landing phase).
- The board shows `defaults` slow on 8 of 8 aligned offsets at 32,000; the
  RTL SKU proxy is fast on 6 of 16 at 8,000 (fast is absorbing, so longer is
  not slower). That gap is between the board and the RTL simulation, not the
  model.

## 7. Record

- Proxy runs (scratch): SKU `mixed` at TEST_REF_ALIGN 0 .. 750 (TXN 8000),
  the read-path and combiner variants, pick probes at flip 68 (offset 0).
- Model: `sku_refdrainpb` with `GRANITE_SKU_PARAMS=behind_lag=1`;
  `cmp_both.md` (scratch) is the board compare of the pair.
