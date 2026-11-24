# MC-024: the read-priority direction register, priced in the SKU model

> memory-controllers MC-024, 2026-11-24. The owner's "design a read-priority
> direction register" (the third option ISSUE-005 left open). Priced in the
> GraniteSKU model (`granite_sku_controller.cpp`, `dir_mode 1`; the
> committed default, `rfc_block` on, is the baseline) before any RTL.
> Mixed cell `mixed_bl8` (4 writers + 4 readers, equal streams, the board's
> cell) and the new `sustained` suite (`mixed_rd4_bl8`: reads four times the
> writes; `mixed_wr4_bl8`: the reverse), `granite_sku100` (`defaults`) unless
> named.

## 1. The rule priced

- A read hold has **no batch cap**.
- A write hold is capped at **`wr_burst`** columns (16).
- The register leaves the reads for the writes when the reads drain (as the
  symmetric register does), or on **write starvation**: a write head queued
  `wr_starve` MC cycles (512) with no write column fired. The starvation
  flag is registered, one slot late, as the RTL would carry it.
- Everything else is the symmetric register: the leftover rule, the
  cross-direction fire, the hold-idle, the ownership courtesy (which, with no
  read cap, the reads keep for the whole hold).

## 2. Result

| cell | symmetric (today) wr / rd, union | read priority wr / rd, union | read latency mean / max (cyc) | worst write wait |
|---|---|---|---|---|
| `defaults` mixed_bl8 | 278 / 278, 555 | **307 / 597, 614** (+10.6%) | 19.0 / 450 -> **9.8 / 80** | 463 -> 559 |
| `open_page` mixed_bl8 | 290 / 366, 581 | 307 / 597, 614 | 14.8 -> 10.1 | 8,237 -> 558 |
| `close_page` mixed_bl8 | 73 / 121 | 72 / 114 (reads -6%) | 68.6 -> 72.5 | |
| `bank_interleave` mixed_bl8 | 160 / 160 | 231 / 364 | 80.4 -> 35.7 | |
| `mixed_rd4` (reads outlast) | 278 / 490, 612 | **124** / 597, 618 | 19.7 -> 9.8 | 463 -> 559 |
| `mixed_wr4` (writes outlast) | 469 / 277, 586 | 486 / 597, 608 | 19.0 -> 9.8 | |

The board's fast mode (303 / 594, `open_page`, two runs of ten) is this
shape; the register makes it the rule. On the 40-phase GO sweep both
open-page presets are **one mode on 40 / 40 phases** (303 .. 307 / 591 ..
597), where the symmetric register is the refresh-placed race of ISSUE-005;
`close_page` is one mode too (72 / 114 .. 115). Every other cell of the four
SKU configs' `all` suites moves by less than 2 percent (they are
single-direction passes). The cost is the write share while reads keep the
bus: 124 MB/s under sustained reads against 278 today, about 17 percent of
the bus, held by the starvation bound.

## 3. What was priced and not carried

| form | `defaults` mixed wr / rd, union | `mixed_rd4` writes | why not |
|---|---|---|---|
| pool-occupancy watermark drain (enter at 6, leave at 2) | **477 / 277**, 554 | -- | the writers refill the pool as fast as a drain empties it, so the drain never reached the low watermark and ran to the cap: write priority, not read |
| watermark at 8 or 12 | 316 / 656 (no flip) | -- | the per-bank admission cap holds the pool at ~6 on this cell: never reached |
| read quantum 64 / 128 / 255 under write pressure, write burst 16 | 271 / 416 .. 297 / 563 | 102 .. 119 | more turnarounds; the write share went DOWN |
| write burst 32 / 64 / 128 | 301 / 569 .. 290 / 382 | 122 .. 191 | the floor rises only at 128 and the board cell's reads fall to 382 |
| starvation 128 / 256 / 1024 (burst 16..64) | 270 / 325 .. 306 / 611 | 116 .. 204 | 128 halves the reads; 1024 doubles the write wait for +1 MB/s |

No form raised the write floor under sustained reads without giving back the
read-priority gain on the board cell; 512 / 16 is the knee.

## 4. Record

- Model: `dir_mode`, `wr_starve`, `wr_burst` (GraniteSKU knobs and
  `ModelConfig` fields; preset `sku_rdprio`); `dir_mode 0` reproduces the
  committed `_rfcb_2026-11-24` CSVs to the cycle on all four configs.
- `sustained` suite: the mixed family's `param` lengthens the read (> 0) or
  write (< 0) streams; not a board suite.
- Model test `test_read_priority_register_makes_the_mixed_cell_one_mode_and_bounds_the_writes`;
  47 / 47.
