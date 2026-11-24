# MC-024: the read-priority direction register, priced in the SKU model

> memory-controllers MC-024, 2026-11-24. The owner's "design a read-priority
> direction register" (the third option ISSUE-005 left open). Priced in the
> GraniteSKU model (`granite_sku_controller.cpp`, `dir_mode 1`; the
> committed default, `rfc_block` on, is the baseline) before any RTL.
> Mixed cell `mixed_bl8` (4 writers + 4 readers, equal streams, the board's
> cell) and the `sustained` suite (`mixed_rd4_bl8` / `mixed_rd16_bl8`: reads
> four / sixteen times the writes; `mixed_wr4_bl8`: writes four times the
> reads), `granite_sku100` (`defaults`) unless named.

> **Correction, same day (section 4).** The first pricing quoted the write
> floor under sustained reads as 124 MB/s. That was the write WINDOW (first
> write sent to last write done), and under read priority the writes finish
> after the reads, so the window carries a writes-only tail. Measured only
> while the reads hold the bus, the floor at 512 / 16 is **23 MB/s**. The
> section-3 rejections of longer bursts and other starvation bounds used the
> same window and are superseded by the grid in section 5, which turns the
> floor into a dial the two CSRs set.

## 1. The rule priced

- A read hold has **no batch cap**.
- A write hold is capped at **`wr_burst`** columns (16 in the first pricing).
- The register leaves the reads for the writes when the reads drain (as the
  symmetric register does), or on **write starvation**: a write head queued
  `wr_starve` MC cycles (512 in the first pricing) with no write column
  fired. The starvation flag is registered, one slot late, as the RTL would
  carry it.
- Everything else is the symmetric register: the leftover rule, the
  cross-direction fire, the hold-idle, the ownership courtesy (which, with no
  read cap, the reads keep for the whole hold).

## 2. Result at 512 / 16

| cell | symmetric (today) wr / rd, union | read priority wr / rd, union | read latency mean / max (cyc) | worst write wait |
|---|---|---|---|---|
| `defaults` mixed_bl8 | 278 / 278, 555 | 307 / 597, 614 (+10.6%) | 19.0 / 450 -> 9.8 / 80 | 463 -> 559 |
| `open_page` mixed_bl8 | 290 / 366, 581 | 307 / 597, 614 | 14.8 -> 10.1 | 8,237 -> 558 |
| `close_page` mixed_bl8 | 73 / 121 | 72 / 114 (reads -6%) | 68.6 -> 72.5 | |
| `bank_interleave` mixed_bl8 | 160 / 160 | 231 / 364 | 80.4 -> 35.7 | |
| `mixed_rd4` (reads outlast) | 278 / 490, 612 | 124 (window) / 597, 618 | 19.7 -> 9.8 | 463 -> 559 |
| `mixed_wr4` (writes outlast) | 469 / 277, 586 | 486 / 597, 608 | 19.0 -> 9.8 | |

At 512 / 16 the mixed cell's 307 MB/s write is also a window figure: the
reads run at 597 with the writes held to 23, the reads finish, and the writes
then run alone. The board's fast mode (303 / 594, `open_page`, two runs of
ten) is this shape. On the 40-phase GO sweep both open-page presets are one
mode on 40 / 40 phases (303 .. 307 / 591 .. 597), where the symmetric
register is the refresh-placed race of ISSUE-005; `close_page` is one mode
too (72 / 114 .. 115). Every other cell of the four SKU configs' `all`
suites moves by less than 2 percent (they are single-direction passes).

## 3. What was priced first and not carried

| form | `defaults` mixed wr / rd, union | why not |
|---|---|---|
| pool-occupancy watermark drain (enter at 6, leave at 2) | **477 / 277**, 554 | the writers refill the pool as fast as a drain empties it, so the drain never reached the low watermark and ran to the cap: write priority, not read |
| watermark at 8 or 12 | 316 / 656 (no flip) | the per-bank admission cap holds the pool at ~6 on this cell: never reached |
| read quantum 64 / 128 / 255 under write pressure, write burst 16 | 271 / 416 .. 297 / 563 | more turnarounds for the same reads; judged on the write window, not repriced |

The rows that priced other `wr_burst` / `wr_starve` values against the write
window (which concluded "512 / 16 is the knee") are withdrawn; section 5
replaces them.

## 4. The contended write rate

`TimedLoadStoreTrace` now reports `writes_at_read_last` (the writes done when
the last read completes) and `char_model.py` writes `wr_bw_rd_live_mb_s` on
the mixed rows: those writes over the window from the first write to the last
read. When the writes finish first it is their own window (they were never
held behind live reads). At 512 / 16:

| cell | write window MB/s | while the reads hold the bus |
|---|---|---|
| `mixed_bl8` | 307 | 23 |
| `mixed_rd4` | 124 | 23 |
| `mixed_rd16` | 36.5 | 23 |
| symmetric, any of them | 278 | 278 |

The floor is the rule's arithmetic: one write hold of at most `wr_burst`
columns per `wr_starve` cycles plus the turn, less the row work the turn
costs. The committed `defaults` CSV regenerates identically with the new stat
(15 / 15 cells, every column).

## 5. The dial: `wr_starve` x `wr_burst`

`model_mc024_rdprio_knob_grid_granite_sku100_2026-11-24.csv` (30 knob points x
4 cells). The contended write rate is from `mixed_rd16`; the union, the read
latency and the write wait from the board's cell `mixed_bl8`. The best union
at each write share:

| `wr_starve` / `wr_burst` | contended write MB/s | mixed_bl8 wr / rd, union | read lat mean / max | worst write wait |
|---|---|---|---|---|
| 512 / 16 (first pricing) | 23 | 307 / 597, **614** | 9.8 / 80 | 559 |
| 1024 / 64 | 45 | 309 / 582, 618 | 10.2 / 165 | 1,085 |
| 1024 / 128 | 83 | 304 / 537, 608 | 11.0 / 259 | 1,062 |
| **512 / 128** | **140** | 299 / 454, **599** | 12.8 / 256 | 553 |
| 512 / 255 | 221 | 290 / 357, 580 | 17.0 / 454 | 558 |
| **256 / 255** | **305** | 305 / 283, **566** | 22.0 / 455 | **299** |
| 128 / 255 | 375 | 375 / 283, 566 | 26.5 / 456 | 193 |
| symmetric (today, cap 255) | 278 | 278 / 278, 555 | 19.0 / 450 | 463 |
| symmetric, cap 128 / 64 | 263 / 241 | 272 / 279, 543 / 258 / 271, 515 | 19.9 / 229, 20.3 / 158 | 228 / 152 |

- **The write share costs union, monotonically.** Each step down the table
  gives the writes more of the contended bus and the board cell less union.
- **Long bursts dominate short ones.** At the same contended write rate a
  long burst with a long bound beats a short burst with a short bound (64 /
  16: 116 MB/s for a 490 union; 512 / 128: 140 for 599), because every turn
  pays the turnaround and the row work. The 8-bit `wr_burst` field reaches
  255, the right end of this curve.
- **256 / 255 dominates today's register**: more contended write (305 vs
  278), more union (566 vs 555), a lower worst write wait (299 vs 463), the
  same worst read (455 vs 450), mean read latency 22 vs 19. Lowering the
  symmetric cap (128, 64) only loses union.
- **The price of a short read tail is the write burst**: the worst read
  waits for one write hold, ~2 cycles a column (80 at 16, ~256 at 128, ~455
  at 255).

One mode on every refresh phase holds across the dial:
`model_mc024_rdprio_go_sweep_2026-11-24.csv`, mixed_bl8 at 40 GO phases under
`defaults` and `open_page`:

| `wr_starve` / `wr_burst` | `defaults` wr / rd, union | `open_page` wr / rd, union |
|---|---|---|
| 512 / 128 | 296 .. 301 / 454 .. 457, 593 .. 601 | 297 .. 300 / 455, 593 .. 600 |
| 512 / 255 | 290 .. 292 / 357, 580 .. 583 | 291 .. 293 / 359, 582 .. 586 |
| 256 / 128 | 284 .. 288 / 345 .. 350, 568 .. 576 | 284 .. 286 / 345, 568 .. 571 |
| 256 / 255 | 305 .. 306 / 279 .. 284, 558 .. 568 | 306 / 280 .. 281, 559 .. 563 |

Every point is one mode within 2 percent on 40 / 40 phases of both presets.

## 6. Record

- Model: `dir_mode`, `wr_starve`, `wr_burst` (GraniteSKU knobs and
  `ModelConfig` fields; preset `sku_rdprio` = 512 / 16); `dir_mode 0`
  reproduces the committed `_rfcb_2026-11-24` CSVs to the cycle on all four
  configs.
- `sustained` suite: the mixed family's `param` lengthens the read (> 0) or
  write (< 0) streams; `mixed_rd16_bl8` added for the steady contended rate.
  Not a board suite.
- Frontend stat `writes_at_read_last`; CSV column `wr_bw_rd_live_mb_s`.
- Model tests `test_read_priority_register_makes_the_mixed_cell_one_mode_and_bounds_the_writes`
  and `test_contended_write_rate_is_measured_while_the_reads_hold_the_bus`;
  48 / 48.
