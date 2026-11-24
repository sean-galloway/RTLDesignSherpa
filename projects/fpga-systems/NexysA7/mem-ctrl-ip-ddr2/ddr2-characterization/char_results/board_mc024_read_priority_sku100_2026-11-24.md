# MC-024 on the board: read priority makes the mixed cell one mode on every run, +7 percent union on both open-page presets

> memory-controllers MC-024, 2026-11-24. The sys100 SKU bitstream with the
> read-priority register (`fpga/bitstream/ddr2_char_granite_sku100_mc024_2026-11-24.bit`,
> WNS +0.003, 0 failing; `proxy_mc024_read_priority_rtl_2026-11-24.md` section 4),
> run under decision 2's benchmark rule: every cell at the power-on defaults
> AND at its optimized settings.

## 1. The run

Nexys A7-100T, 100 MHz, the host default. Smoke: init, write_read, memtest
(32 / 32 chunks over 128 MB) PASS. Two passes, each `windows` x3 + `every` x1
(`--txn-scale 4000`):

- **A, the power-on register** (`dir_mode` 0, the symmetric register):
  `char_granite_sku100mc024{,w2,w3}_windows_2026-11-24.csv`,
  `char_granite_sku100mc024_every_2026-11-24.csv`.
- **B, read priority on every preset** (`TEST_READ_PRIORITY=1`, 512 / 128 at
  the CSR reset): `char_granite_sku100mc024rp{,w2,w3}_windows_2026-11-24.csv`,
  `char_granite_sku100mc024rp_every_2026-11-24.csv`.

Both passes make the same register writes (every config writes
`SCHED_DIR_RP` and `SCHED_POLICY.dir_mode`; only the mode bit differs), so
the A/B carries no GO shift between its arms. Against the 11-22 board record
(`sku100rpap`) every config now makes those two extra writes, so pass A, not
the older runs, is the baseline here. **0 mismatched beats on all 154 cell x
setting results.**

## 2. The mixed cell

| preset | A: symmetric, runs 1 / 2 / 3 (wr / rd MB/s) | B: read priority, runs 1 / 2 / 3 | model, `sku_rdprio` |
|---|---|---|---|
| `defaults` | 277 / 276 x3 (union 553) | **297 / 455 x3 (union 594)** | 299 / 456 (599) |
| `open_page` | 280 / 280 x3 (union 559) | **297 / 455 x3 (union 594)** | 297 / 456 (594) |
| `close_page` | 73 / 121 x3 (union 146) | 71 / 113 x3 (union 143) | 72 / 114 (143) |

- One mode on every run under both registers on this bitstream; with read
  priority it is the mode the model and the proxy priced (proxy 297 .. 305 /
  455 .. 457 on five refresh phases), for both open-page presets alike. The
  symmetric register was slow on all six open-page runs here, as on 18 of
  the 20 earlier SKU runs MC-023 counted (`open_page` 8 / 10, `defaults` 10 / 10); under read priority there is no slow mode to draw.
- Union +7.4 percent (`defaults`) and +6.3 percent (`open_page`); reads
  +65 / +63 percent, writes +7 / +6 percent.
- `close_page` loses 5 percent of the reads under read priority, as the
  model said: its optimized setting is the symmetric register.

## 3. Every cell at the power-on defaults and at its best setting

The best of the eight settings measured (`defaults`, `open_page`,
`close_page`, `bank_interleave` x {symmetric, read priority}; `windows` the
mean of three runs), ranked by wr + rd MB/s; "power-on" where nothing beats
the defaults by more than 0.5 percent. (`every` runs `col_major_bl8_multiid`
twice per config, once from the medium-level variants and once from the
full-level per-family loop -- the suite has done so since it was written;
the first row is used.)

| profile | cell | power-on wr / rd (wr + rd) | best setting | best wr / rd (wr + rd) | gain |
|---|---|---|---|---|---|
| windows | mixed_bl8 | 277 / 276 (553) | defaults + rd_priority | 297 / 455 (752) | +36.0% |
| windows | row_thrash_bl8 | 770 / 772 (1542) | power-on | 774 / 774 (1549) | +0.4% |
| windows | random_bl8 | 729 / 754 (1483) | open_page | 736 / 761 (1498) | +1.0% |
| every | incremental_bl4 | 776 / 777 (1554) | power-on | 777 / 779 (1557) | +0.2% |
| every | incremental_bl8 | 777 / 777 (1554) | power-on | 777 / 779 (1557) | +0.2% |
| every | incremental_bl16 | 777 / 777 (1554) | power-on | 777 / 779 (1557) | +0.2% |
| every | row_major_bl4 | 777 / 779 (1557) | power-on | 777 / 779 (1557) | +0.0% |
| every | row_major_bl8 | 777 / 779 (1557) | power-on | 777 / 779 (1557) | +0.0% |
| every | row_major_bl16 | 777 / 779 (1557) | power-on | 777 / 779 (1557) | +0.0% |
| every | col_major_bl4 | 311 / 389 (701) | bank_interleave | 442 / 518 (961) | +37.1% |
| every | col_major_bl8 | 446 / 520 (965) | bank_interleave | 583 / 583 (1166) | +20.8% |
| every | col_major_bl16 | 565 / 623 (1188) | power-on | 565 / 623 (1188) | +0.0% |
| every | col_major_interleaved_bl4 | 768 / 766 (1534) | open_page | 773 / 770 (1543) | +0.5% |
| every | col_major_interleaved_bl8 | 770 / 770 (1541) | open_page + rd_priority | 774 / 774 (1549) | +0.5% |
| every | col_major_interleaved_bl16 | 776 / 774 (1550) | power-on | 776 / 777 (1553) | +0.2% |
| every | col_major_bl8_multiid | 446 / 520 (965) | bank_interleave | 583 / 583 (1165) | +20.8% |
| every | col_major_bl8_gap | 376 / 400 (776) | power-on | 376 / 400 (776) | +0.0% |
| every | incremental_bl8_multiid | 776 / 777 (1554) | power-on | 777 / 779 (1557) | +0.2% |
| every | row_major_bl8_multiid | 777 / 779 (1557) | power-on | 777 / 779 (1557) | +0.0% |
| every | col_major_interleaved_bl8_multiid | 770 / 770 (1540) | open_page | 774 / 774 (1549) | +0.5% |

- Read priority is the best setting for the mixed cell only; every
  single-direction cell is within 1 percent under both registers on the
  open-page presets (it has no contended bus to arbitrate).
- The large wins elsewhere are page/address presets, not the register:
  `bank_interleave` on the col_major bl4 / bl8 cells (+21 .. +37 percent),
  known since MC-020.
- `bank_interleave`'s per-pass levels (~517 / 566 / 583) moved between
  passes A and B on seven cells (-1.5 .. +2.2 percent): ISSUE-007's draw,
  present under both registers.

## 4. The model against both passes

`char_model.py board-compare`, the four SKU configs:

- Pass A against the committed model (`_rfcb_2026-11-24`):
  **56 in / 1 out** (`compare_model_sku_rfcb_vs_board_sku100mc024_2026-11-24.md`).
- Pass B against the model at `dir_mode` 1
  (`model_ramulator2_ddr2_granite_sku100*_rdprio_2026-11-24.csv`):
  **56 in / 1 out** (`compare_model_sku_rdprio_vs_board_sku100mc024rp_2026-11-24.md`);
  the three mixed cells within +0.1 .. +0.8 percent of the union.
- The one OUT in each is `bank_interleave row_major_bl16`'s write on the
  517 / 521 level (model 582): ISSUE-007.

## 5. Closes

MC-024's done-when: the board's mixed cell within tolerance of
`sku_rdprio` (section 4), one mode on every run, 0 mismatched. ISSUE-005
(the open-page mixed cell's two modes) closes into MC-024: with read priority
there is one mode on every refresh phase (the proxy, five; the model, 40) and
every board run (six); the symmetric register at power-on keeps the race,
which the power-on rule (decision 2) accepts as the generic setting.
