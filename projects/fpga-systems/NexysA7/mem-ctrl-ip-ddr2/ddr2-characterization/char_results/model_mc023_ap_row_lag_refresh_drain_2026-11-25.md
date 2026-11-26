# MC-023 items 1 and 4: the same-row ACT after a self-close is at fire + 4, and the refresh drain is one PRE per two slots

> memory-controllers MC-023, 2026-11-25. Item 1 closed with one term,
> `ap_row_lag`, now the SKU default. Item 4 has a second term,
> `ref_drain_pb`, measured on the RTL and kept as a knob: it fixes
> `open_page`'s mixed cell and breaks `defaults`'. Proxy:
> `test_granite_char_perf`, 100 MHz, `TEST_DUAL=1`, phase-exact default.

## 1. Item 1: the close_page read sides

Every close_page read side was 10 .. 12.5 percent high in the committed model
(incremental 104 against the board's 93) and every write side exact.

The proxy (close_page incremental, one generator, `PERF_DRAM_TRACE`) shows the
per-bank read chain as ACT, RD + AP at + 2, the self-close at ACT + tRAS 5,
and the next ACT at + 9 MC: fire -> ACT 4. The model had the chain at 8 MC
(fire -> ACT 3), because its same-row rule raised the ACT request the slot the
timer opened. The RTL's head of the closed row reads as a hit until the row
image clears the slot after the fire, then the record re-classifies it.

Term `ap_row_lag` (`granite_sku_controller.cpp`): a head of the row the
self-close closed decodes no ACT request before fire + 2, so its ACT fires at
fire + 4. A head of another row keeps the lookahead. `sku_noaprowlag` is the
model before.

The `ap_close_rec` probe went the other way (incremental 138) because it
dropped the same-row rule's no-lookahead before the fire, so the ACT was
armed early. A delay term has to keep the gate the event comes after.

Against the SKU board set (`compare_model_sku_aprowlag_vs_board_sku100rpap_2026-11-25.md`):
**57 in / 0 out**, the largest delta 12.5 -> 4.4 percent.

| cell | board wr / rd | before | now |
|---|---|---|---|
| close_page incremental_bl8 | 92 / 93 | 92 / 104 | 92 / 93 |
| close_page row_major_bl8 | 87 / 87 | 87 / 98 | 87 / 87 |
| close_page col_major_bl4 | 92 / 95 | 92 / 105 | 92 / 95 |
| close_page row_thrash_bl8 | 344 / 354 | 345 / 390 | 345 / 358 |
| close_page random_bl8 | 270 / 283 | 271 / 310 | 271 / 282 |
| close_page mixed_bl8 | 73 / 121 | 73 / 121 | 73 / 121 |
| bank_interleave col_major_interleaved_bl4 | 356 / 361 | 354 / 394 | 354 / 361 |
| bank_interleave row_major_bl8 | 582 / 566 | 582 / 579 | 582 / 590 |

Twenty cells moved, all close_page or bank_interleave. Three bank_interleave
row_major reads moved away from the board (+2.3 -> +4.4 percent); these are
item 3's refresh-orbit cells. Model tests 49 / 49, including
`test_ap_row_lag_puts_the_same_row_act_at_the_self_close_plus_four`.

## 2. Item 4: the refresh drain

`mc_bank_pick`'s refresh override closes the open banks one PRE per slot. Each
slot it takes the lowest bank that the REGISTERED row image (`r_row_act`) shows
open with its REGISTERED pre-ready (`r_pre_rdy`). A PRE fired last slot still
reads open, so the next slot re-picks that bank, the live gate refuses it, and
the slot is lost. The REF follows when the image shows every bank closed and
every bank is ACT-ready.

The proxy traces (`mixed`, 4 generators, TXN 512, tREFI 779) show it on every
episode: PREs two slots apart, the REF at the last PRE + tRP, and the first
ACT at the REF + 16. With one bank open, a refresh in a write turn costs 21 MC
from the last demand command and one in a read turn costs 19, plus 2 per
further bank (`defaults` 33 / 26 / 11 / 9 of 91 episodes on those four
shapes). The committed model closes every bank with one PREab.

Term `ref_drain_pb` (`sku_refdrainpb`) implements the override's scan: the
image and the pre-ready are taken at the start of the slot before, and a bank
whose self-close is pending holds the REF without taking a PRE. On the same
cell at 779 it reads 280.47 / 282.48 against the RTL's 280.5 / 282.4.

The modes at the board's full count, 40 GO phases (`defaults` and `open_page`
`mixed_bl8`):

| model | `defaults` | `open_page` |
|---|---|---|
| committed (`ap_row_lag` 2) | 278 / 278 x27; 303 .. 308 / 618 .. 622 x13 | 289 .. 291 / 366 .. 369 x40 |
| `ref_drain_pb` | 293 / 406 .. 410 x21; 301 .. 302 / 566 .. 570 x19 | **280 / 280 x27; 302 / 578 .. 580 x13** |
| board, `REF_ALIGN` 0 .. 700 (MC-025) | 277 / 276 x8 | 280 / 280 x5; 303 / 593 .. 594 x3 |

With the drain, `open_page` is in the board's two modes and nearly its
proportion (32 percent fast, the board's 38), with the fast read 2.4 percent
under. The intermediate mode is gone. `defaults` (the hybrid policy, the
shipped preset) leaves the board's one mode on every phase, so the term is not
the default. It is the RTL's drain, so `defaults` held its mode in the
committed model by compensation: a cheap drain offsetting a hybrid-path cost
the model still lacks.

One-knob probes of `defaults` with the drain on, 40 phases each: `tr_init` 0
gives 291 / 388 x33; the lane ACT-only 300 / 535 .. 541 x40; `drain_arm_max_cols`
0 gives 291 / 379 .. 389 x33. Only `pred_cmd_reg` false moves it toward the
board (281 / 313 x30, 280 / 280 x6, 279 / 279 x4). Granite builds
`PRED_CMD_REG = 1`, so that is not the term, but it says the policy's history
across a refresh episode is where to look next.

## 3. A method note: compare refresh modes by proportion

The model at the board's eight `REF_ALIGN` offsets (GO offset
2 (780 - o - 1) ticks, with launch shifts of -20 .. +20 MC) changes mode
within a 10-MC shift on both presets. The mode at one offset depends on a
launch latency neither side pins, so a per-offset match is not a test. The
proportion of modes across offsets is.

## 4. Record

- Model CSVs: `model_ramulator2_ddr2_granite_sku100{,_open,_bi,_close}_aprowlag_2026-11-25.csv`
  (the committed defaults).
- Proxy: close_page incremental at 1 and 4 generators (TXN 128); `mixed`
  `open_page` and `defaults` at tREFI 779 (TXN 512, DRAM traces).
- Open in MC-023: item 3 (the bank_interleave orbits) and item 4's `defaults`
  term.
