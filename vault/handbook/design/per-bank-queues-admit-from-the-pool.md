---
title: Per-bank queues admit from the pool, not from the bank
summary: Behind one in-order AXI address channel, any admission condition finer than "the pool has a free slot" is head-of-line blocking for every other bank. A per-(direction, bank) cap of 4 on granite's FIFO store cost 23 percent at eight threads and deadlocked the concurrent family, because an 8-beat burst chops into 8 same-bank entries (2026-10-23). Size bank queues to the pool and keep the records O(1) per depth.
---

# Per-bank queues admit from the pool, not from the bank

**Rule:** a storage backend that keeps per-bank queues of descriptors must
still admit a request on the pool condition alone ("a slot is free"). The
AXI address channel in front of it is a single in-order stream: when the
store refuses the head request because *its* bank's queue is full, every
request behind it, to every other bank, waits with it. The per-bank depth is
therefore not a tuning knob for area; it must be the pool size, and the
per-depth cost has to be made negligible some other way (store the derived
facts at push instead of comparing at the head).

## The failure that taught it

granite's `mc_bank_fifo_store` (recovery plan Phase 4, report 5.10 item 1)
replaced the flat entry store and its N x N age matrix with per-(direction,
bank) FIFOs of slots. The first cut capped each FIFO at `BANK_FIFO_DEPTH = 4`
"to keep the record loops shallow" and gated `aw_push_ready` /
`ar_push_ready` on `cnt != 4`. The granite suite passed (6 / 6, one benign
xpass) and so did the single-bank streams. Then the eight-thread grid came
back:

| family, 8 threads | entry store wr/rd MB/s | FIFO store cap 4 |
|---|---|---|
| incremental | 557 / 555 | 429 / 476 |
| row_major | 558 / 557 | 429 / 476 |
| col_ilv | 534 / 526 | 414 / 458 |
| col_major | 459 / 458 | 386 / 421 |
| random | 442 / 453 | 370 / 407 |
| mixed (two threads per bank, concurrent R/W) | 98 | **did not complete** |

and the one-thread `col_ilv` cell lost 17 percent (385 vs 461) with a
single stream in flight. The one-thread loss is the tell: no two threads
shared a bank, yet the cap still bit. On the board geometry (BL4 x16, 8-byte
DRAM bursts) the write splitter chops one 8-beat AXI burst into 8 same-bank
entries, so a depth of 4 blocks the address channel half way through
*every* burst, and the next burst's bank -- the parallelism `col_ilv` and
`random` exist to expose -- cannot be admitted until the first bank drains.
Under `mixed` (two threads per bank on banks 0-3) the DRAM went silent at
8.127 ms and stayed silent for 15 600 cycles: the test gave up on an engine
that never finished.

## What landed

- Bank queues are pool-deep (`BANK_FIFO_DEPTH = 0` means `NUM_ENTRIES`);
  admission is `pool has a free slot` for writes and the same plus a return
  ticket for reads -- exactly the entry store's.
- The record flag that made depth expensive, same-row-behind, is a stored
  bit per queue position: at push the incoming row is compared with the
  bank's registered tail row (one compare per direction per cycle), and the
  bit rides the position through the pack-on-pop. `mc_bank_pick` already
  reads the flag as "the entry behind this one shares its row", which for an
  in-order per-bank queue is exactly that bit. The only per-cycle compares
  left are the heads' row hits against the open-row image.
- The second record's hit is that stored bit too (pumice TASK-052). The
  pick core reads head2 only under its pop shadow, the cycle after it fired
  the head as a column; the record it reads was formed while that column
  fired, against an image showing the head's row open, so "head2's row ==
  the open row" is "head2's row == head's row": the pushed bit. The
  general rule: a record consumed in exactly one known cycle may be derived
  from what that cycle implies instead of computed for every cycle. Store
  3 096 -> 2 627 LUT, cycle-identical on every cell.
- One head record per bank was measured and is a no at BL4 x16: an 8-beat
  burst is eight same-bank entries, so the pop shadow is the common case;
  the single-bank stream halves (292 vs 568 MB/s) and eight threads lose 20
  to 26 percent for 281 LUT. It is a knob (`HEAD2_EN`), default on.
- The queues are linked lists through the slots (pumice TASK-054): a 3-bit
  `next` per slot, a same-row-as-predecessor bit per slot, head / tail /
  count per bank. A pool-deep per-bank queue needs no position storage at
  all -- every slot is in exactly one queue at a time, so the slot IS the
  position. The 8 x 8 pointer array per direction (416 flops, a 64-way
  write decode) became 24 + 8 + 48 + 32 flops; the store went 1 203 -> 806
  flops, cycle-identical on every cell. The fill-order FIFO is circular for
  the same reason as the queues: it only ever pops its head.
- The queues are circular (pop = pointer increment): the pick core always
  fires the head -- it reads the second record only in the one-cycle shadow
  after a pop -- so no pack-on-pop network is needed. The packed pool-deep
  form cost 5 822 LUT on the board, the circular one 3 894, against 5 825
  for the entry store with its records.
- The records carry no row or column: the pick core looks the command
  payload up by slot from the backend's slot fields (one mux per direction
  in the fire stage, keyed by the registered winner) instead of 32 records
  each materialising row + col. Store 3 894 -> 3 096 LUT, granite_core
  7 403 -> 6 634, timing +0.194 ns (pumice TASK-051).
- Verified: every granite grid cell equal to the entry store's number to the
  decimal (15 cells, 1 / 2 / 4 / 8 threads), row_thrash reads +14 percent at
  one thread; board builds +0.304 / +0.545 ns before the payload change
  (Phase 3 report section 5.11).

## How to check a design against it

1. List every term in each `*_push_ready`. Anything that names the request
   (its bank, its ID, its row) is a per-request admission condition and
   blocks the channel for unrelated requests when false. Justify it or
   remove it.
2. Run a one-thread bank-rotating stream (`col_ilv`) against the flat
   backend. A loss with one stream is an admission or record defect, not a
   scheduling one; multi-thread losses have too many explanations.
3. Run the concurrent family with two threads per bank. A "did not
   complete" with the DRAM silent for thousands of cycles is a deadlock,
   not the wall-clock wait (ISSUE-024): read the last command timestamp.
4. Chopped bursts: know how many entries one host burst becomes at the
   shipping geometry. Any per-bank structure shallower than that serialises
   the host's own bursts.

Related: [[dependent-hops-forward-the-pick]] (the pick side of the same
plane), [[plane-boundary-registered-snapshots]] (the records are a
registered snapshot; the pick core masks its own pop shadow).
