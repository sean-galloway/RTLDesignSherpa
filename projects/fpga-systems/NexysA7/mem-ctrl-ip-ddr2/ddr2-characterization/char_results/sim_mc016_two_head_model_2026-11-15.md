# The two-head store, modelled: the second head is the same burst, and granite's `mixed` gap is the direction rule (memory-controllers MC-016, 2026-11-15)

MC-013 item 4 priced granite's queue shape on the Ramulator 2 DDR2 model:
strict per-bank FIFOs with a rotor and a column-first select (`BankFIFO-RR`)
give 320 / 320 MB/s on `mixed_bl8` where the pooled row-hit-first queue gives
360, equal on every single-direction family. MC-016 was filed on the reading
that granite's store sits between the two, because `HEAD2_EN` keeps two head
records per bank and "the pick can see one record past a conflicting head".
This is the model step the task asked for first. It closes the task without
RTL: the premise is wrong in two places, and the number that matters for
`mixed` is not the queue's.

Same point as MC-013: DDR2-400 x16, 100 MHz MC / CK 200, `open32` = pooled
FR-FCFS with 32-deep read and write queues, `open16` / `open8` the same at
16 / 8 (granite's pool at 16 and 8: MC-015, `GRANITE_SEAM_N`). Model cells
are write / read MB/s; on `mixed` the two directions share one window, so
the union (both directions' bytes over that window) is twice the cell.

## 1. The RTL: head2 is not a scheduling peek

`mc_bank_pick` reads the second record in exactly one place:
`w_cand[p] = r_shadow[p] ? w_rec2[p] : w_rec1[p]`, where `r_shadow` is the
pair whose column fired last cycle. The head record is registered one cycle
behind the store, so in the cycle after a pop the pick serves the pair from
its second record, which by then is the head; outside that cycle head2 is
never read. Its `hit` is not a compare against the open row: it is the
stored "same row as the entry ahead" bit (the store's header,
`mc_bank_fifo_store`: the compare form cost a 14-bit 8:1 row mux and a
14-bit compare per record, sixteen records, and was dropped). The store
keeps the queues as `gaxi_age_fifo_sync` with `PEEK = 2`: the FIFO exposes
the entries behind its head and pops the head only. In scheduling terms
granite's store is the model's strict FIFO (`open*_bankrr_col`), not a point
between the columns.

## 2. The model: a peek shallower than a burst changes nothing

`BankFIFO-RR` got a `peek_depth` (overlay
`bank_fifo_rr.cpp`, default 1 = the strict FIFO): a bank whose head is a row
conflict (its next command closes the open row) offers instead the oldest
row hit among its first N entries, if no older entry in the window carries
the same address; a head that is a miss on a closed bank keeps its place
(nothing behind it can be a hit). N = 2 is the two-head store if the pick
could fire the second record on its own hit; N = the queue depth is the
per-bank pooled hit-first bound (`_allh`).

Captured `mixed` trace (MC-013 item 5, the controller's own port; the
`run-trace` column), with the row hits / misses / conflicts the model counts
for the read direction and the ticks the frontend spent held on a full
queue:

| pool | pooled FR-FCFS | pooled row-hit-first | strict FIFO (`_col`) | peek 2 | peek 4 | peek 8 | peek 16 | whole queue | rd hits / miss / conf (`_col` -> whole) | stall ticks (`_col` -> whole) |
|---|---|---|---|---|---|---|---|---|---|---|
| 32 | 363 | 388 | 342 | **342** | **342** | **342** | 381 | 374 | 28515 / 67 / 4186 -> 31124 / 89 / 1555 | 11003 -> 4491 |
| 16 | 364 | 388 | 349 | **349** | **349** | **349** | -- | 357 | 28470 / 92 / 4206 -> 28530 / 90 / 4148 | 9550 -> 7955 |
| 8 | 386 | 386 | 375 | **375** | **375** | -- | -- | **375** | 28479 / 81 / 4208 (unchanged) | 4353 (unchanged) |

The rebuilt `mixed` stream (MC-013's beat-alternating build, kept for
continuity with its tables) says the same thing one row down: 320 / 320 at
pool 32 for the strict FIFO and for peek 2, 4 and 8; 351 at peek 16 and the
whole queue; 297 at pool 16 for every depth up to 8 and 298 for the whole
queue; 271 at pool 8 for every depth including the whole queue.

- **Peek 2, 4 and 8 are bit-identical to the strict FIFO** -- the same
  cycles, hits, conflicts and stalls -- at every pool depth, on both streams.
  One store entry is one BL4 column, one AXI beat; an AxLEN-8 burst is eight
  consecutive entries of one row in one bank's queue. The entry behind a
  conflicting head is its own burst's next beat, so the two-head record's
  "hit" (same row as the head) is a conflict too. A hit behind a conflict is
  at least eight entries deep, and at pool 8 one burst is the whole queue.
- The first depth that moves is 16 at pool 32 (342 -> 381 captured, the
  conflicts 4186 -> 1577); the whole 32-deep queue is lower (374): the
  deeper reorder lengthens one direction's run and the frontend's stall on
  the other queue grows back (4491 ticks against 3284). At pool 16 the whole
  queue buys 8 MB/s; at pool 8, nothing.
- The pooled queue's gain over the strict FIFO is 3 percent at pool 8 (386
  vs 375), 11 percent at 16 and 13 percent at 32 -- and its mechanism in the
  model is the frontend stall, not the conflicts: the strict FIFO's
  conflicts equal the pooled queue's (4186 vs 4201 at pool 32) while its
  stall ticks are five times higher (11003 vs 2006). The model's frontend
  is one in-order stream; a full queue in one direction holds the other
  direction's requests too. Granite's AXI port has independent write and
  read channels, so this part of the model's gap does not transfer.

The single-direction families (`model_ramulator2_ddr2_<config>_2026-11-15.csv`,
the rebuilt suite): every cell equal to the strict FIFO's at every peek depth
and pool depth -- `incremental` / `row_major` 781 / 783, `col_major` 465 / 570,
`col_major_interleaved` 780-781 / 782-783, `row_thrash` 780-781 / 782,
`random` 775 / 780 at 32 (the whole-queue peek 777 / 781), 758 / 772 at 16,
709 / 746 at 8. A peek is inert where there is one direction and one row per
bank at a time.

## 3. Where granite's `mixed` number actually is

The union (both directions' bytes over the longer of the two windows: the
board CSV's "union", the proxy's `mixed_bw_mb_s`), model and granite at the
same pool depth:

| pool | model strict FIFO (granite's shape) | model pooled row-hit-first | granite sim, lane on | granite board, lane on (`defaults` / `open_page`) | granite `rd_lat_max` (sim, cycles) |
|---|---|---|---|---|---|
| 8 | 750 | 773 | 600 (475 / 300) | 599 (487 / 300) / 668 (334 / 649) | 52 120 |
| 16 | 698 | 776 | 533 (473 / 267) | 635 (318 / 649) / 571 (473 / 286) | 52 860 |
| 32 | 684 | 776 | -- | -- | -- |

Granite sits 20 percent under the model's strict FIFO at pool 8 and 24
percent at pool 16; the strict FIFO sits 3 and 10 percent under the best
pooled queue. The granite cells are asymmetric where the model's are not,
and `rd_lat_max` of 52 000 cycles is a read that waited out the write side's
whole run: the direction register holds a direction while it has pending
columns, up to the 255-column batch cap, and on `mixed` the owning
direction's four injectors keep its heads queued so the cap is the only
flip. That is the direction rule, filed as **MC-017** with the probe and the
sweep it needs. The queue shape costs granite at most what it costs the
model -- 3 percent at the pool the SKU ships, 11 at 16 -- and nothing of it
is reachable with a two-record peek.

The MC-015 observation that `mixed` loses with the deeper pool is in the
model too, for the strict FIFO: 750 -> 698 -> 684 at 8 / 16 / 32 (the
pooled row-hit-first queue is flat, 773-776). A per-bank FIFO's cost on a
two-direction load grows with the queue it can fill.

## 4. What this task does not propose

No RTL. A cross-bank row-hit preference already exists in the pick's class
order (a COL request beats ACT and PRE at the arbiter; MC-013's `_col`
column is that select, and it is the one the model says ties the pooled
queue on every single-direction family). An intra-bank peek that moves
`mixed` has to look a whole burst past the head: a row compare per record
(the form the store rejected for area), a mid-queue pop that
`gaxi_age_fifo_sync` does not have, and a fire path that reads a record
outside the pop shadow -- for a 3 to 11 percent model bound on one family
whose measured gap is a different mechanism. MC-017 goes after that
mechanism; if it closes the 20-24 percent, the queue shape's residue is
re-priced from these tables.

## Method

- **Read the consumer before modelling the producer.** The task's premise
  ("the pick can see one record past a conflicting head") came from the
  store's port list; the pick reads head2 in one expression, under one
  condition. One grep settled what the model would otherwise have been built
  to approximate.
- **A peek is measured in bursts, not entries.** Any lookahead on a
  beat-granular queue has to be sized against AxLEN before it is sized
  against the pool; at AxLEN 8 the first seven entries behind a head are
  known in advance to be its own row.
- **Compare unions on a two-direction window.** The per-direction cells on
  `mixed` are each measured over their own window and the model's are over a
  shared one; MC-013 put granite's 330 beside the model's 370 and read a 10
  percent gap, where the unions read 524 against 740 (lane off, both). The CSV already carried
  the union in its notes column.
- **Say which half of a model's gap transfers.** The pooled queue's gain here
  is mostly frontend stall on a single in-order stream, which the RTL's two
  AXI channels do not have; the conflict counts, which do transfer, are
  equal.

## Recipe

    # the scheduler: overlay/src/ramulator/controller/scheduler/impl/bank_fifo_rr.cpp (peek_depth), copied into
    # vendor/ramulator2 and rebuilt (make -j in vendor/ramulator2/build; codegen regenerates the Python wrapper)
    cd projects/components/mem-ctrl-ip/references/ramulator2 && python3 -m pytest tests -q       # 25 passed
    cd vendor/ramulator2 && PYTHONPATH=python python3 -m pytest tests/smoke tests/device_timings -q   # 215 passed
    M=projects/components/mem-ctrl-ip/references/ramulator2/bin/char_model.py   # PYTHONPATH=vendor/ramulator2/python
    for c in open32_bankrr_col open32_bankrr_2h open32_bankrr_4h open32_bankrr_8h open32_bankrr_16h open32_bankrr_allh \
             open16_bankrr_col ... open8_bankrr_allh open8 open8_rowhit open16 open16_rowhit; do
      python3 $M run-trace --config $c --name mixed_bl8 --both <mc013 traces>/mixed.trace \
          --out <char_results>/model_ramulator2_ddr2_mixed_captured_mc016_2026-11-15.csv
      python3 $M run --config $c --suite all --out <char_results>/model_ramulator2_ddr2_${c}_2026-11-15.csv
    done
