# Model: the store's write record waits for the fill (memory-controllers MC-021 step 6), 2026-11-19

The last write-side cells out between the SKU model and the board after step
5 -- `close_page col_major_interleaved_bl8` (model 287, board 250) and `_bl16`
(208 against 171), the proxy equal to the board on both -- are one register
of the store: the write head record is `has0 && r_wr_fdone[s0]`, the read
record `has0`. A write beat is the pick's request two cycles later than a read
beat after it lands in its bank queue, and under close page every burst's
first beat lands in an empty queue. The model carries it as `wr_fill_lag` (2).

| cell (close_page, write / read MB/s) | board (step 5) | model step 5 | model step 6 |
|---|---|---|---|
| col_major_interleaved_bl4 | 386 / 387 | 388 / 389 | 388 / 389 |
| col_major_interleaved_bl8 | 250 / 361 | 287 / 334 | **251** / 334 |
| col_major_interleaved_bl16 | 171 / 238 | 208 / 239 | **172** / 239 |

The write cycles land within 0.6 percent of the board's on all three (bl16
4,868,366 against 4,895,826; bl8 1,672,079 against 1,678,178; bl4 540,932
against 542,629). The read sides do not move: the term is the write record's.

## 1. The probes: same stream, same banks, a longer bank cycle

Two 4000-cycle pick probes on the proxy's bl16 cell (`PERF_PICK_PROBE_FLIP=1`
for the write pass, `2` for the read pass, with the DRAM trace), beside the
model's debug dump of the same cell (800 slots of each pass). Hop
distributions from the fire events alone (`hops2.py`, pairs 0-15):

| write pass | RTL (4000 cycles) | model (800 slots) |
|---|---|---|
| beats per cycle | 0.214 | 0.270 |
| holds per ACT | 0.48 (413 / 861) | 0.11 (24 / 215) |
| ACT -> column | 2: 445, 5: 412 | 2: 202, 5: 13 |
| column -> next ACT, same bank | 8: 283, 9: 305, 10: 202 | 8: 182, 9: 11, 10: 5 |
| ACT -> ACT, same bank (mean) | 10-15 flat (12.6) | 10: 179 of 199 (10.4) |
| ACT from the lane | 115 of 861 | 7 of 215 |

| read pass | RTL | model |
|---|---|---|
| beats per cycle | 0.293 | 0.300 |
| holds per ACT | 0.10 | 0.07 |
| ACT -> column | 2: 1060, 5: 112 | 2: 233, 5: 6 |
| column -> next ACT | 7: 863, 8: 96, 9: 25 | 7: 210 |

The regime is the same on both sides: the pool straddles the same number of
bursts (27-28 other-bank beats inside a 16-beat burst in both; the per-bank
depths in the model's dump are three banks, 2 / 8 / 5), and the read pass
matches as it does on the board. The whole write-side gap is the bank cycle:
12.6 cycles against 10.4 for the same three banks.

## 2. Every hold is one mechanism

All 413 of the RTL's write-pass holds are the same event: a main ACT fires
for pair A while pair B's row request is live in the same cycle; the select
picks B's ACT for the next cycle; it cannot fire (tRRD 2) and holds; the hold
discards A's next-op hint; A's column request becomes visible at ACT + 3 and
fires at ACT + 5 behind B's hinted column at B + 2. Now A's and B's columns
are adjacent, their row requests come up adjacent at column + 7, and the
pattern repeats with the roles swapped: a two-bank lock at period 12 (11 and
13 alternating), and a third bank that lands in it makes three serial ACTs at
the tRRD spacing with two holds, period 13-14. The RTL's hold gaps are 2,
11 and 12 for the whole 4000 cycles except the five refresh windows.

The model has the lock. After the refresh in its dump (slots 10138-10156) two
row requests come up together, the first hold follows, and the lock runs for
130 slots (holds every 12). It dissolves when a locked partner's burst ends:
the next bank's first request lands ONE slot after the remaining bank's ACT,
the lane picks that ACT to ride beside the hinted column, and the three banks
settle into a 10-slot rotation with no holds (ACTs 3-4 slots apart). The RTL
re-locks at every burst transition instead -- its new bank's request lands IN
the remaining bank's fire cycle, not the slot after.

## 3. The arrival: three cycles for a write, one for a read

From the probe's bank queue counters (banks 0 and 1 carry them): a column
fire frees a pool slot, the next W beat lands in its bank queue 3 cycles later
in every instance, and the new bank's row request is visible 3 cycles after
the landing in every instance of the write pass; in the read pass the request
follows the landing by 1. The model's request follows the landing by 1 on both
sides (the staged beat enqueues at `admit_lag` 3 and the decode registers it).

The store (`mc_bank_fifo_store.sv`, the head record block): the write record
is valid only when the entry's data fill is done and the fill-done register
is set (`h.vld = has0 && r_wr_fdone[s0] && !merge-this-cycle`, the TASK-006
form that keeps a write from committing before its data); the read record is
`has0`. Those are the two cycles. They matter only where a bank's queue was
EMPTY when the beat landed -- a continuing queue's next head was filled long
before it is head -- which is every burst's first beat under close page, and
nowhere in the single-bank open-page streams. The two cycles put the new
bank's first ACT in the collision slot of the banks already cycling (their row
requests come up at column + 7, the new bank's at the freeing column + 6);
one slot earlier, the model's, and the lane rides it beside the hinted column.

## 4. The term

`wr_fill_lag` (default 2): a write beat is a head record `admit_lag +
wr_fill_lag` slots after its acceptance, and until then its pair has no head
(the queue is in order; an unfilled oldest beat blocks the pair). A read beat
is a head record at `admit_lag`, as before. `sku_wrfill0` is the model before.
The pool slot is held from the acceptance in both, so the admission itself
does not move.

The term is in `granite_sku_controller.cpp` (`m_wr_fill_lag`, `build_heads`),
`char_model.py` (`ModelConfig.wr_fill_lag`, the variant, the docstring) and
`test_char_model.py` (`test_wr_fill_lag_is_the_write_records_fill_gate`: the
bl8 write side at 4096 beats falls to 0.87 of the fill-less model, the read
side within 2 percent; the shipped-point test asserts the default). The
step-4 hit-lag test's write band widened: with the fill lag the hit_lag-1
counterfactual's write side is 321 (283 without), the shipped side 258 either
way. 38 / 38 and the vendor's 217 pass.

Full run of the three model configs against the step-5 board set
(`compare_model_sku_vs_board_sku100s4_s6_2026-11-19.md`): **56 in / 1 out** of 57, the one out
`open_page mixed_bl8` (the board's fast mode 311 / 522 against the model's 271 /
271, union -12.9; the board's slow mode is 272 / 272). Against the step-5 model:
the SKU's 15 cells moved 2.2 percent at most (`mixed_bl8` 277 / 277 -> 271 /
271, the board's slow mode 272 / 273); `close_page` moved toward the board on
five cells (`incremental` 83 -> 82 against 82, interleaved bl8 / bl16 as
above, `row_thrash` write 249 -> 243 against 238, `random` write 218 -> 205
against 203) and away on one: `close_page mixed_bl8`'s read side 75 -> 116
against the board's 59 (union 117 -> 125 against 112, +3.6 -> +11.2 percent,
inside the 15 tolerance). That cell is MC-021's next item (the direction
register under close page with four writers and four readers), and the fill
lag now sits in it as a second term to weigh.

## 5. Two lessons for the method

- **Measure the arrival path per direction.** The pick's view of a beat is
  the store's record, and the store's write and read records are built from
  different gates. The single `admit_lag` measured in ISSUE-004 was the read
  path's; the write path is two registers longer and only shows where queues
  empty, which the single-bank cells never do.
- **A histogram over half the pairs reads like a mechanism.** The first pass
  of the hop script indexed pairs 0-7 of 16 and counted 214 collisions against
  413 holds, which looked like two mechanisms; fixing the range made it one.
  Check a per-pair script against the fire count before reading it.

## Record

- `model_ramulator2_ddr2_granite_sku100{,_bi,_close}_s6_2026-11-19.csv`, the
  compare above; the step-5 board set `char_granite_sku100s4_*_2026-11-19.csv`.
- The probes and scripts in the session scratchpad (`pick_close_ilv16_long{1,2}.json`,
  `hops2.py`, `win_dump.py`); the model dump `model_close_ilv16_s4.out`.
- Previous step: `model_mc021_hit_lag_2026-11-19.md`, `board_mc021s4_granite_sku100_2026-11-19.md`.
