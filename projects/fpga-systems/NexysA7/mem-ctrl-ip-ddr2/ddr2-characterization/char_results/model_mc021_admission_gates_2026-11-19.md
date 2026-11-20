# Model: the admission is three registers, and one slot of it decides the mixed close-page turns (memory-controllers MC-021 step 7), 2026-11-19

`close_page mixed_bl8` -- four writers and four readers on two banks, rows
eight apart, under close page -- was the model's last cell off the board by a
mechanism rather than a mode: the board gives 56 / 59 (union 112), the proxy
56.3 / 57.0 (112.6), and the model after step 6 gave 62.6 / 115.7 (reads done
in 113k cycles, writes in 209k). The model's direction register held the reads
to the 255-column cap; the RTL turns the register every 16 columns. The cause
is one slot in the admission path, and the fix is to model the store's three
admission registers separately instead of as one three-slot stage.

| cell (write / read MB/s, union) | board | proxy | model step 6 | model step 7 |
|---|---|---|---|---|
| close_page mixed_bl8 | 56 / 59 (112) | 56.3 / 57.0 (112.6) | 62.6 / 115.7 | **56.3 / 57.4 (113)** |

At matched counts (512 bursts per injector) the model's write window is
232,814 cycles against the proxy's 232,852 and the read window 228,082 against
229,896. The full compare against the step-5 board set stays 56 in / 1 out
(`compare_model_sku_vs_board_sku100s4_s7_2026-11-19.md`); four cells moved
more than half a percent from step 6 (this one; `defaults mixed_bl8` 271 ->
276 against the board's 272 / 273; `close_page col_major_interleaved_bl8`
write 251 -> 254 against 250; `bank_interleave mixed_bl8` -0.3) and the SKU's
largest move is 2.1 percent. The one cell out is `open_page mixed_bl8`, the
board's fast mode (311 / 522) against the model's 276 / 276, which is the
board's slow mode (272 / 272) within 1.5 percent.

## 1. What the RTL does on this cell

The proxy's direction-flip log (`PERF_DIR_FLIPS`) over the timed phase: 556
read turns and 556 write turns, every one 16 columns (a batch histogram of 16:
1092, 32: 18), the read turn 113 cycles ending because a write column fired
(cause 0, all 556), the write turn 111 cycles ending because the writes
drained (cause 1, 555 of 556). Each turn, from the DRAM trace: 16 columns
with auto-precharge, 21-23 ACTs and 6 PREs on banks 0 and 1 -- five to seven
of the ACTs are the waiting direction's rows, opened by the lane beside the
holder's columns and closed again by the holder's PREs.

The pick probe anchored on the timed phase's second flip
(`PERF_PICK_PROBE_FLIP=3`) shows how a turn ends. During a read turn the read
queue of bank 0 sits at the cap of 6 (`BANK_CAP_MIXED`) and refills one beat
after every bank-0 read fires, while the read queue of bank 1 drains from 6 to
0 and gets nothing: the single in-order AR hold is holding a bank-0 beat the
cap refuses, and the bank-1 bursts behind it cannot be admitted. With bank 1
empty the reads serialize on bank 0 against the write row the lane keeps
re-opening (PRE, ACT, column per beat, about 14 cycles), the direction's idle
counter reaches 8, the idle hold lapses, the waiting write column becomes
eligible (`w_xdir_ok`), fires, and the register flips. The write turn mirrors
it with the write queues: bank 1's writes land (0 -> 6 in four cycles) as soon
as the turn starts, bank 0's write queue stays at the cap, and the turn ends
when the writes have drained bank 1 and the reads' column fires.

The queue occupancies at the flips are therefore (6, 0) for the waiting
direction every time: one bank at the cap, the other empty.

## 2. What the model did

The same flip rules, the same cap, the same in-order admission (the frontend
retries a refused request and holds the ones behind it), the same stream (the
captured AXI request stream of the proxy run through the model gives the same
62.6 / 115.7 as the generated one). The model's dump shows read turns of 254
columns (the cap, cause 2) lasting 1,700 slots and write turns of 30-60 slots
with 3-7 columns, and during the read hold BOTH write banks at 6 and both read
banks populated: the reads pay a PRE for a write row on both banks every beat,
neither read bank outruns the other, nothing drains, and the register stays
until the cap. The two attractors -- (6, 0) with 16-column turns, (6, 6) with
cap-length turns -- are both self-consistent under the same rules; which one a
run falls into is decided in the first turns after GO.

The model's dump at its first flips shows the decision. At the write turn's
start (slot 151, after the reads' first 16 columns) the bank-0 write beat the
hold had been refusing is admitted, bank 1's write beats follow, and the first
bank-1 write ACT request appears at slot 158 and fires at 160 -- when the write
direction's idle counter has already reached 8, so the select at 160 takes the
reads' column under `xdir_ok` and the register flips back at 161 with two
write columns done. In the RTL's probe the same write ACT fires with the idle
counter at 7 (cycle 129 after a flip at 122), one cycle inside the hold, and
the write turn runs its 16 columns. One slot, and the attractor.

## 3. Where the slot is: three admission registers, not one stage

The model carried one admission stage, `admit_lag` 3: a beat accepted at slot t
lands in its bank queue at t + 3 and holds its pool slot from t. That is the
pool path measured in ISSUE-004 and again on the interleaved cells today: a
column fire at t, the pool's valid count drops at t + 2 (two registers), the
beat waiting at the hold is accepted and lands at t + 3. The bank-cap path is
one slot shorter: the bank queue count the cap reads drops at t + 1, the held
beat lands at t + 2 (the mixed probe: the write column at 121, bank 0's held
beat in its queue at 123, bank 1's beats at 124, 125, 126 -- one per cycle,
each landing one cycle after its acceptance). The store's admission is: a gate
the host waits on (the pool valid, two registers behind the pop; the bank
count, one register behind), then the hold -> FIFO push, one cycle.

So the model's admission is now three knobs with the RTL's values:
`pool_gate_lag` 2 (a pop frees its pool slot to the host two slots later),
`cap_gate_lag` 1 (a pop shows in the count the cap reads one slot later),
`admit_lag` 1 (acceptance -> landing). The pool path is unchanged at 3; the cap
path is 2. Implementation: the controller logs every pop (slot, bank) and the
admission checks count the pops still hidden from each gate as occupied
(`pops_hidden`); `sku_admit3` is the model before (one three-slot stage on both
paths). The step-6 fill lag sits on top unchanged (a write beat is a head
record two slots after it lands; the bank-1 write beats landing at 124 were
the pick's requests at 127).

## 4. Record and method

- The proxy runs: `TEST_PAGE_POLICY=2 TEST_FAMILIES=mixed TEST_NUM_GEN=4
  TEST_TXN=512` with `PERF_DIR_FLIPS`, `PERF_DRAM_TRACE`, `PERF_PICK_PROBE`
  (`PERF_PICK_PROBE_FLIP=3`, 1200 cycles) and `PERF_AXI_TRACE`; the model's
  `GRANITE_SKU_DEBUG=0:28000` dump of the same cell at `--txn 512`.
- `granite_sku_controller.cpp` (`m_pool_gate_lag`, `m_cap_gate_lag`, the pop
  log and `pops_hidden`, `admit_lag` redefined as acceptance -> landing),
  `char_model.py` (`ModelConfig`, the `admit3` variant replacing `lag4`, the
  docstring), `test_char_model.py` (the shipped point's trio;
  `test_admission_gates_decide_the_mixed_close_page_turns`: the read and write
  windows within 5 percent of each other and the write window within 5 percent
  of the proxy's, against the single-stage model's read window at 0.55 of the
  write one). 39 / 39 and the vendor's 217 pass.
- Two things worth keeping. **A one-slot difference can pick an attractor**:
  the two modes here are not noise and not two mechanisms, they are one race
  decided once per run; measure the thing that decides it (here the idle
  counter at the first write ACT of a turn) on both sides, cycle for cycle.
  **Measure a lag per path, not per name**: the admission's "3" was the pool
  path's; the cap path shares two of its three registers and skips one.
- Previous steps: `model_mc021_wr_fill_lag_2026-11-19.md` (step 6),
  `board_mc021s4_granite_sku100_2026-11-19.md` (step 5).
