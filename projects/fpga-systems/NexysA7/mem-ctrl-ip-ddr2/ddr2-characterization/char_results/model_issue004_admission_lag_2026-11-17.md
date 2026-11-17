# The `mixed` turn structure: the rotor was right, the stream to it was wrong (memory-controllers ISSUE-004, 2026-11-17)

MC-018 closed with the granite SKU model inside tolerance on every open-page
cell but one shape wrong: `mixed` read 296 / 417 write / read against the
board's 272 / 272, the model's read turns running four times the batch cap.
The issue named the suspect -- the lane's rotor handing a shared bank's ACT to
the holding direction after its auto-precharge -- and the probe that would
settle it. This is that probe, on the granite proxy at the SKU point (100 MHz
MC / CK 200, lane on, pool 16, `TEST_TXN` 1024, `mixed` = four writers and four
readers from one GO, rows 8 apart in two shared banks), and the model terms it
produced. Model side: `references/ramulator2` (GraniteSKU controller, frontend,
`char_model.py`); the proxy probes are `PERF_PICK_PROBE` with the store's
occupancy and head records added (`test_granite_char_perf.py`).

Short form: the RTL's pick does hand the ACT to whichever pair the rotor
reaches first, exactly as the model copied it. The difference is who is
standing there. In the RTL the holder's next burst on the shared bank is NOT
in the store when its auto-precharge fires, so the waiting direction's ACT
rides unopposed; in the model it always was. Three admission terms the model
did not carry put it there, and with them the model reads 286 / 286 (union
573 against 543-545, +5 percent) with 255-column turns, as the RTL does.

## 1. The RTL's read turn, slot by slot

`PERF_PICK_PROBE_FLIP=4` (a cap flip into a read turn), 80 cycles, with the
decode's registered class per pair, the bank timers, the four head records
and the store's `r_rd_valid` / `r_wr_valid` counts and per-bank queue
counts. Pairs: p0 = bank 0 read, p1 = bank 0 write, p2 = bank 1 read, p3 =
bank 1 write. The turn is a 19-cycle period per 16 columns:

| cycle (rel.) | main slot | lane | store (rd pool, bank 0 / bank 1 queue) |
|---|---|---|---|
| 0 .. 7 | 8 read columns, bank 0 (burst A, the last with auto-precharge) | -- | 6 -> 5; bank 0 6 -> 0, bank 1 0 -> 5 (burst B's beats push one per pop) |
| 6 | column | **ACT bank 1 for B** (B1 became a head at cycle 4) | |
| 8 .. 14 | 7 read columns, bank 1 (B) | **ACT bank 0 for the WRITER** at cycle 10 | bank 0 queue EMPTY at 9 .. 11; C1 lands at 12 |
| 15 | **PRE bank 0** (the read's: C1 misses the writer's row; the owner's courtesy lifts) | | |
| 16 | the 8th column of B | | |
| 17 | **ACT bank 0** (the read's, by the PRE -> ACT hint) | | |
| 18 | idle (tRCD) | | |
| 19 = 0 | 8 read columns, bank 0 (C) | | |

Three main slots in nineteen are the other direction's row being opened and
closed again: the writer's ACT rides the lane because at cycle 10 bank 0's
read queue is empty -- the reads' next burst C is behind B7 and B8 in the AR
stream, and those wait for bank 1's queue to drop below `BANK_CAP_MIXED` (6).
The write head on bank 0 then shows a hit (its row is open) for three cycles
of every period, which is what the direction register's cap flip reads
(`r_batch_done && w_wr_col_any`): at batch 255 the flip lands inside the
period. The write turn is the mirror, 25 cycles per 16 columns (the read's
ACT cannot ride beside a column at the burst boundary and takes a main slot
after two idle ones), and it starts with a 12 .. 15-cycle hold of the first
write column on the PHY-window tRTW.

The store's view settles the rest:

- `r_rd_valid` sits at 6 (5 while a burst streams) and `r_wr_valid` at 6 for
  the whole window. The 16-entry pool never holds more than one direction's
  six: `BANK_CAP_MIXED` is checked at every push (`w_rd_cap_ok` /
  `w_wr_cap_ok` in `mc_bank_fifo_store`), the AR chops in order, so a burst's
  7th beat waits for its first pop and everything behind it waits with it.
- A push lands one cycle after the pop that freed its slot, the pushed beat is
  a head record three cycles later and a decode request one after that: a
  slot freed at cycle t carries a schedulable head at t + 5.
- The direction register's flips: 257 in the window, 251 at the cap, 4 drain,
  2 fire; every batch 255; read holds 313 cycles (301 .. 343), write holds 432
  (414 ..). The flip log is `PERF_DIR_FLIPS`.
- The decode's registered request for a column needs the row hit and the
  bank's own timer (`bank_rdwr_ready_la`); the RD <-> WR turnaround, tRRD /
  tFAW and tCCD are the fire stage's (`w_timer_ok`). A column the turnaround
  blocks still counts for the register, and when picked it holds its slot
  until the timer opens.

## 2. What the model did instead, and the terms

The MC-018 model applied the mixed cap once per AXI burst (the remaining
beats exempt), so a bank queue held up to 13 and the pool 16: both banks'
next bursts were always queued. An accepted beat was a head the same slot. At
the holder's auto-precharge its next burst's ACT and the waiting direction's
ACT asked for the bank in the same slot and the rotor -- the main winner's pair
plus one, wrapping to the lowest pair -- took the read pair (even) before the
write pair (odd) every time. The writer never opened a row during a read turn,
so `oth_col_any` was never true at the cap and the read turn ran until a write
column fired by other means (cause 0 flips, ~1 000 columns). The lane rule was
the RTL's; the queue it looked at was not.

Terms added to `granite_sku_controller.cpp` (each a knob, the SKU's value the
default, the MC-018 form a `sku_*` variant):

| term | the RTL | knob | variant |
|---|---|---|---|
| the mixed cap at every push | `w_rd_cap_ok` / `w_wr_cap_ok` per push, in-order chopping | `cap_per_beat` (default on) | `sku_capburst` |
| an accepted beat is a head admit_lag slots later | push -> bank FIFO -> head record -> request, 4 MC cycles | `admit_lag` 4 | `sku_lag0`, `sku_lag2`, `sku_lag6` |
| a request needs the bank's timers; rank-level terms hold the fire | stage-1 decode vs `w_timer_ok` / `w_hold_next` | `req_bank_timing` (default on) | `sku_reqfull` |
| each direction's stream paced by its own channel | the AXI write and read channels | frontend `split_directions` re-stamps ticks per direction | -- |

The staged beats hold their pool slot and count for the cap from the
acceptance (as the store's push does) and the pick sees them `admit_lag`
slots later. The fourth term is the frontend's: a captured port stream's
ticks are the port's accept order with both directions interleaved, so a
split replay paced each channel at half rate whenever one direction ran
alone (the capture's write pool emptied during every read turn). Re-stamped,
the captured `mixed` stream replays to the same cell as the rebuilt one to
the second decimal -- the two streams are identical, which is the stream
equivalence MC-018 claimed, now exact.

## 3. Results

`mixed` at the proxy's point (TXN 1024, 4 + 4 generators), the board and the
proxy beside the model before and after; the variants isolate the terms:

| | wr / rd MB/s | union | flips (cause) | turns rd / wr (slots) | rd_lat_max | wr_wait_max |
|---|---|---|---|---|---|---|
| board 2026-11-16 (`defaults` / `open_page`) | 272 / 272 | 543 / 545 | ~256 | | | |
| proxy, same point | 271.5 / 272.4 | 543.1 | 257 (251 cap) | 313 / 432 | 521 | |
| model MC-018 (`sku_lag0`, per-burst cap) | 315.0 / 508.8 | 630 | 67 (65 cap, 1 fire) | | 556 | 1046 |
| model `sku_lag2` | 311.5 / 499.3 | 623 | 69 | | 578 | 1035 |
| **model SKU (lag 4, cap per push, bank-timed request)** | **286.4 / 286.5** | **573** | **255 (255 cap)** | **319 (319-339) / 380 (380-403)** | 414 | 364 |
| model `sku_lag6` | 207.8 / 208.3 | 416 | 255 | | 678 | 475 |
| model `sku_capburst` (lag 4, cap per burst) | 279.6 / 295.2 | 559 | 227 | | 512 | 817 |
| model `sku_reqfull` (lag 4, full-timing request) | 286.6 / 286.7 | 573 | 255 | | 414 | 364 |

The lag has a cliff: at 2 slots the holder's next burst is still present at
the auto-precharge (both banks interleave column by column, the MC-018
shape); at 4 the bursts serialize as the RTL's do and the waiting
direction's ACT rides; at 6 the refill lags the pops and the turns stretch
(208 / 208). The per-push cap is what makes the pool six: with the cap per
burst the second bank's burst is queued early and a quarter of the turns end
on the drain branch. The bank-timed request is inert on this window once the
other two terms are in (the writer's column is open for three cycles a period
with either form) but it is the RTL's structure and it carries the hold
statistic (`sku_win_holds`).

The residual: the model's read turn is 319 slots against the RTL's 313 (+2
percent) and its write turn 380 against 432 (-12 percent); the union lands
+5.5 percent over the board (573 / 543), inside the family's 10 percent
tolerance and with the shape right. The write turn's 52 missing slots are in
the terms the model still does not carry on the write path (the write-data
fill and commit back-pressure, `w_wr_sink_ok`; the decode -> pick -> fire
stages); they are the `mixed` error bar now.

Every other cell, re-run (`model_ramulator2_ddr2_granite_sku100_issue004_2026-11-17.csv`,
compared in `compare_model_sku_vs_board_sku100def_issue004_2026-11-17.md`,
31 in / 26 out against MC-018's 30 / 27):

- the SKU's single-direction cells are unchanged within 0.4 percent
  (`incremental` / `row_major` 778 / 782, `col_major` 283 / 390 .. 542 / 624,
  `col_major_interleaved` 777 / 780, `row_thrash` 778 / 779, `random` 749 /
  767): the staged beat arrives well inside the burst ahead of it, and the
  cap is off with one direction streaming;
- the two presets already out (ISSUE-002 `bank_interleave`, ISSUE-003
  `close_page`) moved on their ACT-bound rows and away from the board:
  `bank_interleave` `col_major` 312 -> 389 (board 237), bl16 519 -> 777 (238),
  `random` 312 -> 389 (238); `close_page` `col_major_interleaved` 312 -> 389
  (235 / 213), `row_thrash` 312 -> 377 / 389 (208 / 197), `random` 281 / 293
  -> 303 / 315 (188 / 207). A bank-ready ACT that the rank timers still
  block is now a lane candidate and fires on the odd CK the moment tRRD /
  tFAW open, where before it had to be fully ready at the even slot: two
  slots per hop on a tRRD-bound chain instead of two and a half. The RTL's
  lane does the same (phase 1, `w2_timer_ok` at the fire), so the model's
  hop cost is the right lower bound and the board's 3.3 cycles per hop
  (ISSUE-002) and 2.5 (ISSUE-003) are RTL pipeline terms the model never
  had; the two issues carry the new numbers. The one-bank `close_page`
  chains (`incremental` 104 / 119, `row_major` 98 / 112) are unchanged.

## 4. The MC-018 sweep, re-read

The 23 MC-018 configurations plus the five admission variants, over the
`everything` suite (28 patterns, 784 cells): `model_ramulator2_ddr2_sku_sweep_issue004_2026-11-17.csv`,
the pattern x variant table in `model_sku_sweep_table_issue004_2026-11-17.md`.
Per variant, the delta against the SKU over the 21 single-direction patterns
and over the 7 two-direction ones (`mixed_*`, `rw30`, `rw70`; the union),
beside MC-018's numbers:

| variant | single-direction, now | two-direction, now | single (MC-018) | two-direction (MC-018) |
|---|---|---|---|---|
| `laneoff` / `lanepre` | -20.4 .. 0.0 (mean -6.3) | -8.8 .. +8.9 (-2.3) | -20.2 .. 0.0 (-6.0) | -7.2 .. +14.7 (-1.3) |
| `laneact` | 0.0 on all 21 | 0.0 on all 7 | 0.0 | 0.0 |
| `slot1` | -0.7 .. +12.9 (+1.4; `col_major` only) | -0.1 .. +25.6 (+11.1) | 0.0 .. +12.8 (+1.5) | +0.3 .. +29.1 (+8.9) |
| `ideal16` | 0.0 .. +17.5 (+2.2; `col_major` only) | +16.3 .. +40.6 (+27.2) | 0.0 .. +16.7 (+2.1) | -2.2 .. +35.1 (+19.4) |
| `pool8` | -5.7 .. +15.0 (+0.4) | -0.7 .. +0.7 (0.0) | -6.6 .. +5.6 (0.0) | -5.5 .. +18.4 (+2.6) |
| `pool24` / `pool32` / `peek16_pool32` | -0.1 .. +2.1 (+0.1) | 0.0 | -0.7 .. +2.2 (+0.1) | -7.0 .. +3.7 (-0.5) |
| `peek2`, `hold16`, `noalt`, `cap0/4/8`, `batch0/64/128`, `hold0`, `noown` | 0.0 on all 21 | see below | 0.0 | see below |
| `refburst8` | +0.4 .. +1.4 (+0.8) | -22.3 .. +6.9 (-1.7) | +0.4 .. +1.0 (+0.7) | +0.4 .. +33.6 (+9.8) |
| `jedec` (tRTW 5 CK) | +0.1 .. +14.9 (+1.3) | -3.5 .. +31.1 (+12.4) | -2.8 .. +4.7 (+0.5) | -0.7 .. +13.0 (+6.2) |
| `capburst` (MC-018's cap) | 0.0 | -5.6 .. +16.8 (+3.1) | -- | -- |
| `lag0` / `lag2` (MC-018's admission) | -0.2 .. +0.6 (0.0) | -9.6 .. +9.2 (-0.3) | -- | -- |
| `lag6` | 0.0 .. +1.1 (+0.1) | -35.2 .. -0.1 (-15.6) | -- | -- |
| `reqfull` | -0.1 .. 0.0 (0.0) | 0.0 .. +14.0 (+4.4) | -- | -- |

- **Every single-direction conclusion of MC-018 stands.** The lane is the
  one structural win and carries ACTs only (`lanepre` == `laneoff` to the
  cell, `laneact` == the SKU on all 28 patterns): MC-019 as filed. The
  one-slot rule still costs `col_major` alone, +13 / +17 at `slot1` /
  `ideal16`: MC-020 as filed. The pool is right at 16, the peek, the hold,
  the alternation, the caps and the batch terms do nothing on
  single-direction traffic, the refresh burst is worth under 1 percent.
  None of the three admission terms moves a single-direction cell by more
  than 1 percent (`lag6` +1.1 on one), as section 3 found.
- **The two-direction rows are now read against the right structure, and
  several signs flip.** With the turns at the cap and the pool six deep,
  `noown` (DIR_OWNS_ROWS off) is -25 percent on `mixed` bl8 where MC-018 had
  it +14 (the holder's courtesy PRE is what re-closes the other direction's
  row cheaply); `cap4` is -40 where it was 0 (a cap of four with 8-beat
  bursts stalls both directions' refills); `refburst8` is -22 on `mixed`
  bl16 where it was +34. `batch0` (+36) and `hold0` (+31) still read as
  gains on the two-direction rows: both let the holder run until the other
  direction's column is ready, i.e. they buy the sequential shape MC-017
  removed on purpose (a 520 us read wait); they stay recorded, not filed.
  `jedec` tRTW is +31 on `mixed` bl8 now (it was +13): the model's write
  turn starts with the 12-15 slot PHY-window hold the RTL also pays, so
  the PHY lever is worth more than MC-018 said, and it is still the host's
  / PHY's number, not a scheduler task. `ideal16` is +27 on the two-direction
  rows (+19 before) -- the decomposition widened on `mixed`, mostly the
  turnaround and the wasted row openings a direction-free scheduler does not
  pay.
- **Two model cells remain unverified against hardware.** `mixed` bl4 is
  still asymmetric (272 / 445 write / read): a 4-beat burst pops in four
  slots, the admission stage is four, so the holder's next burst lands at
  the auto-precharge exactly and the race returns; the board has no bl4
  `mixed` cell to say which is right. `rw30` / `rw70` (165 / 389 and 387 /
  166) follow the 30 / 70 burst split and have no board cell either.

Open after this: MC-019 (ACT-only lane), MC-020 (the `col_major` slot),
ISSUE-002 and ISSUE-003 with their moved rows; nothing new filed.

## Method

- **When a copied rule gives the wrong answer, check what it is looking at
  before changing it.** The rotor rule was the RTL's and gave a different
  answer because its candidate set was different: the model's pool held two
  bursts where the RTL's held six beats. The probe that settled it read the
  store's occupancy beside the pick, not the pick alone.
- **A pool's depth under mixed traffic is the per-bank cap, not the pool.**
  Checked at every push with in-order chopping, a cap of 6 on an 8-beat burst
  makes the whole direction wait on the capped bank's first pop; the 16-entry
  pool is six deep for both directions whenever both are present.
- **Admission is a pipeline with a latency, and the latency has a cliff.** A
  beat that becomes a head the slot it is accepted interleaves two banks'
  bursts; one that takes four slots serializes them. The two shapes give
  opposite answers to "who gets the shared bank's ACT", and the number in
  between (2) is on the wrong side.
- **The direction register reads the request, not the fire.** A column the
  turnaround blocks for twenty cycles still flips the register at the cap,
  and then holds the slot. A model that requires full readiness to request
  cannot flip until the holder pauses.
- **Re-stamp a captured port stream per channel before splitting it.** A
  combined file's ticks are the port's beat order; offered as two streams
  they pace each channel at half rate whenever one direction runs alone.
  The re-stamped capture and the rebuilt stream agree to the second decimal.

## Recipe

    cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests   # env_python sourced
    export TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024 TEST_LEVEL=FUNC
    # the pick, the decode's class, the bank timers, the head records and the store's occupancy at the 4th flip
    TEST_DUAL=1 TEST_NUM_ENTRIES=16 TEST_FAMILIES=mixed TEST_NUM_GEN=4 PERF_DIR_FLIPS=$OUT/flips.json \
        PERF_PICK_PROBE=$OUT/pick.json PERF_PICK_PROBE_FLIP=4 PERF_PICK_PROBE_CYCLES=80 \
        python3 -m pytest test_granite_char_perf.py::test_granite_char_perf -q
    # the read path's handshakes (AR accept, push, issue, return, R) for the same window
    PERF_LAT_PROBE=$OUT/lat.json ... python3 -m pytest ...
    # the model's slot trace and flips (CK window), the SKU and the one-term variants, the capture replay
    GRANITE_SKU_DEBUG=2496:3100 python3 .../char_model.py run --config granite_sku100 --suite all --only mixed_bl8 --txn 1024 --out x.csv
    python3 .../char_model.py run-trace --config sku_lag0 --name mixed_capture --both <capture>/mixed.trace --split --out y.csv --overwrite
    python3 .../char_model.py board-compare --model model_ramulator2_ddr2_granite_sku100{,_bi,_close}_issue004_2026-11-17.csv \
        --measured <char_results> --granite sku100def_2026-11-16 --out compare_model_sku_vs_board_sku100def_issue004_2026-11-17.md
