# The SKU as a Ramulator configuration: within 1 percent of the board on every open-page cell, three presets that are not, and a pattern x variant table (memory-controllers MC-018, 2026-11-17)

The owner's ask (2026-11-16): make a Ramulator configuration that matches the
design, then run patterns on it to find microarchitecture improvements. THE
FPGA SKU IS THE CONFIGURATION, so the model is the shipped granite sys100
point -- `GRANITE_SEAM_N` 16, `DUAL_ISSUE` 1, `BANK_CAP_MIXED` 6, the MC-017
direction register, the host's derived timings at 100 MHz MC / 200 MHz CK --
and not a policy. Reference cells: `char_granite_sku100def_{windows,every}_2026-11-16.csv`
(lane on, pool 16, host defaults). Model columns are write / read MB/s under
the board's bandwidth definition (bytes over first beat in to last response
out, at the MC clock); `mixed` adds the union (both directions' bytes over the
longer window).

## 1. What `granite_sku100` is

A new controller in the Ramulator overlay, `GraniteSKU`
(`references/ramulator2/overlay/src/ramulator/controller/impl/granite_sku_controller.cpp`),
on a new DDR2 timing preset, `DDR2_GRANITE_SKU100`, run by `char_model.py`
(`--config granite_sku100`; `granite_sku100_bi` / `granite_sku100_close` are
the board's `bank_interleave` / `close_page` presets on it; the `sku_*` configs
each change one term). Every term below names the RTL term it carries:

- **One command slot per MC cycle.** The controller ticks at CK; the main slot
  is every second tick (DFI 1:2, the column on phase 0) and the only command
  the odd tick may carry is the row lane's (row_phase 1).
- **The timing set is the host's, in CK.** `pumice_device.ddr2_timings_mc_cycles(100e6, cl=3, row_phase=1)`
  gives tRCD 2, tRP 2, tRAS 5, tRC 7, tWR 4, tRTP 1, tCCD 1, tWTR 4, tRRD 2,
  tFAW 5, tRFC 14, tRTW 20, tREFI 780 MC cycles. The preset carries 2 x the MC
  count where that exceeds the JEDEC CK count rounded to the slot (tRC 14,
  tWTR 8 as WL + BL/2 + 4, tWR 8 as WL + BL/2 + 4, tRRD 4, tRFC 28, tRTW 40)
  and the JEDEC CK count elsewhere, where the even slot already rounds it to
  the RTL's count and the odd-slot lane command keeps the JEDEC distance. RD ->
  WR became its own DDR2 parameter (`nRTW`, JEDEC's RL + BL/2 + 2 - WL by
  default) because the board's tRTW is the PHY's read-DQ window, 20 MC cycles
  against JEDEC's 2.5. A test pins each constraint to the host function.
- **The store.** One FIFO per (direction, bank) in a 16-entry pool per
  direction (`BANK_FIFO_DEPTH` 0); `BANK_CAP_MIXED` 6 applied as the RTL
  applies it, once per AXI burst at the AW / AR, so a burst's remaining beats
  enter as the pool has room; one entry = one BL4 column = one AXI beat. No
  write coalescing and no read forwarding (the controller it inherits from
  does both; the board does neither).
- **The pick.** DECODE per head (hit -> column; open miss -> PRE, withheld
  while the other direction's head hits the open row unless this direction
  holds the bus with its batch not done, `DIR_OWNS_ROWS`; closed -> ACT,
  blocked under a refresh demand); the rotor over pairs 2 x bank + dir from the
  last winner; the row / column alternation; the direction register in its
  MC-017 form (follows a column of the other direction, flips on drained or
  on the cap with a ready column waiting, holds through `DIR_HOLD_IDLE` 8 and
  `DIR_BATCH_MAX` 255; row preference turns to the waiting direction at the
  cap); the row lane (an ACT or PRE to a bank with no pending column, not the
  column's bank, ACT before PRE, fired on the odd tick beside a main-slot
  column only); close-on-drain auto-precharge off the store's
  behind-same-row bit; AllBank refresh at nREFI with the drain-then-grant
  shape (PREab, where the RTL drains per-bank PREs).
- **The front end.** The timed trace frontend gained `split_directions`: the
  writers' and readers' streams are offered independently, each stalling on
  its own, as the AXI port's two channels do; the single-direction families
  are one stream at one beat per MC cycle as before.

Not carried, and therefore the instrument's error bars: the two-stage
decode -> fire pipeline with its lookahead and next-op hint (a dependent hop
lands on the timer in the model, one or two cycles later in the RTL when the
hint cannot pre-arm it: ISSUE-003); the pop shadow and the two-cycle stale
mask; the write-data fill and the sink / return-ring back-pressure; the age
overlay (inert on the SKU, `HAS_AGE` 0); the hybrid page predictor of the
board's `defaults` (modelled as `open_page`; the two differ by under 1
percent on every 2026-11-16 cell); per-bank refresh PREs; the AXI combiner;
the host-path latency. The `random` family's LFSR order differs from the
injector's (the hit / miss statistics do not) -- and the proxy's own
captured streams at the SKU point (TXN 1024) put a number on what the
pipeline costs at a 50 percent row-switch rate: on the same accepted
requests the model reads `col_major_interleaved` 780 / 781 against the
proxy's 766 / 768 (+1.7 %), `row_thrash` 778 / 779 against 769 / 769
(+1.2 %) and `random` 750 / 768 against 718 / 716 (+4.4 / +7.1 %). The
per-hop cost ISSUE-003 names at full strength on `close_page` is 5-7
percent at `random`'s hop rate and under 2 at `row_thrash`'s.

## 2. Model beside board (`compare_model_sku_vs_board_sku100def_2026-11-17.md`)

Tolerances, stated before the comparison and kept: row-hit families 2
percent, `col_major_interleaved` / `row_thrash` 3, `col_major` / `random` 5,
`mixed` 10 on the union; the `close_page` preset 15, `bank_interleave` 10.

| preset | family | board wr / rd | model wr / rd | delta | verdict |
|---|---|---|---|---|---|
| defaults, open_page | incremental, row_major (bl4 / 8 / 16) | 775 / 776-778 | 778 / 782 | +0.4 .. +0.7 % | IN, all 12 cells |
| defaults, open_page | col_major bl4 / 8 / 16 | 283 / 389, 416 / 520, 541 / 623 | 283 / 390, 418 / 520, 542 / 624 | -0.1 .. +0.6 % | IN |
| defaults, open_page | col_major_interleaved bl4 / 8 / 16 | 765-772 / 763-774 | 776-778 / 777-780 | +0.8 .. +1.8 % | IN |
| defaults, open_page | row_thrash | 770 / 770 | 778 / 779 | +1.0 / +1.2 % | IN |
| defaults, open_page | random | 718-726 / 740-746 | 747 / 767 | +3.0 .. +4.0 % | IN (the LFSR order is the model's) |
| defaults, open_page | mixed (union) | 272 / 272 (543-545) | 296 / 417 (592) | +8.6 .. +8.9 % | IN on the union, the SHAPE is wrong: ISSUE-004 |
| bank_interleave | every family | 232-238 / 232-239 (col_major 195-238) | 777-781 (col_major 312-519) | +30 .. +300 % | OUT, all 12: ISSUE-002 |
| close_page | one-bank families | 78-82 / 87-92 | 98-104 / 112-119 | +19 .. +29 % | OUT: ISSUE-003 |
| close_page | bank-parallel families | 180-235 / 197-240 | 281-312 | +30 .. +60 % | OUT: ISSUE-003 |
| close_page | mixed (union) | 73 / 152 (145) | 79 / 79 (158) | +8.8 % | IN |

30 of 57 cells in tolerance: every open-page cell of the SKU preset, which is
the configuration the task is about. The 27 out are two board presets the
model does not reproduce, and each is a named RTL effect with its own item:

- **`bank_interleave` (ISSUE-002).** The model sustains 778 on a stream of
  rotating-bank row hits; the board does 233-258, ~3.4 MC cycles per beat,
  read latency 234 against 58. The DRAM and the scheduling rules the model
  carries are not the cost. An RTL-side serialization under that map,
  unprobed.
- **`close_page` (ISSUE-003).** 8 B per 7 cycles (tRC) in the model, per
  ~9.5 on the board: the pipeline's per-hop cost, invisible on open-page
  streams where hops are one per burst, is 2.5 cycles per beat when every
  column is a hop.
- **`mixed` (ISSUE-004).** The union is inside the tolerance but the model's
  read turns run ~1 000 columns where the RTL's run the 255 cap: after the
  holder's auto-precharge both directions' heads ask for the shared bank's
  ACT in the same slot, and the lane's rotor (past the other bank's column
  winner, wrapping to the lowest pair = the bank-0 READ pair) hands it to the
  reader every time. Lane off, the model alternates fairly (297 / 297). The
  RTL term that gives the ACT to the waiting direction is the question. The
  stream is not it: the proxy's accepted `mixed` stream captured at the SKU
  point (lane on, pool 16, TXN 1024, `PERF_AXI_TRACE`) replays to 293 / 396,
  union 586, and the MC-013 capture to 298 / 423, union 595 -- the rebuilt
  stream's 296 / 417, union 592 -- while the proxy itself measured 271.5 /
  272.4, union 543.1, worst read wait 521 on that run, the board's cells to
  the MB/s.

Four model terms were wrong on the first run and are worth recording, each
found by one family off and the others on:

- **The RTL rounds twice where the model adds once.** `col_major` writes were
  +7 percent with the reads exact: the model summed WRA -> ACT as 7 + 3 CK =
  5 MC cycles, the RTL counts tWR 4 then tRP 2 = 6. Forcing nWR to the 8-CK
  compound makes the sum 11 CK -> 6. A derived timing has to round the way the
  RTL's counters sequence it, not the way JEDEC adds it.
- **Inherited conveniences are model terms.** The base controller coalesces
  a write to a buffered address and forwards a read from one; `mixed`'s
  wrapped page walks tripped both (reads 509 with the forwards). The SKU's
  admission is its own.
- **The cap is per burst.** Applying `BANK_CAP_MIXED` per beat stranded six
  beats of one burst in the queue and the other bank's burst behind it, so the
  write side ran one bank at a time; the RTL takes the AW whole.
- **A lane ride is a race on a shared bank.** Which direction's ACT the lane
  carries after an auto-precharge decides the turn structure; the model's
  rotor rule is the RTL's as written and gives a different answer from the
  RTL's measurement (ISSUE-004).

## 3. Patterns x variants

644 cells: 22 variants and the ideal against the SKU on the 15 `every` /
`windows` scenarios and the 14 MC-018 patterns (`model_ramulator2_ddr2_sku_sweep_2026-11-17.csv`;
the full table with every cell and its worst read wait is
`model_sku_sweep_table_2026-11-17.md`). Headline per cell = the larger
direction, or the union on the two-direction rows; delta against the SKU
column. Rows whose headline moves by less than 1 percent on every variant are
folded.

| pattern | SKU | ideal16 | pool8 | pool24 / 32 | laneoff = lanepre | laneact | slot1 | jedec | refburst8 | batch0 | hold0 | noown | cap0 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| incremental, row_major, locality h10-90, col_ilv_s2 (11 rows) | 779-782 | +0.1 | 0 | 0 | 0 (row-hit) / -6.7 .. -11.6 (locality, s2) | 0 | 0 | 0 | +0.5 .. +0.7 | 0 | 0 | 0 | 0 |
| col_major bl4 / 8 / 16 | 390 / 520 / 624 | +14.6 / +9.5 / +5.3 | 0 | 0 | 0 | 0 | +14.4 / +9.5 / +5.3 | +0.7 / +0.3 / +0.5 | +0.8 | 0 | 0 | 0 | 0 |
| col_major_interleaved bl4 / 8 / 16 | 777 / 780 / 780 | +0.4 / 0 / +0.2 | +0.4 / 0 / +0.1 | 0 | -20.2 / -11.6 / -6.0 | 0 | +0.4 / 0 / 0 | +0.5 / +0.2 / +0.3 | +1.0 / +0.7 / +0.7 | 0 | 0 | 0 | 0 |
| row_thrash | 779 | 0 | 0 | 0 | -11.6 | 0 | 0 | +0.3 | +0.7 | 0 | 0 | 0 | 0 |
| random | 767 | -0.2 | -4.5 | +1.0 / +1.3 | -10.5 | 0 | +0.7 | +0.2 | +0.7 | 0 | 0 | 0 | 0 |
| col_ilv_s4 (2 banks in play) | 733 | +6.3 | 0 | -1.2 | -6.0 | 0 | +4.1 | -10.1 | -4.6 | 0 | 0 | 0 | 0 |
| rw70 / rw30 (one stream, 70 / 30 percent writes) | 656 / 660 | -1.8 / -2.2 | -5.5 / -5.3 | +2.7 / +2.4, +3.7 / +3.0 | -6.9 / -6.6 | 0 | +0.3 | +13.0 / +12.8 | +0.5 / +0.4 | 0 | -0.7 / -0.1 | 0 | +0.1 |
| mixed bl8 (union) | 592 | +31.7 | +7.3 | 0 | +0.3 | 0 | +11.0 | +5.7 | +15.1 | +8.6 | +12.5 | +13.6 | +5.3 |
| mixed bl8 at 2 / 8 threads | 455 / 577 | +31.0 / +35.1 | 0 / +18.4 | 0 / -2.8, 0 / -3.5 | 0 / +14.7 | 0 | +7.7 / +29.1 | +5.8 / +7.1 | +0.5 / +33.6 | +1.9 / +34.9 | 0 / +33.5 | 0 / +23.7 | 0 / +6.2 |
| mixed bl4 / bl16 (union) | 530 / 693 | +29.5 / +12.5 | +1.7 / +1.6 | 0 / -7.0, 0 / -6.3 | -7.2 / -3.5 | 0 | +10.7 / +3.6 | -0.7 / -0.1 | +8.6 / +9.5 | +4.0 / +7.3 | 0 / +6.2 | +2.5 / +6.8 | -4.0 / 0 |

Also: `batch64` / `batch128` move only the mixed rows (bl8 +5.7 / +0.5, t8
+30 / +23, bl4 +5.2 / +0.9, bl16 +5.4 / +4.2) and cut the worst read wait
from 566 to 174 / 318 cycles; `hold16`, `noalt`, `peek2`, `cap4` / `cap8` are
the SKU to the MB/s on every single-direction row (`noalt` +5.6 on mixed bl8,
`cap4` / `cap8` within +-6 on the mixed rows); `peek16_pool32` is `pool32`
everywhere. Worst read wait: the SKU's is 36-84 MC cycles on every
single-direction row and 390-686 on the mixed rows; `pool24` / `pool32`
raise it 1.3 / 1.6 x, `refburst8` 2.5-3.8 x (150-176), `pool8` lowers it
(34-50).

What the table says, by column:

- **The lane is the SKU's one structural win, and it is an ACT lane.** Lane
  off costs 6-20 percent on every bank-parallel miss family, 7-11 on the row
  locality sweep and the one-stream mixes, 10 on `random`; `lanepre` (PRE
  only) is lane-off to the MB/s on all 29 rows and `laneact` (ACT only) is
  the SKU to the MB/s on all 29. A PRE never needs to ride: the auto-precharge
  closes the rows this traffic closes, and a demand PRE in the main slot
  costs nothing the model can see.
- **The one-slot tax is `col_major`'s alone.** A command slot every CK
  (`slot1`, the lane then moot) and the ideal at the SKU's timings agree:
  +14.6 / +9.5 / +5.3 on `col_major` bl4 / 8 / 16, +4 .. +6 on the two-bank
  interleave, nothing on the bank-parallel families (the lane already covers
  them) and nothing on the row hits. It is the RDA -> ACT -> RD chain of ONE
  bank landing on the odd CK, which the lane cannot carry (it fires beside a
  column, never to the column's bank, never into an idle slot: the MC-014
  cuts that closed 100 MHz).
- **The pool is right at 16.** 24 / 32 buy +1 on `random` and +2.4 .. +3.7 on
  the one-stream mixes, cost 6-7 on `mixed` bl16, and raise the worst read
  wait 1.3-1.6 x; 8 costs 4.5 on `random` and 5.5 on the mixes (MC-015's
  write pool, re-seen).
- **The PHY read window is the biggest timing term the SKU pays on
  alternating traffic.** The JEDEC CK set (`jedec`: tRTW 5 CK instead of 40)
  is +13 percent on the one-stream 70 / 30 and 30 / 70 mixes and +5.7 .. +7
  on the mixed windows, nothing elsewhere; the host's tRTW is the measured
  read-DQ occupancy plus an empirical guard of 6 (pumice BUG-014 history),
  so the lever is the PHY's, not the scheduler's. (`jedec` is -10 on
  `col_ilv_s4`: tRRD 2 CK lets the two banks' ACTs bunch and the lane then
  collides with them.)
- **Refresh bursting is a latency trade.** `refburst8` is +0.5 .. +1.0 on
  every single-direction row (the MC-013 0.6 percent) and raises the worst
  read wait 2.5-3.8 x. Recorded, not proposed.
- **`BANK_CAP_MIXED`, the hold, the batch cap, the alternation and a two-entry
  peek do nothing on single-direction traffic**, as they should; their
  mixed-row deltas (`cap0` +5, `hold0` +12, `noown` +14, `batch0` +9,
  `refburst8` +15 on `mixed` bl8, up to +35 at 8 threads) all change the
  turn structure the model gets wrong (ISSUE-004: its read turns run four
  times the cap), so they are the model repairing its own defect, not
  improvements to the RTL. They are recorded here and re-read when ISSUE-004
  closes; none is filed.

## 4. The list

Filed, each with its model number:

- **MC-019** -- the row lane carries ACT only. The model prices a PRE on the
  lane at 0.0 on all 29 patterns (`lanepre` = lane off, `laneact` = the SKU to
  the MB/s); dropping the PRE class from the lane (`w2_pre_set`, the PRE
  timer and class checks, the PRE payload) is logic out of the cone that
  bound 100 MHz, at no measured cost. A sim A/B on `TEST_DUAL` both ways and
  the no-knob sys100 build are its gate.
- **MC-020** -- a row command for the idle main slot or the column's own
  bank (the chain `col_major` pays): +14.6 / +9.5 / +5.3 on `col_major` bl4 /
  8 / 16 and +4 .. +6 on the two-bank interleave in the model, nothing
  elsewhere. MC-014 removed exactly this (the FR-FCFS core's lane fires
  alone) because the lane then entered the plane's command-valid cone at
  100 MHz; the task is to find a form that does not (a registered idle-slot
  row fire a cycle late, or the main select itself taking the row when its
  own bank's column is timer-blocked), gated by the 0.2 ns budget.

Recorded, not filed: pool 24 / 32 (+1 .. +4 on three rows, -6 .. -7 on
`mixed` bl16, worst wait 1.3-1.6 x); pool 8 (-4.5 .. -5.5); refresh burst 8
(+0.5 .. +1.0, worst wait 2.5-3.8 x); a two-entry peek (0.0 everywhere, as
MC-016 said); no alternation (0.0 single-direction); `BANK_CAP_MIXED` 0 / 4 /
8, `DIR_HOLD_IDLE` 0 / 16, `DIR_OWNS_ROWS` off, `DIR_BATCH_MAX` 0 / 64 / 128
(0.0 single-direction; their mixed deltas are pending ISSUE-004); the JEDEC
tRTW (+13 on alternating traffic -- a PHY / host number for the owner, not a
scheduler task). Open: ISSUE-002 (`bank_interleave` at a third of the model),
ISSUE-003 (`close_page`'s per-hop cost), ISSUE-004 (the model's `mixed` turn
structure).

## Recipe

    # build (the overlay's controller + preset + frontend mode, then codegen's Python wrappers)
    projects/components/mem-ctrl-ip/references/ramulator2/fetch.sh --test        # 217 passed
    cd projects/components/mem-ctrl-ip/references/ramulator2 && python3 -m pytest tests -q   # 35 passed
    M=projects/components/mem-ctrl-ip/references/ramulator2/bin/char_model.py
    R=projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2-characterization/char_results
    for c in granite_sku100 granite_sku100_bi granite_sku100_close sku_ideal16; do
      python3 $M run --config $c --suite all --out $R/model_ramulator2_ddr2_${c}_2026-11-17.csv; done
    python3 $M board-compare --model $R/model_ramulator2_ddr2_granite_sku100{,_bi,_close}_2026-11-17.csv \
        --measured $R --granite sku100def_2026-11-16 --out $R/compare_model_sku_vs_board_sku100def_2026-11-17.md
    python3 $M sweep --configs granite_sku100 sku_ideal16 sku_pool8 ... sku_jedec --suite everything \
        --out $R/model_ramulator2_ddr2_sku_sweep_2026-11-17.csv --table $R/model_sku_sweep_table_2026-11-17.md
