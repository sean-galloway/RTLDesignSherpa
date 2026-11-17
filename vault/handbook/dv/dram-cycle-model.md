---
title: A DRAM cycle model beside the measured controller
summary: Ramulator 2 with this repo's DDR2 class replays the board's characterization streams through an ideal FR-FCFS controller; the gap between its number and the measured one is the scheduler's share, the rest is the DRAM's. Where the model lives, how its clocks map, and what it cannot say.
---

# A DRAM cycle model beside the measured controller

Every bandwidth figure the memory-controller family had was measured: cocotb
characterization, LiteDRAM on the same harness, the board. A measurement says
how far the controller got; it cannot say how far the DRAM would have let an
ideal controller get on the same requests. **Ramulator 2 answers that
question**, and the recipe below keeps its answer comparable to the measured
cells rather than to a paper.

## Where it lives

- `vendor/ramulator2` -- the upstream clone (CMU-SAFARI, pinned), gitignored
  like every third-party source. `projects/components/mem-ctrl-ip/references/ramulator2/fetch.sh`
  clones, pins, overlays and builds it; `--test` runs the upstream suites.
- `references/ramulator2/overlay/` -- what upstream lacks: the **DDR2 and
  DDR2_BL8 device classes** (`python/ramulator/dram/ddr2.py`, every constraint
  annotated with its JESD79-2F clause), a **timestamped trace frontend**
  (`TimedLoadStoreTrace`, `<tick> <LD|ST> <addr>`, replays once and drains),
  their tests, and a three-file registration patch.
- `references/ramulator2/bin/char_model.py` -- builds the board host's
  request streams (the `pumice_char.py` families) as traces, runs them, and
  puts the model's cells beside the measured `char_results` CSVs.

## The rules that make the number comparable

1. **Same requests, same injection shape.** One 8-byte BL4 transaction per
   MC cycle is the board's 64-bit AXI beat rate; the frontend ticks at the MC
   clock (`clock_ratio=1`) and the memory system at CK (`clock_ratio=2`, the
   DFI 1:2 ratio). Ramulator's ratio is a relative FREQUENCY: a higher number
   ticks more often. The stock `LoadStoreTrace` replays cyclically and stops
   when its last line is *sent*, so a finite trace ends with requests still
   queued; the timed frontend exists because of that.
2. **Same bandwidth definition.** Bytes moved over the cycles from the first
   beat in to the last response out, times the MC clock, per direction -- the
   board timer's `w_last - w_first`. The frontend reports those two ticks per
   direction; do not use the controller's run-total throughput.
3. **Same device, the part's own limits.** The board runs a DDR2-800 part at
   CK 150 / 200 MHz, below every JEDEC bin, so the preset carries the part's
   ns limits (`DDR2_MT47H64M16_*`), not the bin table at that rate. The bin
   presets (`DDR2_400B` ... `DDR2_800E`) are for questions about the standard.
4. **One CK per constraint is the expected gap.** Ramulator is CK-granular;
   the RTL's counters are MC-cycle granular with a phase margin. A model cell
   a few percent above the RTL on a row-hit stream is that margin, not a bug.
5. **Check the two things the model does that the board cannot.** The
   controller coalesces a write to an address already in its write queue and
   forwards a read from it; the CSV carries both counts. Wrapped walks
   (`row_major` wraps inside one page) can trip them; a non-zero count is a
   note on the cell, and a large one disqualifies it.

## What it cannot say

- Nothing narrower than a transaction: the half-burst families
  (read-combiner stress) have no model.
- Nothing about the host path: the model's read latency is command accept to
  data return; the board's includes the AXI fabric and the UART harness.
- The `random` family's LFSR is a stand-in with the injector's shape
  (16-bit maximal, bursts inside a two-row-by-all-banks region); the per-burst
  order differs, the hit / miss statistics do not.

## What the first comparison said (granite sku100, 2026-11-11)

Two model columns beside the measured one tell the gap apart. `open32` is the
CK-granular ideal; `open32_mc2` is the same controller with every constraint
rounded up to 2 CK, the granularity of the RTL's MC-cycle timers.

- Row-hit streams: granite within 1 % of the ideal, and the ideal is 2.3 %
  under peak purely from refresh. Nothing left to schedule.
- `col_major` (every burst a miss in one bank) and `mixed`: the mc2 column
  reproduces granite to 2 MB/s. That gap is timer granularity, the DRAM's share
  as the RTL can count it, not a scheduling loss.
- `col_major_interleaved`, `row_thrash`, `random` (bank-parallel misses):
  granite 12-21 % under the ideal and mc2 explains none of it. The gap is ~1.1
  MC cycle per burst at every burst length -- the shape of one command slot
  per burst, which is what a one-DRAM-command-per-MC-cycle issue path costs
  when ACT and PRE share the slot with a column command that already fills
  every MC cycle at BL4. Filed as memory-controllers MC-013; confirmed the
  next day, below.

## The slot, measured (2026-11-12)

The model named the slot; the RTL sim confirmed it without building anything.
The row lane could not be tried on granite (its store forces the bank-pick
core, which has no lane), so the granite perf proxy's command trace was
repointed at the scheduler plane's `evt_*` strobes and made to report **slot
occupancy**, the fraction of MC cycles with a fire per 1024-cycle bin. On
`col_major_interleaved` and `row_thrash` the plane fires in 97 % of cycles and
the ACT recurs every 9 cycles exactly: eight columns plus one ACT per burst,
auto-precharged, through one command per cycle, 8/9 of peak less refresh =
the measured cell. Pumice, which has the lane on the same DFI command path,
gains +13 % reads with it and leaves the timer-bound `col_major` alone
(`char_results/sim_mc013_command_slot_dual_issue_2026-11-12.md`; the RTL item
is MC-014).

Two method points. **Measure the resource the model accuses before building
the fix**: a one-line occupancy statistic over the fire strobes settled in an
afternoon what a row lane on the pick core would have taken a week to show.
And **a probe that finds nothing is not a probe**: the trace had pointed at a
retired per-bank scheduler for weeks and logged "absent" every run; nobody
read the line because the run passed.

## The lane, built (2026-11-12, the same day)

The fix the two measurements pointed at took an afternoon once the slot was
named: a row-only second issue lane on the pick core (memory-controllers
MC-014, `mc_bank_pick` `DUAL_ISSUE`, the FR-FCFS core's lane re-made with the
pick core's own rules). Sim at the same point, lane off -> on:
`col_major_interleaved` reads 686 -> 773, `row_thrash` 687 -> 775, `random`
656 -> 722, against the model's 781 / 781 / 773; `col_major` unchanged
(`char_results/sim_mc014_granite_row_lane_2026-11-12.md`). The reads landed
within 1 percent of the ideal on the two pure families, which is the model's
column confirmed a third way.

What the lane did NOT move is the other method point: the writes stayed at
686. The model had said the write and read ideals were equal; the trace
shows the write stream paying one slot per AXI burst with or without the
lane, a bubble the slot cost had hidden. **One cell can hide another of the
same size.** Fixing the named one revealed the next (MC-015), and the
model's "both directions reach 781" is what says it is worth chasing.

The method point: **run the model twice, once ideal and once at the RTL's own
granularity**. The difference between the two columns is what the RTL cannot
recover without changing how it counts; the difference between the second
column and the measurement is what scheduling work can still buy.

## Four policies priced, one filed (2026-11-12, MC-013 items 2-5)

With the model in place a policy question costs 30 seconds of compute, so the
rest of MC-013 ran the same afternoon
(`char_results/sim_mc013_policies_2026-11-12.md`). What came out, and the
method points each one left:

- **Write-drain hysteresis** moves `mixed` by -20..+8 percent across its
  range, and the best point is the deepest drain -- the policy granite's
  direction register already implements. *Price the knob the RTL already has
  before adding one: the model's sweep said "keep what you have", which is a
  result, not a null.*
- **Refresh**: 1.67 of the 2.4 percent is tRFC and no scheduler moves it;
  bursting eight REFs recovers the other 0.6. *Decompose a cost into its floor
  and its recoverable part before chasing it* -- the DDR2 class makes the
  floor one line of arithmetic (nRFC / nREFI). Also: `scatter_interval` is a
  phase shift at one rank; a knob that staggers NODES does nothing with one
  node, so read the implementation's unit before sweeping it.
- **Queue shape** (`BankFIFO-RR`, a 90-line scheduler in the overlay): per-bank
  FIFOs tie the pooled queue on every single-direction family and lose 11
  percent on `mixed` -- filed as MC-016 with that number. The surprise was the
  control: **upstream's plain FR-FCFS is the WORST policy on `row_thrash` and
  `random`** (743 reads where row-hit-first or per-bank reach 782), because its
  arrival-order tie-break preempts an open row with a ready miss elsewhere.
  *The "ideal controller" has a policy too.* The 2026-11-11 compare used it as
  the ceiling on those two families and was 5 percent low; the ceiling is the
  best policy the model has (`open32_rowhit` there), and a column in a compare
  table should say which one it is.
- **The captured trace** (`perf_axi_trace.py` off the controller's own AXI port,
  `char_model.py run-trace`): the three single-direction rebuilds replay to the
  MB/s, so MC-012's stride-table streams stand; `mixed` does not, because the
  port accepts write bursts and read bursts on two channels in parallel and the
  rebuilt trace alternated beats. The model's mixed ideal is 363-370, not 337,
  and granite's `mixed` gap is 10 percent, not 2. *A rebuilt stimulus is a
  hypothesis about the interface; capture it once from the real port before
  resting a conclusion on it* -- the one family where the rebuild was wrong was
  the one with two channels in flight.

## The hidden write cell, found (2026-11-13, MC-015)

The lane left the writes at 686 and the task was filed as "one command slot
per AXI burst": seven WRs a cycle apart then a gap of two, per 8-beat burst.
A per-cycle probe on every valid/ready hop of the write path
(`PERF_W_HOPS` in the granite proxy) put the stall in the FIFO store in one
run -- `w_wr_have_free = 0`, the write pool full -- and the pool holds eight
entries. Eight slots at a nine-cycle turnaround is 8/9 of a command per
cycle, which is 686 of 781. The period was the pool, not the burst; the
burst is eight BL4 sub-commands by coincidence. Pool 16 in sim: 766-769
writes on the bank-parallel families, level with the reads, zero mismatches,
on granite AND pumice (same pool, same eight); `col_major` unchanged; `mixed`
reads -11 percent, the direction register holding writes longer, filed under
MC-016 (`char_results/sim_mc015_write_pool_2026-11-13.md`).

Three method points:

- **A period equal to a burst length is not a per-burst mechanism.** The
  write path has three things of size eight (the burst, the pool, the bank
  count). The task listed three per-burst candidates, all read statically
  and all cleared -- an hour that settled nothing a 12 000-cycle probe did
  not settle in three minutes WITH the gating term named. When a statistic
  names a count, enumerate everything in the design with that count before
  naming a mechanism.
- **Sample valid AND ready at every hop, not the handshake.** The handshake
  count is identical at every hop of one stream (it must be); ownership of
  the stall is in which side is low. "Valid without ready" per hop pointed
  down the chain to the store on the first run.
- **Little's law before microarchitecture.** Slots over turnaround is the
  throughput; a pipeline whose every stage is a deliberate register (the
  100 MHz work) is fixed by capacity, not by a shorter pipe. The write
  pool's turnaround was never measured because the pool was never
  suspected; the model's "both directions reach 781" (above) is what said
  the gap was worth a probe at all.

## The two-head store, modelled -- and the premise read first (2026-11-15, MC-016)

MC-016 asked for a model of granite's two-head store before any RTL
(`char_results/sim_mc016_two_head_model_2026-11-15.md`). The model step took
an afternoon and closed the task without RTL; what it left:

- **Read the consumer before modelling the producer.** The task's premise,
  "the pick can see one record past a conflicting head", came from the
  store's port list. `mc_bank_pick` reads the second record in one
  expression under one condition (the pop shadow); its hit is a stored
  same-row bit. One grep said the RTL is the model's strict FIFO already,
  and the model was then built to answer the next question (what a real
  peek would buy) instead of approximating a mechanism that does not exist.
- **A peek is measured in bursts, not entries.** The overlay's `BankFIFO-RR`
  got a `peek_depth`; depths 2, 4 and 8 are bit-identical to the strict FIFO
  on `mixed` at every pool depth, because one store entry is one beat and an
  AxLEN-8 burst is eight entries of one row. Size any lookahead on a
  beat-granular queue against AxLEN before sizing it against the pool.
- **Compare unions on a two-direction window.** MC-013 put granite's 330
  read cell beside the model's 370 and read a 10 percent gap; both
  directions' bytes over the longer window read 524 against 740, and the
  board CSV had carried that union in its notes column all along. The
  per-direction cells of a mixed window are each measured over their own
  window and are not the model's shared one.
- **Say which half of a model's gap transfers.** The pooled queue's gain
  over the strict FIFO is frontend stall on Ramulator's single in-order
  stream (conflicts equal, stall ticks five times higher); the RTL's AXI
  port has two channels. The half that transfers -- the conflicts -- is
  zero here, and granite's 20-24 percent under its own shape is the
  direction rule (MC-017).

## The direction register, measured and fixed (2026-11-15, MC-017)

MC-016 left granite's `mixed` window 20-24 percent under the model's own
shape with a read waiting 52 000 cycles. MC-017 counted the direction
register's flips, swept the cap the task named, and fixed the mechanism in
`mc_bank_pick` (`char_results/sim_mc017_direction_register_2026-11-15.md`).
What it left:

- **Count the flips before touching the rule.** A per-flip log with the
  cause and the batch length (`PERF_DIR_FLIPS`) said in one run that the
  cap handed the bus over every time and the handover failed every time
  (136 of 143 read turns ended in five cycles with zero columns). The cap
  sweep the task was filed for became a table that confirmed a non-lever.
- **Trigger a probe on an event count, not a cycle number.** The absolute
  cycle of a window moves between runs of the same test; the n-th direction
  flip does not. `PERF_PICK_PROBE_FLIP` replaced two wasted probe runs.
- **A fix that holds one path opens the next.** Gating the ungated hint
  moved the take-back to the drain branch; holding the drain moved it one
  cycle past the idle window. Each step was re-probed, not re-guessed; the
  lane-on residue was a one-cycle race between the register's decision and
  the fire that would have reset its idle counter.
- **Re-check the other build of the same block.** A fall-through gate that
  looked right with the row lane on cost the lane-off window 40 percent,
  because the lane-off design uses the main slot for what the lane does.
  Every pick-core change now runs `TEST_DUAL` both ways before it is read.
- **Register-only terms, and the block boundary is a timing rule.** Reading
  the select's gate inside the lane's register-only block was a Verilator
  block-level cycle (UNOPTFLAT) and would have been a cone the 100 MHz
  budget could not take; the lane block exports per-direction terms and the
  select combines them.
- **Fairness has a price on a synthetic window, and the model prices it.**
  The old register ran the writes alone and then the reads alone; a fair
  alternation pays the turnarounds and the writers' per-burst row switch on
  every turn (-9 percent union at pool 8 with the lane, +1 / +2 elsewhere,
  worst read wait 520 us -> 5 us). Carry the union AND the worst wait to the
  owner, not one cell.

## The SKU moved to the measured point (2026-11-16)

The owner closed the question MC-015 and MC-017 left open: THE FPGA SKU IS
THE CONFIGURATION, so the granite defaults became the point the board had
measured -- `GRANITE_SEAM_N` 16, `DUAL_ISSUE` 1 in `granite_core` /
`granite_top_geared`, the board harness and the TB top, `TEST_DUAL` /
`TEST_NUM_ENTRIES` defaulting to 1 / 16 in the proxy (sim_build tags
`_laneoff` and `_n<N>` for the controls), the board knob `GRANITE_DUAL_ISSUE`
now carrying a value (0 builds the lane out), and the host's runtime lane
enable following the controller (granite on, pumice off, `TEST_DUAL_ISSUE`
wins). What to carry forward:

- **The runtime enable belongs to the host, not the RDL reset.** The lane
  needs `SCHED_POLICY.dual_issue` and `DFI_PHASE.row_phase` set together, and
  the host derives its tRTP / tRCD margins from `row_phase`; a reset default
  the host did not know about would mis-derive them. The host already owns
  every timing CSR for the same reason (2026-09-08), so the lane's enable
  went the same way: `ControllerConfig.lane_on(drv)`.
- **A default flip needs the no-knob build, not the knob build.** The MC-017
  bitstream was built with `GRANITE_DUAL_ISSUE=1 GRANITE_NUM_ENTRIES=16` in the
  environment; the SKU commit is proved by a plain `GRANITE_SYS_100=1 make
  bitstream` reproducing its timing and cells, and by the sys75 build closing
  under the budget too, since the package default moves both profiles.
- **Model the SKU, not a policy.** MC-018 is filed for it: a `granite_sku100`
  Ramulator configuration tied to the 2026-11-16 cells, then one-term variants
  priced on it before any RTL task is filed.

## The SKU as a configuration (2026-11-17, MC-018)

The owner's 2026-11-16 ask closed the loop the policy configs had left open:
a Ramulator configuration that IS the granite FPGA SKU, not a policy beside
it. It is the overlay's `GraniteSKU` controller
(`references/ramulator2/overlay/src/ramulator/controller/impl/granite_sku_controller.cpp`)
on the `DDR2_GRANITE_SKU100` preset: one command slot per MC cycle with the
row lane on the odd CK, per-(direction, bank) FIFO heads in the 16-entry
pools with `BANK_CAP_MIXED`, the pick core's decode / select / rotor /
alternation, the MC-017 direction register, close-on-drain, drain-then-grant
refresh, the host's MC-cycle timings written in CK and the PHY-window tRTW
as a DDR2 parameter of its own (`nRTW`). `char_model.py --config
granite_sku100` runs it; `board-compare` puts it beside a board CSV set with
a tolerance per family; `sweep` prices one-term variants against it
(`char_results/model_mc018_sku_config_2026-11-17.md`). What it taught:

- **State the tolerance before the comparison, per family, and keep it.**
  Row-hit families 2 percent, the bank-parallel miss families 3, `col_major`
  and `random` 5, `mixed` 10 on the union. Every open-page cell of the SKU
  preset landed inside (row-hit +0.4 .. +1.2, `col_major` within 0.6,
  `random` +3 .. +4, `mixed` +9 on the union); the three presets that did not
  are each a named RTL effect with its own item (ISSUE-002 `bank_interleave`
  at a third of the model, ISSUE-003 `close_page` paying ~2.5 cycles per
  dependent hop, ISSUE-004 the `mixed` turn structure), not a number averaged
  into a wider band.
- **Derive each timing the way the RTL's counters sequence it, not the way
  JEDEC adds it.** `col_major` writes were +7 percent with the reads exact:
  the RTL counts WRA -> ACT as tWR 4 MC then tRP 2 (6), the model summed the
  CK terms (7 + 3 = 10 CK = 5 MC). One family off while its neighbours are on
  points at one term; the preset's comment names each forced value and a test
  pins every constraint to the host function.
- **Inherited conveniences are model terms.** The upstream controller
  coalesces a write to a buffered address and forwards a read from one;
  `mixed`'s wrapped page walks tripped both and gave the reads a third of
  their bandwidth for free. A model of a specific machine owns its admission.
- **Admission has a granularity.** `BANK_CAP_MIXED` applied per beat stranded
  six beats of a burst in the queue and the other bank's burst behind it, so
  one direction ran one bank at a time; the RTL takes the AW whole. The trace
  carries beats, so a beat contiguous with the last admitted one is the same
  burst and exempt. Read where the RTL applies a rule (the AW / AR) before
  applying it where the model happens to see requests.
- **A rule copied from the RTL can still give a different answer than the
  RTL.** The lane's rotor (past the held winner's pair, wrapping to the
  lowest) is the pick core's as written, and in the model it hands the
  shared bank's ACT after an auto-precharge to the holder every time, so the
  waiting direction never opens a row and the read turns run four times the
  cap; the RTL's flip log (MC-017) shows 255-column turns. The disagreement
  is the finding -- it names the probe (`PERF_PICK_PROBE_FLIP` at a cap flip,
  lane on) and the term the model is missing, and it is filed (ISSUE-004)
  rather than tuned away. Until it closes, `mixed` rows of the sweep carry it
  as their error bar.
- **Stream equivalence first.** The MC-013 captured `mixed` trace replays to
  the same cells as the rebuilt stream (union 595 against 592), so a `mixed`
  disagreement is the controller's, not the stimulus's.

- **Read a variant's gain against the model's own defect first.** The sweep's
  biggest movers were all on the `mixed` rows (+9 .. +35 percent for no batch
  cap, no idle hold, no row ownership, a refresh burst) -- every one of them a
  knob that changes the turn structure the model gets wrong (ISSUE-004). A
  variant that improves a cell the model does not reproduce is the model
  repairing itself; it is recorded, not filed. The two that were filed
  (MC-019: a PRE never needs to ride the lane, 0.0 on 29 patterns; MC-020:
  the single-bank RDA -> ACT -> RD chain, +5 .. +15 on `col_major`) move cells
  the model reproduces within 1 percent.
- **An ideal column is a decomposition, not a target.** At the SKU's timings
  the ideal beats the SKU only on `col_major` (+5 .. +15, the one-slot tax, which
  `slot1` isolates to the slot) and on `mixed` (+32, under the ISSUE-004 bar);
  on the 23 other patterns it is within 0.4 percent. The SKU's rules are the
  ideal's everywhere the lane reaches.

## The admission pipeline decides who gets the ACT (2026-11-17, ISSUE-004)

MC-018 left one shape wrong: the SKU model's `mixed` read turns ran four
times the batch cap (296 / 417 against the board's 272 / 272). The issue
blamed the lane's rotor handing a shared bank's ACT to the holding direction
after its auto-precharge, a rule copied from the RTL. The probe (the pick's
state with the store's occupancy and head records beside it, at a cap flip)
showed the rule was right and its candidate set was not: the RTL's pool holds
six beats of each direction, the holder's next burst on the bank is not there
when its auto-precharge fires, and the waiting direction's ACT rides
unopposed. Three admission terms reproduce it; `mixed` reads 286 / 286 with
255-column turns, every other SKU cell unchanged
(`char_results/model_issue004_admission_lag_2026-11-17.md`).

- **When a copied rule gives the wrong answer, check what it is looking at
  before changing it.** The rotor's order was the RTL's; the queue in front
  of it held two bursts where the RTL's held six beats. The term that fixed
  the model was in the store, not in the pick -- the probe that found it read
  both in the same cycle.
- **A pool's depth under mixed traffic is the per-bank cap, not the pool.**
  `BANK_CAP_MIXED` is checked at every push and the AR chops in order, so a
  burst's seventh beat waits for its first pop and the other bank's burst
  waits behind it. The 16-entry pool is six deep for both directions the whole
  window. The MC-018 model exempted a burst's remaining beats (its own
  guess at the AW / AR granularity) and held 13 per bank.
- **Admission is a pipeline with a latency, and the latency has a cliff.** A
  pushed beat is a head record three cycles later and a request one after;
  a slot freed at t carries a schedulable head at t + 5. Modelled as a 4-slot
  stage: at 0 or 2 slots the two banks' bursts interleave column by column
  and the holder's next ACT is always present (the old shape); at 4 they
  serialize as the RTL's and the waiting direction rides; at 6 the refill lags
  the pops and the turns stretch. Two is on the wrong side of the cliff.
- **The direction register reads the request, not the fire.** The decode's
  request needs the row hit and the bank's own timer; the RD <-> WR
  turnaround, tRRD / tFAW and tCCD gate the fire. A write column that tRTW
  blocks for twenty cycles still counts at the cap, flips the register and
  then holds the slot. A model whose request needs every timer cannot flip
  until the holder pauses. (Inert on `mixed` once the other two terms are in;
  it moves the ACT-bound presets, since a bank-ready ACT is now a lane
  candidate that fires the CK the rank timers open.)
- **Re-stamp a captured port stream per channel before splitting it.** A
  combined capture's ticks are the port's beat order with both directions
  interleaved; offered as two streams they paced each channel at half rate
  whenever one direction ran alone, and the capture's write pool emptied in
  every read turn. Re-stamped, the captured `mixed` stream and the rebuilt one
  agree to the second decimal -- the stream equivalence MC-018 claimed, exact.
- **Say which cells a model term moved and which it should not have.** The
  three terms left every single-direction SKU cell within 0.4 percent, as the
  mechanism predicts (the staged beat lands inside the burst ahead of it, the
  cap is off with one direction streaming), and moved the two presets already
  out (`bank_interleave`, `close_page`) +25 percent further from the board on
  their ACT-bound rows, which the two issues now carry: the model's hop cost
  is the tRRD bound, the board's is the pipeline.

## The JEDEC check that found a table error (2026-11-11)

Writing the class constraint by constraint against JESD79-2F showed the
repo's DDR2 ns table (`pumice_device.py::DDR2_MT47H64M16_NS`) carrying tRRD =
7.5 ns, the 1 KB-page column of Table 42; a x16 part with 1K columns is a
2 KB page and its tRRD is 10 ns. At the board clocks both round to 2 CK, so
nothing moved on silicon; at the DDR2-800 span config it is one MC cycle.
Filed as memory-controllers BUG-003, fixed 2026-11-16. The lesson is the
method: **derive each timing from the spec's table with its page-size /
speed-bin column named**, not from a part's quick-reference line; the model
class now carries the clause beside every constraint so the next reader can
check it in one look.

The fix exposed a second lesson: **a checker case that only arms on a wrong
table is a case passing on the bug.** JESD79-2F sets tFAW = 4 x tRRD + 5..7.5
ns at every page size, and the MC-cycle derivation rounds each UP (phase
margin, then the 2 CK floor), so four rounded tRRDs cover the rounded tFAW at
every legal point of this part -- the controller's tFAW check is unreachable
on a consistent table, and the pumice command-stream checker's tFAW case had
bound only because the table mixed a 1 KB-page tRRD with a 2 KB-page tFAW.
It now runs the rule on a synthetic set and asserts that neither named point
binds, so a table change that makes one bind is noticed. When a fix makes a
test fail its own precondition, read what the precondition was standing on
before picking "another config".

Related: [[measure-over-the-window]] (the window rule is the same one),
[[arbiter-compliance-model]].
