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
- **A 0.0 on a path the model never exercises is not a price** (MC-019,
  2026-11-20). The lane-PRE variant measured 0.0 because the model's SKU
  issues no demand PRE at all -- `lane_pre` 0 on every cell -- while the RTL's
  `defaults` and `open_page` presets issue ~700 per `col_ilv` run (rows the
  page policy leaves open), 424 of them on the lane; removing the class cost
  that read side 1.3 percent on the proxy. Before a variant that REMOVES
  something is filed as a task, count the command it removes on the proxy
  (`PERF_CMD_TRACE`): a model that reproduces a cell's MB/s can still be
  issuing a different command stream to get there
  (`char_results/rtl_mc019_lane_act_only_2026-11-20.md`, ISSUE-006).
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

## A knob is not a term, and a preset is what the host programs (2026-11-17, the knob grid)

After ISSUE-004 the two board presets already out of tolerance moved further
out, and the owner asked whether everything was getting worse. The right
answer needed a grid, not a defence: every setting of the three new admission
terms (28 combinations) on every preset configuration (4) over the
board-measured cells (15), scored against the board per preset and combined
(`char_results/model_knob_grid_2026-11-17.md`). What it said, and what it
taught:

- **Score the whole grid before choosing.** On the SKU all 28 settings give
  the identical 14 single-direction cells; only `mixed` moves, and the setting
  that reads best (`lag3`, +1.4 percent) sits on the admission cliff -- the
  same lag with the other request form is -19.6. A setting that wins one cell
  and loses its neighbour on the same axis is a cliff, not a fit. The default
  one step past the cliff, on the RTL's side, stays.
- **A knob that must flip per preset is a missing term, not a model.** On
  the close-page presets `req_bank_timing` off read closer (312 against 389
  on the board's 235) by adding half a cycle of waiting per hop. The RTL has
  one decode; a model that needs a different decode per preset is standing in
  for something it does not carry. The proxy, run at the board's exact
  preset with the DRAM trace and the pick probe, named it: a dependent
  command the next-op hint does not pre-arm fires two MC cycles after its
  timer opens (the registered request plus the winner register), the
  hinted hop lands at the timer. One number, measured twice (one bank: 10 / 9
  against 7.7 / 6.7; eight banks: 3.4 per beat against 2.0). That became
  MC-021, and ISSUE-002 / ISSUE-003 closed into it.
- **A preset is what the host programs, not what its name says.** The
  board's `bank_interleave` is `scheme=SCHEME_BANK_INTERLEAVE,
  page_policy=PAGE_POLICY_CLOSE` in `pumice_char.py`; the model's `_bi`
  encoded the map and left the page open, and ISSUE-002's factor of three
  was that line. Read the ControllerConfig fields before encoding a preset,
  and guard the encoding with a test that imports the host's table
  (`test_board_presets_are_what_the_host_programs`).
- **When the model and the board disagree, run the proxy at the board's
  preset first.** It reproduced all three presets to within a percent
  (235 / 230 against 234 / 233; 82 / 92 against 82 / 92) before any model
  change, which turned "the model moved away from the board" into "the model
  lacks a term the RTL has", with the term's size.
- **One perf dump per run.** The proxy writes `logs/perf_dump_<test>.json`
  and the next run overwrites it; a serial script that copies it after each
  run copied the second run's numbers under the first run's name, caught
  only because the dump carries `page_policy`. Set `PERF_DUMP=<own path>` per
  run.

## A lag term stood for a pipeline; carry the pipeline (2026-11-17, MC-021)

The knob grid measured a two-cycle hop on the close-page presets and MC-021
asked for a `hop_lag` term. The term reproduced the one probe window it was
read from (an eight-slot period per two beats) and missed the board by 17
percent on the eight-bank chain, because the RTL's period is six, seven or
eight slots, decided slot by slot by registers the model did not have. The
model now carries `mc_bank_pick`'s stages (`model_mc021_pick_pipeline_2026-11-17.md`).
What it cost to learn:

- **A measured latency is not a term when it comes from a pipeline.** The
  same "+2" was a request register plus a winner register, and the two
  patterns the probe recorded (ACT -> COL 2 in 60 percent, 4 in 40) were the
  pipeline's race over which pair sat in the winner register at the fire. A
  lag reproduces an average; registers reproduce the distribution. When the
  RTL is a pipeline, model the pipeline and let the latency fall out.
- **Line the model's slot trace against the RTL's per-cycle decisions.** The
  pick probe (`PERF_PICK_PROBE`) carries the request register, the stale
  mask, the select's source, the winner's fate, the hint and the lane per
  cycle; `GRANITE_SKU_DEBUG` prints the same from the model. Find the same
  cadence in both, walk forward, and the first slot where the select's
  branch differs names the rule -- here the stale mask engaging on a pair
  with nothing filled behind it, which turned "two empty slots after a
  column pair" into zero, one or two.
- **A rule that must differ per preset is keyed on state you are not
  carrying.** Arming the ACT after an auto-precharge fixed the SKU's
  `col_major` cells and broke `close_page` by 28 percent; not arming it did
  the reverse. The RTL's decode arms it for a head that misses the closed row
  and not for one that hits it: the key is the next head's row against the
  closed row, and once the model carried that, both presets held.
- **Do not count a stage twice.** ISSUE-004 measured four cycles from a push
  to the request; when the request register became explicit, `admit_lag`
  had to drop to three or the SKU's mixed cell paid the cycle again (-8.2
  against +1.7 percent).
- **Name the residual's mechanism before tuning it.** `bank_interleave` sits
  at -15 percent; two knobs land it (`pick_la` 0, `ap_stale`) and each breaks
  or changes another preset. The mechanism -- per-bank depth deciding where
  the stale mask engages, fed by the held lane pair's starvation and the
  write fill -- is written down with the probe evidence and the pool sweep
  that brackets it (pool 8: 260, 10: 215, 12: 208, 16: 199-202, board 234), and the task
  stays open on exactly that.

## A split-phase command is timed at the counter's clock, not the wire's (2026-11-19, MC-021 step 3)

After BUG-004 the model sat 14 percent UNDER the board on `bank_interleave
col_major_bl8` (333 against 387) while every other close-page cell was over,
and symmetric on bl4 where the board reads a third faster than it writes. The
item filed on it said "probe the read path after a read AP and the write
fill". The proxy said neither: it reproduces the board on every cell, and the
asymmetry is the write-recovery hop (t_wr + t_rp = 6 cycles) over the four
banks a bl4 burst touches under `bank_lsb` 2. The model's error was its own
clock. The DUAL_ISSUE lane fires its row command on the odd DFI tick, and the
model checked and stamped that command at the odd tick, in CK; the RTL's bank
and rank timers are MC-cycle counters that start at the fire's CYCLE whatever
its phase. A lane ACT in cycle n and a main ACT in cycle n + 2 are t_rrd = 2
apart to the RTL (3 CK on the wire, inside the host's phase margin); to the
model they were 5 CK, and under a close-page interleave two ACTs in three ride
the lane, so every third ACT paid a cycle: 2.4 slots per beat against 2.0.
Timing the lane at its slot (check at the slot tick, stamp the DRAM with it)
put the eight-bank cells on the board and the compare at 55 / 2 from 53 / 4,
with the SKU's cells moved 0.6 percent at most.

Three lessons. **When a model's command can fire between the RTL's clock
edges, time it at the edge the RTL's counters see**, not where it lands on
the wire -- the counters are the contract, the wire is the host's margin to
argue. **A fix that uncovers a feature uncovers that feature's model**: the
lane never fired on a close-page chain before BUG-004 (0 of 65,810 ACTs), so
its clock had never been tested where it binds; re-read every term a fix
makes live. And **the item's own hypothesis is the first thing to refute**:
"read path after a read AP" and "write fill" were both named in the task
file, both plausible, and the proxy disposed of both in one run before any
term was written. The residual that remains (two bl4 read sides at +11) is
a fixed point of the same pick rules, recorded with its probe in
`char_results/model_mc021_lane_slot_2026-11-19.md`.

## One decode, two latencies: the hit is three registers from its ACT (2026-11-19, MC-021 step 4)

After step 3 the SKU model and the RTL ran the same pick rules on the four-bank
close-page interleave and settled into different fixed points: the RTL a
steady 11-13-cycle read pattern with one 3-cycle ACT gap (2.17 cycles per
beat, the board's 351 MB/s), the model an aligned 8-cycle one (2.0, 389). The
item said "find which rule's timing". The cycle-aligned replay -- the proxy's
pick probe anchored on a direction-flip COUNT (the absolute cycle moved 900
cycles between two runs of the same sim; the count did not) beside the
model's slot debug from its first slot -- found no rule. It found a register.
The head record's row-hit flag is classified against the bank timers'
registered row image ("one cycle stale by contract") and registered into the
record, and the pick registers the decode once more: a bank's column request
is visible three cycles after its ACT, 72 of 72 in the probe. The model read
the hit live, at ACT + 2. The same decode's ACT class travels the other path
(the bank state with the lookahead, visible at ready - 1), and that one HAD
been measured, in step 3, at 39 of 39 -- and taken as the decode's latency.

The term is invisible on the common path: the next-op hint fires the column
at ACT + 2 in both. It binds where a hold discards the hint, and there the
model's column fired at ACT + 3 and the RTL's at ACT + 5, which under a
rotation at the tRRD floor with one cycle of slack (8 per round against tRC 7)
costs the bank its slot -- and the slip re-arms the discard. With `hit_lag` 2
the model matches the RTL's hop distributions row for row and lands the two
cells (258 / 355 against 258 / 351; 247 / 246 against 242 / 253), compare
55 / 2 -> 56 / 1, the SKU's cells moved 0.7 percent at most.

Four lessons. **Measure a decode's latency per CLASS, not per decode**: a
request can reach the same register by two paths (the bank state, the record),
and one path measured says nothing about the other. **Measure where the hint
is not**: a hint that hides a latency on the common path leaves the latency
alive on the path the hint does not cover, and an attractor lives on the rare
path -- probe the discarded-hint case, not the hinted one. **An attractor is
reproduced when the hop DISTRIBUTIONS match, not when the number does**: the
number (389 -> 355) could have been a knob; the model earned the term when its
ACT -> column (2 / 5 / 7), same-bank ACT -> ACT (7 / 8 / 9 / 11) and lane /
main shares came out the RTL's. **Anchor a replay on a count, not a cycle**:
a flip count, a transaction count, an event ordinal -- anything the sim's
host-side jitter cannot move. The record is
`char_results/model_mc021_hit_lag_2026-11-19.md`; the term's price in the RTL
(the leftover pick that starts the chain) is in its section 5.

The price was then paid and scored (MC-021 step 5, the same day): the one-term
RTL change built at 100 MHz, and the board moved exactly the cells the model
had moved and by the amounts it said -- bl4 258 / 351 -> 283 / 388 against a
predicted 283 / 389, the interleaved bl4 read +25 against +27, three
close_page cells within 1.5 percent -- while 62 cells did not move, as it also
said. **A priced RTL question is a prediction; score it cell by cell, not by
the headline.** The two cells the model had wrong before the change were
wrong by the same amount after it, which is what separates a model's missing
terms from its right ones: a term that is right moves with the RTL, a term
that is missing does not move at all. And **a cell that does not repeat is a
mechanism, not noise**: `open_page mixed_bl8` gave 311 / 522 three times in
five runs and 272 / 272 twice, with every other cell repeating to the MB/s
across all five; it is counted, not averaged
(`char_results/board_mc021s4_granite_sku100_2026-11-19.md`).

**Measure the arrival path per direction (MC-021 step 6, 2026-11-19).** The
pick sees a beat as the store's head record, and the store builds its write
and read records from different gates: the write record waits for the entry's
data fill and the fill-done register (`has0 && r_wr_fdone`), the read record
is the queue alone. A write beat entering an EMPTY bank queue is therefore the
pick's request two cycles later than a read beat, and the single admission lag
measured on the read path hid it everywhere a queue never empties (every
single-bank stream). It showed only under close page with bursts rotating
banks, where every burst's first beat lands in an empty queue and the two
cycles put the new bank's first ACT in the cycling banks' tRRD collision slot
-- a two-bank lock the model also has but escapes, because its new bank lands
one slot later and the lane rides its ACT. The method: from the probe's queue
counters, time landing -> request separately for reads and writes before
trusting one lag for both (`char_results/model_mc021_wr_fill_lag_2026-11-19.md`).
A per-pair script indexed over half the pairs counted half the collisions and
read as two mechanisms; check a per-pair histogram against the fire count.

**A one-slot difference can pick an attractor (MC-021 step 7, 2026-11-19).**
The direction register on the close-page mixed cell has two self-consistent
steady states under one rule set: the waiting direction holding one bank at
the cap and the other empty (turns of 16 columns, both directions sharing the
window) or holding both banks (turns at the 255 cap, one direction starved).
The RTL and the model, same rules, same cap, same in-order stream, sat in
different ones; the dumps showed the decision made once, in the first turns
after GO, by whether a write turn's first ACT fired with the idle counter at 7
or at 8. The slot was the admission path: the model's single three-slot stage
was the pool path's, and the bank-cap path shares two of its three registers.
Two modes in a cell are therefore not noise to average and not two
mechanisms to name -- they are one race; find the counter that decides it and
measure it cycle for cycle on both sides. And **measure a lag per path, not
per name**: one number for "the admission" was right on the path it was
measured on and one slot wrong on the other
(`char_results/model_mc021_admission_gates_2026-11-19.md`).

The board's bimodal open-page mixed cell was the same shape one level up
(MC-021 step 8, same day): the proxy is seeded once, so rerunning it gives
one mode; what varies between board runs with a hardware GO is the refresh
counter's phase, and sweeping `TEST_TREFI` by a few cycles in sim gave both
modes. **A bimodal board cell is a phase to sweep, not a seed to re-roll**, and
the model needs a GO-phase knob (`GRANITE_GO_OFFSET`) before it can be asked to
show both. The term the model was missing was again a register read live on
one edge and registered on the other: the record's hit flag lagged the row
image after an ACT (`hit_lag`) but not after a PRE; **a lag measured on one
transition applies to the other until measured otherwise**
(`char_results/model_mc021_mixed_modes_2026-11-19.md`).

Once a cell has two modes, one number per cell cannot judge the model, so the
compare reads such a cell by mode: the board's reruns grouped within the
tolerance, every board mode needing a model phase within tolerance, and a
model phase in a mode the board never showed counting as OUT -- that second
direction is the one a "within tolerance of either" rule would miss, and it
found the first real error in the SKU model's stand-in for the hybrid page
predictor (`defaults` run as open page: the board's predictor never entered
the fast mode on five runs where plain open page did on three; memory-
controllers ISSUE-006). **A mode the model shows and the board does not is
as much a finding as the reverse.** The model's default phase stays the slow
mode: the board's mode is a draw at GO, and a model that picked the lucky
phase would be fitting the draw, not the controller
(`char_results/compare_model_sku_vs_board_sku100s4_s8_modes_2026-11-19.md`).

## The page policy was a stand-in, and the stand-in matched the MB/s (2026-11-20, ISSUE-006)

The SKU model ran the board's `defaults` preset as plain open page with the
drain auto-precharge for three weeks, within 1.8 percent on every cell, while
the RTL's `defaults` is the hybrid (conflict-only drain auto-precharge gated
by per-bank history, a 2-cycle idle-timeout close). Two things found it out,
neither a bandwidth number: a cell with two modes on one preset and one mode
on the other (the by-mode compare), and a command the RTL issued ~700 times
per run that the model never issued (MC-019's lane PREs). **A stand-in that
reproduces a cell's throughput can still be issuing a different command
stream to get there**; count the commands (`PERF_CMD_TRACE` on the proxy, the
model's `lane_pre` / `to_pre` / conflict columns) before pricing anything
that touches them. The term itself was read from `mc_page_policy.sv` and
`ControllerConfig.apply`, not fitted: the preset is what the host programs,
and the proxy's own `TEST_PAGE_POLICY` knob had been programming only half of
it. One defect on the way is worth its sentence: **a delayed view compares
against the image of its own cycle.** The policy's history sees the issued
command one cycle late (PRED_CMD_REG); compared against the live row image,
an ACT found its own row open and read as a mistaken close, and the drain
auto-precharge never armed (-18 percent on one cell). The RTL's registered
image lags by the same cycle, and so must the model's
(`char_results/model_issue006_page_policy_2026-11-20.md`).

## The slot was not the tax: the phase margin was (2026-11-21, MC-020)

The model's `slot1` variant (a command slot every CK) priced `col_major` at
+7 .. +15 percent, and the task read that as the one-slot-per-MC-cycle rule
and named two idle-slot row-fire forms. Both priced at 0.0: on a one-bank
chain the main slot fires the ACT the slot its timer opens. What `slot1` had
measured was the HOST -- `ddr2_timings_mc_cycles` pads every ns-derived
minimum by one CK for an unknown DFI phase, and the phases are fixed, so the
exact count is ceil((n_ck - (b - a)) / 2) for a hop from phase a to phase b.
**When a variant that changes the model's granularity moves a cell, ask
which term rounded, not which structure is missing**: tRC, tWR, tWTR, tRRD
and tRFC each lost a cycle, and tRRD alone was halving the ACT rate of every
close-page stream on the board (bank_interleave 387 -> 583 MB/s).

Two methods out of it. **Price a timing change as a preset, not a knob**: the
phase-exact counters became `DDR2_GRANITE_SKU100_PX` with a test pinning it to
the host function AND to the JEDEC minima on the SKU's phases, so the
model's number was the board's prediction (312 / 448 / 568 against 311 / 446 /
565). **Check the proxy's command stream at the CK, not the model's
cycle**: the controller's timers are MC-cycle counters and the DRAM model's
checker compares CK counts at the wrong clock (its "soft violations" have
been noise for weeks), so the trace now carries each command's DFI phase and
`mem-ctrl-ip-ddr2/bin/jedec_ck_check.py` reads CK = 2 x cycle + phase
against the part, with an auto-precharge as a PRE at the DRAM's internal
close. No timing change goes to the board without that check clean. The
board then confirmed it in 81 cells with 0 mismatched beats
(`char_results/board_mc020_phase_exact_sku100_2026-11-21.md`).

## The default moved to the phase-exact counters, and what the soak had to run (2026-11-22, MC-020)

The owner adopted the phase-exact derivation as the host's default after one
endurance soak at the new counters
(`char_results/board_mc020_default_phase_exact_sku100_2026-11-22.md`). Two
things came out of making the soak mean what it claimed.

**The soak that qualifies a derivation runs on the phases the SKU runs on.**
The bring-up soak (`SimpleTest` + `long_soak`) soft-resets the controller
every round, and the reset state is NOT the SKU: row lane off, `row_phase`
0, the paging resets. The char measures the SKU through
`ControllerConfig.apply` (lane on, `row_phase` 1, the JEDEC set derived for
those phases). A soak through the reset state would have run tWR 4 on
phase-0 row commands, passed, and said nothing about the tWR 3 the SKU runs
with. The `soak` sequence (`bin/seq_soak.py`) re-applies a named config
after every per-round reset (`long_soak(reapply=...)`), so its rounds are
the char's configuration. Before it, no soak had run on the lane at all.

**Derive the timing set from the device as programmed, never at
construction.** `SimpleTest` and `A7Leveling` derived their JEDEC set in
`__init__`, reading the DFI phases back from a register that at that point
held whatever the previous session left (a char run's `row_phase` 1
against the smoke's reset-state 0). Under the margin the phases moved
nothing but tRTP, so a set derived from the stale state was still legal;
the phase-exact derivation counts every hop from them, and a tWR of 3 for
`row_phase` 1 run at `row_phase` 0 is one CK short. The 2026-11-21 smoke got
the right value by the accident of a fresh program. Both classes now derive
in the reset path, after `program_geometry`, and the rule generalises: a
value derived from device state is derived AFTER the code that sets that
state, in the same path, or it describes a device that no longer exists.

The records before 2026-11-22 are the margin's. `JEDEC_PHASE_EXACT=0` on
the board and `TEST_PHASE_EXACT=0` on the proxy restore it; the model's
`sku_margin` variant is that set, and the three model tests that reproduce
numbers recorded under it pin the preset by name (`MARGIN` in
`test_char_model.py`). A test that pins a board number pins the counters
the board ran on, or the next default change fails it for no defect.

## The model's exact term flattered the RTL; price the RTL's sequence first (2026-11-22, MC-020 decision 2)

The SKU model took the auto-precharge path at the DRAM's CK-exact distance
(RDA -> ACT = BL/2 + tRTP - 2 + tRP CK) where the RTL's bank timer sequences
two MC counters -- tRAS from the ACT or the column's recovery, then the same
tRP -- and lands one MC cycle later on the phase-exact counters. The 51 in /
6 out of the morning's compare was read as "the two auto-precharge cells, one
ISSUE-007 draw and three mixed-mode cells". Putting the RTL's sequencing into
the model as a term (`ap_seq`, with the reload value `t_rp_ap_rd` /
`t_rp_ap_wr`) and running it at the RTL's shared tRP moved the compare to
**55 in / 2 out with no RTL change**: the two auto-precharge cells landed
within one percent, and the `defaults` and `close_page` mixed cells came in
too -- two of the three cells filed against the direction register's modes
were this term. The two left out are the open_page modes (ISSUE-005) and the
per-pass draw (ISSUE-007). Three rules fall out:

**The baseline a variant is priced against must be the RTL as it is.** The
model before this term was the ideal on that path, so every delta it priced
for the RTL step was measured from a point the RTL did not occupy, and the
cells it mis-attributed to another issue were the ones where the ideal and
the RTL differ. When the model is faster than the board on a family, ask
which of its terms is exact where the RTL sequences, before filing the gap
under a mode or a draw. A model variant with the term OFF must reproduce the
earlier CSVs cell for cell (60 / 60 here), or the term changed something it
did not claim.

**A hypothesis about the mechanism is a term to test, not a sentence to
write.** The traces said one close-page chain in four takes the exact distance
after the self-close and three take the pipeline's four cycles, and the exact
ones sit at the last column of each four-column AXI burst. "The next burst's
head lands after the close and is a miss from its first record" read as the
explanation; written as a model term (present heads through the record path,
later heads through the lookahead) it gave four cycles on every chain -- 87
MB/s against the proxy's 95 -- so the head is already queued when the close
fires and something else arms it. The record now says "not yet measured",
and the probe stays in the controller, off, with its number. Had the sentence
gone into the record as the mechanism, the next model step would have built
on it.

**A mutation check that does not rebuild the flat is vacuous.** The formal
flats (`make/formal_flat.mk`) are built from the filelist once and not
rebuilt when a source changes; the first mutation of the bank timer (the
write path reloading the read path's value) "passed" the new `a_trp_ap`
assertion because `make prove` ran on the flat of the unmutated RTL.
Remove the flat (or `make clean`) before the mutant run, and confirm the
flat carries the mutation (`grep` it) before reading the verdict. The
rebuilt mutant failed the assertion, as it should; the restored RTL proves.
Also: a harness counter seeded from the DROP of a state bit is one cycle
behind one seeded from the command strobe -- read the block's internal event
off the observability ports at the cycle it fires, or the window the
assertion checks is off by one (it failed at t = 2 and would have passed a
block one cycle early at t = 1).

**A new port on a core the tests drive by name is undriven in sim.** The
granite core suite drives `t_rcd_i`, `t_rp_i`, ... from Python by name; the
two new ports read 0 in Verilator, the self-close reloaded a tRP of 0, and
one test failed once and passed on its rerun -- the suite's summary matched
the baseline with "1 rerun" and the rerun had overwritten the log. When a
block gains a port, grep every TB for the sibling port's name and drive the
new one there; a passing suite with a rerun is not the baseline until the
rerun is explained.

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

## A per-pass level is an orbit; read the inter-refresh cadence, not the refresh gap (2026-11-23)

The board's bank_interleave row-hit cells took one of three bandwidth levels
per pass (583 / 566 / 519 MB/s, exact fractions 1, 32/33, 8/9), a draw per
pass, and the issue named the refresh phase as the candidate. The model's GO
sweep over a refresh period showed nothing (584.6 on every phase), so the
proxy decided it (memory-controllers ISSUE-007,
`char_results/proxy_issue007_bank_interleave_cadence_2026-11-23.md`). Two
lessons:

- **The cost was not where the hypothesis put it.** The gap around every
  refresh is 24 .. 28 cycles in every run, slow pass or fast. What the
  refresh does is re-launch the stream into another periodic orbit of the
  pick pipeline (3 columns per 4 cycles, or 8 per 12 / 13 / 14), which then
  runs for whole refresh periods. Read a trace by inter-refresh SEGMENT
  (`mem-ctrl-ip-ddr2/bin/dram_trace_segments.py`: cadence, ACT phases,
  gaps per segment), not by the event the hypothesis names.
- **A level that holds for a whole pass means the perturbation is
  stationary against it.** tREFI 780 is a multiple of the base orbit's
  period (4 cycles) and the slow orbits' (12, 13), so every refresh lands on
  the same phase of whichever orbit the pass is in and re-launches it; the
  orbit whose period does not divide 780 (14) lasted one segment. Moving
  the proxy's tREFI by one cycle walks the phase and chains the slow orbits
  (779) or never launches them (781, 782). When a board level is pass-stable
  and a draw per pass, ask what period the perturbation is stationary
  against before asking what it costs.

The same day's ISSUE-005 sweep gave the rule's mirror for a bimodal cell:
**price every knob that touches the race before proposing one**
(`model_issue005_hold_idle_modes_2026-11-23.md`: DIR_HOLD_IDLE 0 .. 16 and
DIR_OWNS_ROWS across 40 GO phases on two presets). No value gave the wanted
mode on every phase, and the one that closed the race cost two landed cells
their field gain -- which a single-knob, single-phase pricing would have
reported as a win. And: **a model CSV is dated by the controller build that
made it** -- but a timestamp is a hypothesis about which build, not a
finding (see below).

**When a CSV and the committed model disagree, bisect the model before
blaming the CSV (2026-11-23, MC-023 item 2).** The 2026-11-22 CSVs were
filed as "written before the term was finished" from their mtimes. Reading
the decode at the slot instead found a defect in the finished term: a guard
`m_clk - fire_clk < lag * slot` meant to be off at lag 0, where `fire_clk`
holds a FUTURE fire cycle while the self-close is pending, so the
difference is negative and the guard fires. Fixed, the model reproduced the
"stale" CSVs to the cycle on 120 of 120 cells; the stale story was wrong,
and every sweep run on the defective build had to be re-run -- including a
two-mode race the defect had manufactured on the ISSUE-005 cell. Two rules:
a knob whose 0 means off is gated on `> 0`, never on a compare that happens
to be false at 0; and a difference against a timestamp that can be in the
future is signed, so check what it is while the event is pending.

Related: [[measure-over-the-window]], [[arbiter-compliance-model]].

## A mode that is a draw per run is a lock; compare what the perturbation costs, by where it lands (2026-11-24, MC-023 item 4)

The mixed cell's fast / slow mode on the board was a draw per run, and the
model was fast on every GO phase although its slot-level race matched the
RTL's exactly. The deciding variable was not the race but whether it is ever
armed: only a refresh landing in the last columns of a read turn shifts the
row phase off the cap. The refresh walks ~36 columns a turn; on the RTL the
walk is stationary (the same landing columns every 16 turns, the 16-turn sum
= 15 tREFI), so each phase always or never escapes, and in the model it
drifted, so every phase escaped eventually. What made the difference was the
refresh's COST by landing position (a constant +18 MC in an RTL write turn,
+20 / +15 in the model), traced to one term: the RTL's first ACT after a REF
waits for the pick core's tRFC counter (grant + 16), where the model fired at
the device's tRFC (grant + 13). Two methods: when a mode is a per-run draw,
tabulate where the perturbation lands turn by turn on both sides -- a lock and
a drift look identical in the MB/s; and probe the perturbation's episode on
the RTL (the DRAM trace may not carry the command -- this one has no REF),
since three slots per refresh were enough to turn a lock into a drift.

## A direction's window is not its share of a contended bus (2026-11-24, MC-024)

The read-priority register's write floor under sustained reads was first
quoted as 124 MB/s: the writes' bytes over the write window, first write sent
to last write done. Under read priority the writes finish AFTER the reads, so
that window includes a writes-only tail at full rate after the reads end;
measured only up to the last read completion, the floor was 23 MB/s, a
fifth. The equal-stream board cell had the same blend (307 MB/s of writes
was 23 while the reads ran, then a solo tail). Two rules. A per-direction MB/s
on a two-direction cell is a share of the contended bus only while the other
direction is still live: count the bytes done by the other direction's last
completion (the frontend's `writes_at_read_last`, the CSV's
`wr_bw_rd_live_mb_s`), and check the result is the same at two contention
lengths (reads x4 and x16 agreed at 23; the windows read 124 and 36). And a
knob sweep priced on the blended number can reject the right answer: every
"longer write bursts do not raise the floor" row was the tail talking, and
on the contended rate a 255-column burst at a 256-cycle bound beat the
symmetric register on every column but one.

## An A/B that adds a register write moves GO; on a race cell that is a different mode (2026-11-24, MC-024)

The read-priority RTL's mode-0 check wrote `SCHED_POLICY.dir_mode = 0`
explicitly and the proxy's `open_page` mixed cell at tREFI 781 read 279.6 /
281.7 where the run before the RTL read 300.3 / 506.7. The same cell with
the field left at its reset read 300.3 / 506.7 to the decimal: the one extra
APB write before GO shifted GO against the free-running refresh counter, and
the cell's mode is a draw on that phase (ISSUE-005). On a cell with
refresh-placed modes, an A/B is only an A/B if both arms make the same
register writes; to show "mode 0 is today's register", run the reset, not a
written zero, or compare across a refresh-phase sweep rather than one phase.

## Pin the refresh phase in hardware before a board A/B (2026-11-24, MC-025)

The board's run-to-run spread on granite (the mixed cell's modes, the
bank_interleave levels) was the tREFI countdown's phase at GO, which the
host cannot control over UART. `chargen_regs.REF_ALIGN` makes every launch
reload the countdown `offset` cycles later (`granite_top_geared.refi_reload_i`).
At one offset, `windows` x3 and `every` x2 were identical in wr / rd cycle
counts on every row; unaligned repeats differed on every row. **Run both
arms of a board A/B at the same `TEST_REF_ALIGN`, and sweep the offsets to
see the change across refresh placement; compare cycle counts, not the util
columns** (their denominator comes from meters the host freezes, so they
jitter on cycle-identical runs). This works only because no refresh state
outlives the reload: granite ties postpone and pull-in off. A controller with
refresh credits has to clear those too
(`char_results/board_mc025_ref_align_sku100_2026-11-24.md`). One residual:
a one-cycle draw on one row in 263 survives alignment (memory-controllers
ISSUE-008), so repeat a lone one-cycle difference before believing it.

## A delay term keeps the gate the event comes after (2026-11-25, MC-023)

The close_page read sides were 10 .. 12.5 percent high because the model's
same-row ACT after a self-close fired at fire + 3 where the RTL's fires at
fire + 4. The first probe for it (`ap_close_rec`) gated the ACT from the fire
but, in doing so, lifted the rule that kept the lookahead off BEFORE the
fire: the ACT was armed early and the cell got faster (104 -> 138, the board
93). The term that landed (`ap_row_lag`) adds the delay after the fire and
keeps the earlier gate. **When a "later" term moves a cell the wrong way,
check what it removed before the event.** Read the RTL chain off the proxy's
DRAM trace first: ACT, column + 2, self-close at tRAS, next ACT; the slot
count per chain is the whole answer.

## Compare refresh-placed modes by proportion, not per offset (2026-11-25, MC-023)

The model at the board's `REF_ALIGN` offsets (GO offset `2 (tREFI - o - 1)`
ticks) changes mode within a 10-MC launch shift on both presets, and neither
side pins the launch latency to that precision. A per-offset model-vs-board
mode match is therefore not a test; **compare the share of each mode across
the offsets**. A term that is the RTL's behaviour (the refresh drain's one
PRE per two slots, proxy-measured) can still move a preset out of its board
mode: then another term was compensating, and making the RTL's term the
default waits until that one is found
(`char_results/model_mc023_ap_row_lag_refresh_drain_2026-11-25.md`).

## Model what the record can see, not what the queue holds (2026-11-25, MC-023 item 4)

The hybrid's mixed cell held the RTL's slow mode in the model only after one
slot of visibility: the store counts a pushed entry the next cycle, but the
head record's `behind_empty` / `behind_same_row` see it a cycle after that.
The model read the entry behind the head the slot it landed, so on the first
burst after a refresh a column auto-precharged that the RTL left open (a
"conflict" the RTL could not see yet). One cycle on one refresh shape changed
the refresh's cost at that landing phase, the refresh walk drifted, and every
~42k cycles a refresh landed on the batch cap and moved the turn phase for
good. **When two traces agree on queue depths and disagree on a decision,
probe the record the decision reads.** The pick probe (`PERF_PICK_PROBE_FLIP`
= the flip count to the window; absolute cycles move between runs) decodes
the head records' `behind_empty` bit directly
(`char_results/model_mc023_hybrid_behind_lag_2026-11-25.md`).

## Check the proxy is the SKU before trusting a mode proportion (2026-11-25, MC-023)

`test_granite_char_perf` built the research combiner (`STORE_MERGE_EN` 1) by
default for weeks after the SKU turned it off; `defaults`' mixed cell was fast
on 5 of 8 aligned offsets with it and 2 without. A proxy default that differs
from the board build moves race cells without moving any rate cell, so it
hides. **Before comparing a race cell's mode share, diff the proxy's
parameters against the bitstream's** (`granite_char_top.sv` defines,
`granite_char_macro` defaults) and the host's programmed CSRs against the
proxy's (the board's read-path pair needs `TEST_STRICT_READ_TIMING=1` to
decode in the sim PHY).
