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

## The JEDEC check that found a table error (2026-11-11)

Writing the class constraint by constraint against JESD79-2F showed the
repo's DDR2 ns table (`pumice_device.py::DDR2_MT47H64M16_NS`) carrying tRRD =
7.5 ns, the 1 KB-page column of Table 42; a x16 part with 1K columns is a
2 KB page and its tRRD is 10 ns. At the board clocks both round to 2 CK, so
nothing moved on silicon; at the DDR2-800 span config it is one MC cycle.
Filed as memory-controllers BUG-003. The lesson is the method: **derive each
timing from the spec's table with its page-size / speed-bin column named**,
not from a part's quick-reference line; the model class now carries the
clause beside every constraint so the next reader can check it in one look.

Related: [[measure-over-the-window]] (the window rule is the same one),
[[arbiter-compliance-model]].
