# TASK-060: injectors issue half the DFI burst, addresses alternating bl-hi, bl-lo, bl-hi, bl-lo

> Source: owner, 2026-10-24, while TASK-059 was in progress: "to do: have the
> injectors issue 1/2 the dfi BL and the address are in bl-hi, bl-lo, bl-hi,
> bl-lo". Related: TASK-049 (eight injectors), the char engine's address
> generator (`char_gen_unit`, `program_wr_engine` / `program_rd_engine` with
> `burst_len` / `stride_0`), the burst chopper and the controller's
> legal-AxLEN quantum (`AXI_BEATS_PER_BURST`).

**Priority:** P2
**Status:** active 2026-10-25 (owner: "please fix this in pumice and validate it in sim. Then gather the data.")
**Owner:** TBD

## What is asked (owner, 2026-10-24/25)

Injector transactions of HALF a DFI burst each, and a rotation index
`i = 0..7` that sets how far apart the two halves of one DRAM burst arrive:
at i = 0 the addresses are in order (lo then hi of each burst, back to
back); at i = 1 half a burst is issued first, then the other; at i = 2 a
full burst ahead; and so on. The eight injector threads each take a
different part of the same address line, all issuing out of sequence.
"I want to see aggregation happen, but at some point it must stop happening
much": two half-bursts to the same DRAM burst should be served as ONE DRAM
access while they arrive close together, and that must fall away as the
index spreads them.

## What exists

- **Injector: pure programming, no RTL.** `axi4_master_wr_injector` walks a
  two-dimensional index: the low `idx1_shift` bits are index 0 (times
  `stride_0`, wrapped by `wrap_mask_0`), the rest index 1 (times `stride_1`,
  wrapped by `wrap_mask_1`); `axi_size` sets a narrow beat and the data hash
  is per 32-bit slice of the beat address, so a half-beat lane checks
  exactly. Thread t owns window t of `i + 1` bursts: `start = base +
  t * (i + 1) * BL`, `stride_0 = BL`, `wrap_mask_0` = the window, `stride_1 =
  H` (half a burst), `idx1_shift` = bits of `i + 1`, `txn_count = 2 * (i +
  1)`: it issues the lo halves of its `i + 1` bursts, then the hi halves.
  The two halves of one burst are then `i + 1` transactions apart; i = 0 is
  lo, hi back to back. At the board geometry (BL4 x16, 32-bit beat on a
  64-bit AXI) one burst is one beat and a half is `AXI_SIZE_4` with
  strobes; at the sim geometries with a wider beat it is a shorter AxLEN.
- **Controller: no aggregation of partial requests today.** pumice's only
  aggregation is the split / aggregate of a host burst LARGER than one
  DRAM burst (`agg` / `last` sideband, one B or one RLAST). Two
  half-burst writes to the same `{bank,row,col}` enter `mc_wr_data_cam` as
  two entries and commit as two masked DRAM writes; two half reads issue
  two DRAM bursts and each discards half. So the sequence as asked needs
  a combiner, which is the research item.

## To build (pumice, research vehicle)

1. **Write combiner at CAM insert** (`mc_wr_data_cam`): an insert whose
   `{bank,row,col}` matches an entry that is still UNCOMMITTED merges into
   it -- OR the strobes, overwrite the enabled bytes in the SRAM slot, keep
   the older entry's age -- instead of allocating; the AXI B for the merged
   write still answers in order (the merged entry owes two Bs, or the
   intake's B FIFO is told). The merge window is "the older half has not
   committed yet", which is what the rotation index probes: a merge counter
   (`STORE_STATS_MERGE`, new) and the existing `PAGE_STATS_HIT` (column ops
   issued) give aggregation per host transaction directly.
2. **Reads**: a second half read matching an in-window `mc_rd_cmd_cam`
   entry could share its DRAM burst through the return ring; harder (two
   tickets, one burst). Writes first; reads once the write knee is seen.
   DONE 2026-10-27, see "Read combiner" below.
3. **Family in `pumice_char`**: `half_rot` with parameter `i`, both
   directions, the eight threads per the programming above; grid cells
   i = 0..7, proxy and board (`make smoke` first). Expected shape: ~0.5
   column ops per transaction at i = 0 (aggregated), rising to 1.0 once
   `i + 1` exceeds what the CAM holds across the commit latency -- the
   knee is the number the sequence is for.

Pumice only: granite's FIFO store has no match port and no business
growing one.

## The four board patterns (owner, 2026-10-25, after the one-thread knee)

"On the board, I want four new patterns: one with l0, h0, l1, h1, etc; one
like this except do all 8. Then two super versions where the delay between
each looped from 0-7 clocks." Read as: a streaming lo/hi pair walk
(`half_pair`), the same walk with eight lows then their eight highs
(`half_oct`), and each with the inter-transaction idle gap looping 0..7
(`half_pair_sweep`, `half_oct_sweep`). One thread is the deterministic
ordering; the eight-thread form is the same four under the port mux
(profile `half_burst8`).

## What landed (2026-10-25, uncommitted at the time of writing)

- **Write combiner** in `mc_wr_data_cam` (`MERGE_EN`; `WR_MERGE_EN=1` in
  `pumice_top`, 0 in the core default): a write whose `{bank,row,col}`
  matches a live, unscheduled, un-merged entry merges at fill time -- bytes
  under strobes into the entry's slot, strobes ORed, one commit, two Bs in
  order (`id` then the merged id through a done queue). A commit decided
  before the merge is seen waits for the merge fill; a target gone by fill
  time falls back to a fresh entry. Blocked while another live write carries
  the merged id (same-id B order) or any snarf stream is in flight.
  `STORE_STATS_MERGE` @ 0x18C (free-running), regenerated through
  `bin/peakrdl_generate.py`; scoria / andesite / the TB top tied off.
- **Injector modes** (`axi4_master_wr_injector`, `axi4_master_rd_crc_check`,
  CSR bits `AXI_ATTR.idx1_bit[29]` / `gap_sweep[30]` in `chargen_regs`,
  both directions): `idx1_bit` makes dimension 1 the single bit k =
  `idx1_shift` of the transaction index and dimension 0 the index with that
  bit removed (k = 0 lo,hi,lo,hi; k = 3 eight lows then eight highs; the
  plain split would need a third dimension); `gap_sweep` makes the gap after
  burst n `gap + (n mod 8)`, saturating. Unit cells `idx1_bit_order` and
  `gap_sweep` in both suites, every slave profile; the read TB's preload
  now mirrors the index shaping (it had only modelled stride_0).
- **Families**: `half_rot<d>` (the knee probe, `perf_half_rot_family.py`)
  and the four board patterns in `build-perf/host/half_burst_family.py`,
  ONE implementation for the proxy (`TEST_FAMILIES=half_pair ...`,
  `TEST_HALF_THREADS`, `TEST_HALF_BURSTS`) and the board (`pumice_char`
  `measure_half_burst`, profiles `half_burst` / `half_burst8`,
  `Scenario.threads`). The record carries merges and column ops per write.

## Measured (proxy, board geometry BL4 x16, 4-byte half beats)

The knee, one thread, `half_rot<d>` (the two halves d transactions apart):

| d | merges / writes | column ops per write |
|---|---|---|
| 1 | 1 / 2 | 0.5 |
| 2 | 2 / 4 | 0.5 |
| 4 | 4 / 8 | 0.5 |
| 8 | 0 / 16 | 1.0 |

Eight threads merge nothing at any d: the port mux issues every thread's
low half before any high half, so the halves land ~threads x d apart.
`GEN_MAX_OUTSTANDING` is 32, so the knee is the controller's commit window,
not the host cap: the eight lows share the open row and drain back to back
once the first commits.

The four patterns (32 bursts per thread, 64 writes per thread):

| family | threads | merges / writes | column ops per write | wr cycles |
|---|---|---|---|---|
| half_pair | 1 | 32 / 64 | 0.50 | 85 |
| half_oct | 1 | 0 / 64 | 1.00 | 85 |
| half_pair_sweep | 1 | 10 / 64 | 0.84 | 363 |
| half_oct_sweep | 1 | 0 / 64 | 1.00 | 363 |
| all four | 8 | 0 / 512 | 1.00 | 557 |

Every cell checks every byte of the line on the read pass (0 mismatched).
In the pair sweep the two halves sit 0, 2, 4 or 6 idle clocks apart in
rotation: every gap-0 pair merged and almost nothing beyond it, so the
merge window at one thread is a few clocks after the low half arrives --
four back-to-back transactions fit inside it, eight do not. The sweeps at
eight threads post the same cycle count as without the sweep: the
controller, not the per-thread gap, paces the run.

## Board, first pass (2026-10-25, merge bitstream before the fix below)

Nexys A7 at 75 MHz, `--profile half_burst --txn-scale 4000` (32 000 half-beat
writes per cell), configs close_page and open_page. `make smoke` PASS (init,
write_read, 128 MB memtest).

| config | family | merges / writes | col ops per write | wr MB/s | rd MB/s | peak |
|---|---|---|---|---|---|---|
| close_page | half_pair | 16 000 / 32 000 | 0.50 | 147.7 | 73.1 | 300 |
| close_page | half_oct | 13 690 / 32 000 | 0.57 | 128.3 | 73.1 | 300 |
| close_page | half_pair_sweep | 8 476 / 32 000 | 0.74 | 54.5 | 66.6 | 300 |
| close_page | half_oct_sweep | 0 / 32 000 | 1.00 | 54.5 | 66.6 | 300 |
| open_page | half_pair | 16 000 / 32 000 | 0.50 | HUNG | 220.4 | 300 |
| open_page | half_oct | 9 / 32 000 | 1.00 | 286.5 | 220.6 | 300 |
| open_page | half_pair_sweep | 4 463 / 32 000 | 0.86 | 54.5 | 66.6 | 300 |
| open_page | half_oct_sweep | 0 / 32 000 | 1.00 | 54.5 | 66.6 | 300 |

(peak = one 4-byte half beat per clock.) Two things the proxy's 32-burst
cells could not show: under close_page the oct pattern merges 43 % of its
highs, because each access pays ACT + PRE and the eight lows drain slowly,
so the merge window is long; under open_page it merges none. The window is
the commit latency, and the page policy sets it.

**BUG found on the board, reproduced in sim, fixed.** `open_page/half_pair`
merged every pair and the write engine never completed (sim: 2 000 of 2 000
pairs merged, 2 000 column ops, `wr_done` never, controller idle). The
commit-done queue in `mc_wr_data_cam` (4 deep, one id per pop, a merged
burst takes two pops) had no back-pressure on its push: with an open row,
single-beat bursts and every pair merged the drain pushes one burst per
cycle, the queue overran and the overrun pushes -- B responses -- were
dropped. close_page survives only because each access pays ACT + PRE. Fix:
`cm_rd_valid_o` waits for done-queue room on a beat that will push (room
only grows between a raise and the fire, so valid never drops). Lint clean
at three parameter points; re-verified below.

**Host bug, fixed:** profile `half_burst8` ran ONE thread -- `Scenario.threads`
was clamped by `drv.num_gen`, which is 1 until `sync_gen_config()` reads the
built count off the device; `measure_half_burst` reads it now.

**Timing, attributed by A/B (same text, `WR_MERGE_EN` 1 vs 0):**

| build | WNS | failing | LUT / FF | hotspots |
|---|---|---|---|---|
| combiner off | -5.644 ns | 499 | 46 074 / 34 955 | arbiter cone 68, harness meters / regs |
| combiner on | -5.365 ns | 2 571 | 46 672 / 35 138 | u_wr_cam 965 (median -0.6 ns), u_rd_cam 242 |

**CORRECTION 13:20: that reading was wrong.** `WR_MERGE_EN = 0` only removes
the merge decision; the rewrite of the CAM (strobes out of the BRAM into
flops, the key-carrying fill queue, the per-entry merge state, the done
queue) stays in the netlist. The clean baseline, HEAD + the injector / CSR
changes only (worktree bisect A), closes 75 MHz at **+0.123 ns, 0 failing of
110 862 endpoints, 45 473 LUT**. The design was solid; this task's CAM
rewrite is what broke it (BUG-032 dropped as misfiled). The arbiter cone at
22 levels / 18.8 ns is route-dominated (3.8 ns logic, 15.0 ns route): the
rewrite pushed the part from 71.7 % to 73.6 % LUT and the router lost the
cone. Measured, 75 MHz, Nexys A7 (all four from clean Vivado runs, three of them
in detached worktrees of ed3fed31c):

| text | WNS | failing | LUT / FF |
|---|---|---|---|
| HEAD (ed3fed31c) | +0.002 ns | 0 of 111 194 | 44 353 / 34 949 |
| HEAD + injector modes + CSR bits (bisect A) | +0.123 ns | 0 of 110 862 | 45 473 / 34 838 |
| + CAM rewrite, merge OFF (bisect B) | -5.958 ns | 1 159 | 46 200 / - |
| + merge ON = today's text | -5.376 ns | 3 050 | 46 672 / 35 138 |

The injector modes cost ~1 100 LUT across the 16 engines and close with
margin. The CAM rewrite is the regression, and its STRUCTURE is the bulk of
it: with the merge decision compiled out the miss is already -5.96 ns on
1 159 endpoints (+727 LUT over A). The merge logic on top adds ~470 LUT and
~1 900 more marginal endpoints but does not deepen the worst path. What the
rewrite changed structurally, each a candidate for the clean-up: strobes
moved from the BRAM word into flops (N_SRAM_SLOTS x BL x SW = 256 FF plus the
per-beat OR), the fill queue widened from {slot} to {merge, bank, row, col,
id, qos, slot}, the fetch-time strobe snapshot into the skid tags, the
per-entry merge state, and the done queue in the drain's valid path. Owner's direction: run at 50
MHz now (profile `PUMICE_SYS_50`, closes with 0 failing), then clean this up
under his guidance -- no redesign on my own. The
combiner's own cost is +598 LUT and ~2 000 endpoints in the CAMs around -0.6
ns: the insert-time merge match (`w_mg_hit`, two NUM_ENTRIES x NUM_ENTRIES
compares plus the id-clash scan, feeding `ins_ready_o` in one cycle) is the
cone to pipeline -- it is advisory anyway, since the fill re-finds the target
against live state, so a one-cycle-stale registered candidate costs nothing
in behaviour. Follow-up, not done here.

## Board, fixed text (2026-10-25 12:40, bitstream of the text with the done-queue back-pressure)

`make smoke` PASS (leveled init, write_read, 128 MB memtest); profile
`half_burst`, one thread, 32 000 half-beat writes per cell, 8 / 8 OK, every
byte read back:

| config | family | merges / writes | col ops per write | wr MB/s | rd MB/s | peak |
|---|---|---|---|---|---|---|
| close_page | half_pair | 16 000 / 32 000 | 0.50 | 147.7 | 73.1 | 300 |
| close_page | half_oct | 13 690 / 32 000 | 0.57 | 128.3 | 73.1 | 300 |
| close_page | half_pair_sweep | 8 478 / 32 000 | 0.74 | 54.5 | 66.6 | 300 |
| close_page | half_oct_sweep | 0 / 32 000 | 1.00 | 54.5 | 66.6 | 300 |
| open_page | half_pair | 16 000 / 32 000 | 0.50 | **292.7** | 220.5 | 300 |
| open_page | half_oct | 18 / 32 000 | 1.00 | 286.4 | 220.5 | 300 |
| open_page | half_pair_sweep | 4 475 / 32 000 | 0.86 | 54.5 | 66.6 | 300 |
| open_page | half_oct_sweep | 0 / 32 000 | 1.00 | 54.5 | 66.6 | 300 |

The cell that hung now runs at 97.6 % of the half-beat peak: one host write
per clock with every pair merged into one DRAM burst. The sweeps are
gap-bound (mean 3.5 idle clocks per transaction) and identical across
configs. Timing of this bitstream: WNS -5.376 ns, 3 050 failing endpoints
(the done-queue room is now in the drain's valid path) -- see BUG-032 for
the base miss; the owner's direction (12:38) is to run pumice at whatever
frequency closes for now, so a 66.67 MHz build (`PUMICE_SYS_75=0`) of this
text follows.

**Eight threads at 75 MHz (profile `half_burst8`, now really eight after the
`sync_gen_config` fix; 128 000 writes per cell):** all 16 engines complete,
0 mismatched bytes in every cell, write 207-284 MB/s, read 237-284 MB/s
against the 300 MB/s half-beat peak. Merges: close_page half_pair 45 %,
half_pair_sweep 43 %, open_page half_pair 4.7 %, half_pair_sweep 17 %, oct
0 everywhere (the port mux puts a thread's halves ~8 transactions apart; a
slow close-page commit still catches almost half). Every cell is flagged
NOT OK by the 1:1 check: the read-latency histogram holds 126 689-127 986
entries against 128 000 reads. Data is clean, so the histogram under-counts;
`u_hist_rd` / `u_hist_wr` are among the top failing-timing hotspots of these
bitstreams, so it was re-tested at 66.67 MHz and at 50 MHz (a bitstream with
0 failing endpoints): the SAME counts to the entry (127 986 on close_page
half_pair and half_oct at all three clocks), so it is not timing -- it is deterministic accounting in the read-latency histogram with
eight generators of single-beat reads (candidate: two ARs accepted in one
cycle through the port mux, one histogram entry). Data is clean in every
cell; the engines count their own beats. To confirm in sim with the hist
total exposed (the proxy record does not carry it yet) before the meter is
touched -- a harness item, not a controller one.

## 50 MHz bring-up point (owner 13:05: "get this shit running at 50MHz")

`PUMICE_SYS_50=1` profile added (ddr2_char_top.sv + create_project.tcl: VCO
800 MHz, sys 50, DRAM CK 100 MHz -- below the DDR2 125 MHz minimum, a bring-up
point not a design point). Full text closes: **0 failing endpoints.** Board:
`make smoke` PASS (init, write_read, 128 MB memtest); standard smoke profile
8 / 8 OK (open_page incremental 380.5 / 381.9 MB/s of 400); half_burst 8 / 8
OK with the same merge counts as at 75 and 66.67 MHz (open_page half_pair
195.0 MB/s write of the 200 MB/s half-beat peak, 16 000 / 32 000 merged).
66.67 MHz (`PUMICE_SYS_75=0`): -3.774 ns / 480 failing, yet smoke, standard
char and half_burst all pass. The merge ratios are identical at all three
clocks, as they should be: the commit window is counted in controller cycles.

**Reader levelled with the writer (owner, 13:28: "the read injector needs all
of the same updates"):** `axi4_master_rd_crc_check` gets `GAP_WIDTH` and
`char_gen_unit` drives it from `gap << gap_shift` like the writer (the
reader had ignored `gap_shift`); unit cell `wide_gap`, docs, TB class. Rd
suite 168 / pair 12 on clean builds; the eight proxy cells match the previous
run except two one-thread cells whose read window read 130 instead of 111
cycles -- a rerun of the same build gave 111 again, so that is run-to-run
jitter of the short 64-transaction cells (one refresh in or out of a
111-cycle window), not the change. Timing claims use the 16 000-burst cells.

## Read combiner (2026-10-27, owner: "Fix the read cam so those aggregate")

**Mechanism.** Every live `mc_rd_cmd_cam` entry is a read that has not
issued (issue frees the entry), so an insert whose `{bank,row,col}` equals a
live entry's is a second read of a burst still to come. With `MERGE_EN`
(`RD_MERGE_EN = 1` in `pumice_core`, 0 in the storage plane default, so
scoria / andesite / granite's entry store are unchanged) that insert takes
no entry: `ins_merge_o` hands the ring the matched entry's ticket and the
ring allocates the new ticket as a **shadow** of it (`alloc_merge_i` /
`alloc_src_i` on `mc_rd_return_ring`). A shadow is never issued or filled;
it becomes ready in the cycle its source's last return beat lands and the
fetch reads its beats from the source's slot, so one column command returns
twice, in AR order, and `mc_rd_intake` frames each read's own AxLEN from
it. Nothing in the intake changed. The source slot is **pinned** -- the
tail will not re-allocate it -- until every shadow of it has been fetched
(the shadow's beats beyond the 2-deep prefetch skid are still in the
source's slot after the source itself has drained and freed; with a stalled
R channel the re-allocated slot's return would overwrite them). The match
is not in `ins_ready_o` (a merge still waits for a free entry), so the
compare cone never reaches the admit path; the window is "the first read
has not issued", shorter than the writer's "not committed". The key is the
exact column word, which is what the intake's first-N-beats framing
requires: a different beat window of the same burst is a different column
and its own burst. `STORE_STATS_RD_MERGE` @ 0x190 (free-running) counts
merges; regenerated through `bin/peakrdl_generate.py`.

**Verification.** New unit test `common-ip/dv/tests/fub/test_mc_rd_return_ring.py`
(depth 8, 1 and 4 beats per burst): `pin` is the directed hazard (source,
shadow, six more; drain the source and one shadow beat; stall; `alloc_ready`
must stay low for 40 cycles with the ninth read waiting; release; the
shadow's tail beats carry the source's data; the ninth read then takes the
freed slot) and `random` is a model-driven walk (30 % shadows, issues out
of order, returns in issue order, random drain stalls up to 30 cycles)
checked beat by beat in AR order. Mutation with the pin removed: the walk
returns the ninth read's beats on a shadow and the directed cell sees the
early allocation -- both fail, so the pin is load-bearing. Lint clean at
MERGE_EN 0/1, DEPTH 8/32, 1/4 beats, and on all four cores.

**Proxy (board geometry, one thread, `half_rot<d>`, reads on):** the read
pass merges exactly as the write pass does, zero mismatched bytes:

| d | wr merges / col ops | rd merges / col ops | writes = reads |
|---|---|---|---|
| 1 | 1 / 1 | 1 / 1 | 2 |
| 2 | 2 / 2 | 2 / 2 | 4 |
| 4 | 4 / 4 | 4 / 4 | 8 |
| 8 | 0 / 16 | 0 / 16 | 16 |

**Proxy, the four board patterns (32 bursts per thread, 64 writes then 64
reads per thread, every byte checked, 0 mismatched everywhere):**

| config | threads | family | wr merges / col ops | rd merges / col ops |
|---|---|---|---|---|
| open_page | 1 | half_pair | 32 / 32 | 32 / 32 |
| open_page | 1 | half_oct | 8 / 56 | 0 / 64 |
| open_page | 1 | half_pair_sweep | 10 / 54 | 24 / 40 |
| open_page | 1 | half_oct_sweep | 0 / 64 | 0 / 64 |
| close_page | 1 | half_pair | 32 / 32 | 32 / 32 |
| close_page | 1 | half_oct | 27 / 37 | 0 / 64 |
| close_page | 1 | half_pair_sweep | 16 / 48 | 30 / 34 |
| close_page | 1 | half_oct_sweep | 0 / 64 | 0 / 64 |
| open_page | 8 | all four | 0-3 / 512 | 0 / 512 |

(8 threads: 512 transactions per direction, the port mux spaces a thread's
halves ~8 apart, nothing merges in either direction.) Reads merge every
back-to-back pair, and in the pair sweep merge MORE than writes (24 and 30
of 32 pairs against 10 and 16): a read's window closes at issue, but a read
behind the previous pair's turnaround or page close waits unissued for the
whole gap, while a write's window is its commit. The oct pattern merges no
reads at all: eight lows issue before any high arrives, under either page
policy -- a read is issued the moment its row is open, whereas a write
under close_page waits for ACT + PRE of the access before it, which is
where the 27 oct write merges came from.

**Board, 50 MHz bitstream of this text (`PUMICE_SYS_50=1`, 0 failing
endpoints, 46 861 LUT / 35 512 FF; `make smoke` PASS: init, write_read,
128 MB memtest). CSVs `char_results/char_pumice_rdmerge50_{half_burst,
half_burst8,smoke}_2026-10-27.csv`; "old" = the 2026-10-25 write-combiner
bitstream at the same clock. One thread, 32 000 half-beat reads per cell,
every byte checked, 0 mismatched; peak = one 4-byte half beat per clock =
200 MB/s:**

| config | family | rd merges / 32 000 | col ops per read | rd MB/s | old rd | wr MB/s |
|---|---|---|---|---|---|---|
| close_page | half_pair | 16 000 | 0.50 | **98.1** | 48.7 | 98.5 |
| close_page | half_oct | 0 | 1.00 | 48.7 | 48.7 | 85.5 |
| close_page | half_pair_sweep | 12 223 | 0.62 | 44.4 | 44.4 | 36.4 |
| close_page | half_oct_sweep | 0 | 1.00 | 44.4 | 44.4 | 36.4 |
| open_page | half_pair | 16 000 | 0.50 | 147.4 | 147.1 | 195.0 |
| open_page | half_oct | 0 | 1.00 | 147.1 | 147.1 | 190.9 |
| open_page | half_pair_sweep | 8 321 | 0.74 | 44.4 | 44.4 | 36.4 |
| open_page | half_oct_sweep | 0 | 1.00 | 44.4 | 44.4 | 36.4 |

Under close_page the paired read doubles (48.7 -> 98.1 MB/s, one ACT + RD +
PRE per two host reads instead of per one) and now equals the paired write.
Under open_page every pair merges too, but the one-thread read rate does
not move: it is bound by the read round trip against the thread's
outstanding cap, not by column commands (writes post and run ahead, reads
wait for data). The sweeps are gap-bound either way (same 44.4 MB/s). The
write column is the same text's write pass: identical to the 2026-10-25
run, so the read combiner changed nothing on the write side.

Eight threads (`half_burst8`, 128 000 reads per cell): read merges
**64 000 / 128 000 on half_pair under BOTH page policies** (the write
combiner gets 57 303 close / 6 071 open there: eight generators' lows all
sit unissued in the CAM together, so the read window is wide exactly where
the write window is narrow), 61 004 / 40 778 on the pair sweep, 0 on oct.
Read bandwidth 172-194 MB/s against the 200 MB/s half-beat peak, within
+-2 % of the old bitstream (already saturated at eight threads), 0
mismatched bytes; the cells carry the known 1:1 histogram under-count
(127 973 of 128 000 entries, harness item, data clean -- see "Eight threads
at 75 MHz" above). Standard smoke profile unchanged to +-0.1 MB/s on all
eight cells (open_page incremental 380.5 / 381.9 of 400).

## Thread sweep: where aggregation stops (2026-10-27, owner: "lo0 hi0, lo1 hi1 ... moving 1-8 threads at once offset")

**Correction first.** Every board bitstream in this area (pumice build-perf,
granite target, LiteDRAM flow) carries FOUR injectors per direction
(TASK-043: eight is 91 percent of the part and misses 75 MHz). The host
reads the built count off `GEN_CONFIG` and clamps `Scenario.threads` to it
silently, so the "eight thread" cells above (`half_burst8`, 75 MHz and
50 MHz) were FOUR-thread cells: 128 000 transactions per cell is
4 x 32 000. The numbers stand; the thread count does not. The clamp is in
the record now (`measure_half_burst` notes "threads clamped 8 -> 4 (build
has 4 injectors per direction)"). An eight-injector pumice build at 50 MHz
(`CHAR_NUM_GEN=8 PUMICE_SYS_50=1`) synthesises to 61 515 LUT (97 percent)
and does not place: 13 045 slices needed, 12 858 available.

**Profile `half_threads`** (`pumice_char.RUN_PROFILES`, scenario sweep
`sc_sweep=dict(threads=1..8)`): the pair walk (l0 h0 l1 h1 ...) and the
oct walk, 32 000 host transactions per thread, thread t in its own
contiguous region of the line (an address offset of t x 128 KB, so the
threads' halves interleave only at the port mux), under close_page and
open_page. The same profile runs on granite (`--controller granite`) and
LiteDRAM (`--char-profile half_threads`); those builds have no merge or
column-op counters, so there the evidence is the cost: a controller that
combined the pair would move it faster than the oct walk of the same
bytes. CSVs: `char_pumice_rdmerge50_half_threads_2026-10-27.csv`,
`char_granite75_half_threads_2026-10-27.csv` (the `threads` column is the
count that ran).

**pumice, board, 50 MHz (half-beat peak 200 MB/s), 0 mismatched bytes in
every cell:**

| policy | threads | pair: wr merged | pair: rd merged | pair wr / rd MB/s | oct wr / rd MB/s |
|---|---|---|---|---|---|
| close_page | 1 | 16 000 / 32 000 | 16 000 / 32 000 | 98.5 / 98.0 | 85.5 / 48.7 |
| close_page | 2 | 32 000 / 64 000 | 32 000 / 64 000 | 192.5 / 192.8 | 96.1 / 96.1 |
| close_page | 3 | 48 000 / 96 000 | 48 000 / 96 000 | 192.8 / 193.4 | 142.6 / 142.7 |
| close_page | 4 | 57 289 / 128 000 (45 %) | 64 000 / 128 000 | 179.1 / 184.8 | 187.7 / 188.3 |
| open_page | 1 | 16 000 / 32 000 | 16 000 / 32 000 | 195.0 / 147.4 | 191.1 / 146.9 |
| open_page | 2 | 32 000 / 64 000 | 32 000 / 64 000 | 194.3 / 194.6 | 190.7 / 190.6 |
| open_page | 3 | 47 862 / 96 000 | 48 000 / 96 000 | 193.7 / 194.4 | 190.0 / 190.2 |
| open_page | 4 | 6 078 / 128 000 (4.7 %) | 64 000 / 128 000 | 157.1 / 193.8 | 188.8 / 189.4 |

Reads merge every pair at every thread count the board can run. Writes
merge every pair through three threads under both policies; at four the
write combiner keeps 45 percent under close_page and 4.7 percent under
open_page -- the fourth thread's traffic is what pushes a pair's high half
past the low half's commit. The oct walk never merges (close_page one
thread: 13 690 write merges of 32 000 -- the slow close-page commit
catches a third of the eight-apart highs; reads 0). Where the pair merges
the pair walk beats the oct walk by the column-op count: 2x at one
thread close_page (98 vs 49 MB/s), and at two threads 192 vs 96. Cells
with two or more threads carry the known 1:1 histogram under-count
(63 979 of 64 000 up; harness item, data clean), which is what flags them
NOT OK.

**pumice, sim proxy (`TEST_NUM_GEN=8 TEST_HALF_THREADS=n`, 64
transactions per thread), the 5..8 rows the board cannot build:**

| policy | threads | pair wr merged | pair rd merged |
|---|---|---|---|
| open_page | 1-3 | all | all |
| open_page | 4 | 4 / 256 | 128 / 256 (all) |
| open_page | 5 | 5 / 320 | 15 / 320 |
| open_page | 6-7 | 0 | 15 / 384, 12 / 448 |
| open_page | 8 | 0 / 512 | 0 / 512 |
| close_page | 1-7 | all (223 / 448 at 7) | all |
| close_page | 8 | 223 / 512 | 0 / 512 |

The oct walk merges nothing at any thread count in sim either. So: write
aggregation stops at four threads under open_page (the commit is fast, the
fourth thread's interleave is enough) and at eight under close_page; read
aggregation stops at five under open_page and at eight under close_page.
The sim's four-thread close_page write row (all merged) is rosier than the
board's 45 percent -- the board walk is 500x longer and carries refresh;
the board number is the one to quote.

**granite, board, 75 MHz (half-beat peak 300 MB/s; TASK-003 pass-3
bitstream, WNS +0.299 ns), 0 mismatched bytes:**

| policy | threads | pair wr / rd MB/s | oct wr / rd MB/s |
|---|---|---|---|
| close_page | 1 | 29.5 / 36.9 | 29.5 / 36.9 |
| close_page | 2 | 49.1 / 59.2 | 49.1 / 59.5 |
| close_page | 3 | 72.7 / 87.3 | 72.7 / 87.4 |
| close_page | 4 | 96.4 / 96.5 | 96.5 / 96.5 |
| open_page | 1 | 288.6 / 239.9 | 288.5 / 239.9 |
| open_page | 2 | 286.6 / 287.9 | 286.6 / 287.9 |
| open_page | 3 | 251.2 / 281.0 | 252.9 / 280.0 |
| open_page | 4 | 214.2 / 248.6 | 214.4 / 248.4 |

Pair and oct are the same number to the decimal in every cell: granite
issues one column op per half-burst host transaction whichever order the
halves arrive in. Nothing aggregates, by construction (no combiner, and
the ring's merge inputs are tied off in both store branches).

**LiteDRAM, board, 75 MHz (half-beat peak 300 MB/s), 0 mismatched bytes.**
The flow's bitstream (2026-10-13) predated the generator-config register
and the injector modes the walk needs (the host read zero generators), so
the flow was rebuilt on the current harness: WNS +0.472 ns, 0 failing of
93 999 endpoints, 35 963 LUT; the old bitstream is kept beside the run in
the scratchpad. CSV `char_litedram75_half_threads_2026-10-27.csv`.

| threads | pair wr / rd MB/s | oct wr / rd MB/s |
|---|---|---|
| 1 | 243.0 / 285.7 | 242.9 / 285.5 |
| 2 | 70.7 / 72.0 | 70.7 / 72.0 |
| 3 | 70.2 / 71.5 | 70.2 / 71.5 |
| 4 | 69.6 / 71.0 | 69.6 / 71.0 |

Same picture as granite: pair equals oct in every cell, one column op per
half transaction, nothing combined. (LiteDRAM's own number falls off a
cliff from one thread to two -- its open-page policy against four
regions thrashing one bank -- which is the controller comparison, not the
aggregation one.)

**pumice, board, SEVEN injectors (`CHAR_NUM_GEN=7 PUMICE_SYS_50=1`):
57 417 LUT (91 percent), places and routes but misses 50 MHz by 0.968 ns
on 27 endpoints -- 24 in the FR-FCFS arbiter's `r_wr_pop -> r_wr_col_q /
r_wr_pre_q / r_wr_act_q` cone (the route-bound cone of the timing section
above, now at 91 percent congestion) and three bank-timer -> write-CAM
strobe paths. Run as a labelled timing-failing bitstream: smoke and the
128 MB memtest pass, 0 mismatched bytes in all 32 cells, and the 1..4 rows
reproduce the shipped bitstream's merges and bandwidth to the last digit,
so the rows below are quoted; the bitstream is NOT shipped (build output
restored to the four-injector build; the 7-injector bit and reports are in
the session scratchpad `ht/build7/`). CSV
`char_pumice_rdmerge50_7inj_half_threads_2026-10-27.csv`; the eighth row
clamps to seven (noted in the record).**

| policy | threads | pair: wr merged | pair: rd merged | pair wr / rd MB/s | oct wr / rd MB/s |
|---|---|---|---|---|---|
| close_page | 5 | 64 395 / 160 000 (40 %) | 79 802 / 160 000 (50 %) | 153.2 / 182.8 | 129.5 / 185.8 |
| close_page | 6 | 63 738 / 192 000 (33 %) | 69 681 / 192 000 (36 %) | 101.2 / 110.3 | 64.7 / 71.6 |
| close_page | 7 | 82 458 / 224 000 (37 %) | 86 108 / 224 000 (38 %) | 94.4 / 99.8 | 54.8 / 47.9 |
| open_page | 5 | 4 324 / 160 000 (2.7 %) | 3 419 / 160 000 (2.1 %) | 174.0 / 191.1 | 188.1 / 188.1 |
| open_page | 6 | 17 128 / 192 000 (8.9 %) | 28 754 / 192 000 (15 %) | 172.3 / 187.2 | 156.7 / 173.4 |
| open_page | 7 | 21 468 / 224 000 (9.6 %) | 44 235 / 224 000 (20 %) | 156.8 / 183.8 | 135.9 / 163.1 |

Oct merges nothing at any count. Under close_page the pair walk still
beats the oct walk at six and seven threads (101 vs 65, 94 vs 55 MB/s):
the third of the pairs that still merge is worth that much when the
controller is thrashing seven regions. The sim's "reads hold to seven
threads close-page" was optimistic: on the board reads fall to half at
five threads and a third at six.

**Summary of where aggregation stops (board).** pumice merges every
back-to-back pair in both directions up to three concurrent threads.
Under open_page the window closes at four threads (writes 4.7 percent,
reads still all) and is shut at five (2-3 percent both), recovering to
10 / 20 percent at six and seven as the port mux happens to re-pair
halves. Under close_page the slower commit keeps 45 / 50 percent at four
and five threads and a third at six and seven. The sim says nothing
merges at eight under either policy. granite and LiteDRAM merge nothing at
any thread count: pair costs exactly what oct costs on both.

## Timing census of this text at 100 MHz (2026-10-27)

`PUMICE_SYS_100=1` timing build of the combiner text (shipped 4-injector
config, FR-FCFS), outputs kept out of the shipped `fpga/` dir; reports at
`build-perf/fpga/reports_sys100_2026-10-27/`. WNS **-9.005 ns**, TNS -40.4 us,
22,755 failing endpoints of 113,323, 5,572 inside `pumice_core`; 47,947 LUT
(76 percent). At that TNS the placer stops optimising (2-level paths in
the DFI CDC carry 12 ns of wire), so the level counts are the signal, not
the slacks. The shipped 50 MHz build of the same text closes at +0.029 ns.
Worst path per class inside the core (count, worst slack, levels, route):

| into | from | count | worst | levels | route |
|---|---|---|---|---|---|
| arbiter per-entry COL / ACT / PRE queues (`r_wr_col_q` / `act_q` / `pre_q`) | arbiter `r_rd_pop`, read CAM `r_valid` | 189 | -9.0 ns | 23-24 | 15.6 ns |
| write CAM entry fields, strobe RAM, `r_fdone` | bank timers (fire -> commit) | 1,114 | -7.4 ns | 20 | 13.0 ns |
| write intake W data FIFO flags (commit drain pop) | bank timers | 12 | -6.2 ns | 20 | 12.7 ns |
| ring `r_src` (shadow / snarf source) | write CAM | 811 | -4.5 ns | 9 | 12.8 ns |
| page policy telemetry, `r_to_closed` | arbiter fire, bank timers | 849 | -4.4 ns | 11 | 11.5 ns |
| ring shadow select; ring `r_src` | ring; read CAM | 115 | -4.2 ns | 8 | 12.4 ns |
| read intake R FIFO flags (drain) | ring | 234 | -3.7 ns | 12 | 11.3 ns |
| arbiter `r_col_out` | bank timers | 451 | -3.7 ns | 16 | 10.1 ns |
| read CAM insert (`r_bank`) | write CAM state | 463 | -3.6 ns | 10 | 11.7 ns |
| arbiter `r_wr_pop` replicas | write CAM | 273 | -3.2 ns | 4 | 11.4 ns |

The 75 MHz design-point build of the same text (`PUMICE_SYS_75=1`, reports
at `build-perf/fpga/reports_sys75_2026-10-27/`): WNS **-5.630 ns**, TNS
-3.9 us, 4,221 failing endpoints, 2,935 inside `pumice_core`, 47,336 LUT.
The same cones in the same order: arbiter `r_rd_pop` -> `r_wr_col_q` (23
levels, 15.5 ns route, -5.63), bank timers -> write CAM entry / strobe RAM
(20 levels, 1,105 endpoints, -4.03), DFI CDC (97, -2.25), ring tail -> read
intake R skid (195, -2.17), write CAM -> read CAM insert (461, -1.58),
write CAM -> ring `r_src` (785, -1.45). So the combiner text is 5.6 ns off
its design point and 9 ns off 100 MHz, both route-bound.

Same shape as the 7-injector 50 MHz cone (arbiter `r_wr_pop` ->
`r_wr_col_q` / `pre_q` / `act_q`): the per-entry queue recompute off the
other direction's pop is the deepest thing in the controller, and every
class is route-bound (logic 3 ns, route 10-16 ns). Owner, same day: "the
levels are fine; it's the routing that's killing us" -- the 75 MHz build's
2,935 core paths average 2.2 ns of LUT and 12.0 ns of wire (85 percent);
single nets cost 6-7 ns: the read CAM's `w_rd_sch_v` (66 loads), its row
bits (24 loads), the arbiter's `w_rd_sch_row`. CAM-to-arbiter distance and
fanout, on a 75 percent part shared with the harness, are the problem. Red on
`debug/05_pumice_axi_to_scheduler` is this table. Clean-up of the arbiter
and CAM structure is the owner's call (standing instruction), not this task's.

## Gates

Lint at three parameter points (MERGE_EN 0/1, 1 and 4 beats); pumice
run-all-func-both; injector suites on clean builds (wr 147, rd 161, pair
12); ddr2_char framework run-all-func 222 passed / 2 xfail on the combiner
text (pre-injector-mode run; the post-mode run is in the board section).
