# ISSUE-025: half_threads grades 16 of 32 cells ok=0 on a latency-histogram 1:1 gap of 7 to 40 returns, data clean, every controller

> Source: granite TASK-003 board reruns (2026-10-29) of the `half_threads`
> profile at 75 MHz; the identical grading is in the 2026-10-27 CSVs for
> granite AND pumice (`char_granite75_half_threads_2026-10-27.csv`,
> `char_pumice_rdmerge50_half_threads_2026-10-27.csv`), so it is the
> harness's accounting, not either controller's data path.
> Related: BUG-010 (closed; the same 1:1 check, a different count),
> `pumice_char.py` `_half_record` (`1:1 VIOLATION: hist total != host reads`).

**Status:** closed 2026-10-29 (bug, fixed at source and proven on the board; see the closing entry).

## What is seen

On every `half_threads` run, `rd_hist_total` falls short of the host's read
count by a handful at two or more threads under open_page and at exactly
three threads under close_page: 63,992 of 64,000 (thr2), 95,989 to 95,995 of
96,000 (thr3), 127,963 to 127,970 of 128,000 (thr4 and the clamped thr5..8).
`mismatched` is 0 in every cell and the bandwidth is reproducible to
0.1 MB/s run to run (granite 2026-10-27 vs 2026-10-29, 32 of 32 cells).
Because the record's `ok` is false whenever the note is raised, the profile
exits "16/32 scenarios failed" and `make run` returns 2, which (a) reads as
a board failure in a chained script and (b) marks the open_page thr2..8
cells, the ones the profile exists to compare, as failed on every controller.

The one-thread cells and close_page thr1, thr2 and thr4..8 are exact.
LiteDRAM's host (`host_litedram_char.py`) has no histogram and grades the
same cells ok=1.

## What it is not

Not BUG-010's FIFO depth (that was EXTRA returns under LFSR IDs with
`GEN_MAX_OUTSTANDING` 8; both macros carry 32 now and this is MISSING
returns, 0.01 to 0.03 percent). Not the controller: pumice and granite lose
the same order of count on the same cells.

## To resolve

Decide whether the per-port histogram can be exact under the pair / oct walk
at >= 2 threads (a per-ID RLAST collapse at the port mux is the first
suspect, as in BUG-010's second layer), and until then stop the note from
flipping `ok`: `ok` should follow `mismatched`, with the 1:1 gap kept as a
note and a separate column, so the profile's exit code means what a caller
assumes.

**Clue (2026-10-29, granite TASK-005):** a granite bitstream whose host edge
capped reads in flight at four (an aggregator side queue sized 4) ran the
same `half_threads` profile with the 1:1 note on NO cell (32 of 32 ok,
`char_granite_halfagg75_half_threads_2026-10-29.csv`); the same RTL with the
cap at 32 is expected to show the note again. The under-count tracks the
number of reads outstanding, which points at the histogram's timestamp
queue depth against the engines' admission, the shape BUG-010 had.

## Root cause and fix (2026-10-29)

The clue was right. `char_engine_block` instantiates both
`axi_perf_latency_hist`s on the MERGED port, behind `NUM_GEN` generators
that each admit `GEN_MAX_OUTSTANDING` commands, with the timestamp FIFO at a
fixed `MAX_OUTSTANDING (32)`: 32 covered one generator (the BUG-010 fix),
and two to four generators at 32 each can hold up to 128 reads at the port.
A command that handshakes while the FIFO is full is never timestamped and
never counted (`o_cmd_block` is not consumed there), which is exactly 7 to
40 of 64k to 128k reads at the open_page cells and close_page thr3, where
the controller keeps the most reads in flight. The aggregator bitstream's
depth-4 side queue capped the port at four outstanding, below 32, hence
exact.

Fixed in three places:

- `char_engine_block.sv`: `HIST_DEPTH = NUM_GEN * GEN_MAX_OUTSTANDING` on
  both histograms, so no admitted command can find the FIFO full.
- `axi_perf_latency_hist.sv`: the timestamp array is one flat
  `(* ram_style = "distributed" *)` array indexed `channel * depth +
  pointer`, written from its own reset-free block. It was never reset or
  cleared, but as a two-dimensional `[NUM_CHANNELS][MAX_OUTSTANDING]` array
  written inside the reset-and-clear block Vivado turned it into flops
  without a message, and moving the write out of that block alone did not
  change that; the flat one-dimensional form did. The primitive's own test
  (4/4) and the two observers that instantiate it lint and pass unchanged.
- `pumice_char.py`: `ok` follows wr/rd done and `mismatched`; the 1:1 gap
  stays a note and is its own CSV column `rd_hist_gap` (host reads minus
  histogram samples, positive = missing). The run's exit code now means
  what a chained script assumes.

Proof, granite 75 MHz, same RTL and host as the 06:4x run, board:
`char_granite_setlag75hist_half_threads_2026-10-29.csv` against
`char_granite_setlag75_half_threads_2026-10-29.csv`.

| half_threads, 32 cells | before | after |
|---|---|---|
| cells with a nonzero 1:1 gap | 16 (7 to 42 missing) | 0 |
| cells ok=0 / profile exit code | 16 / 2 | 0 / 0 |
| bandwidth, every cell | - | within 0.1 MB/s of before (largest move: open_page pair thr3 wr 257.1 -> 251.4, a 2 percent run-to-run cell) |
| mismatched beats | 0 | 0 |

The three builds, granite 75 MHz, same tree otherwise (baseline is the
06:xx `setlag` build, 36,386 LUT / 33,715 FF, WNS +1.235 ns):

| build | LUT | FF | WNS | board half_threads |
|---|---|---|---|---|
| depth 128, arrays as flops | 38,282 | 39,908 | +1.080 | 32/32 exact (`...setlag75hist_...csv`) |
| depth 128, write in a reset-free block (still flops) | 38,257 | 39,908 | +0.814 | 32/32 exact (`...setlag75hist2_...csv`) |
| depth 128, flat `ram_style` array (committed) | 35,950 | 31,671 | +0.756 | 32/32 exact (`...setlag75hist3_...csv`) |

The committed form is smaller than the depth-32 baseline in both LUTs and
registers (the 32-deep arrays were flops too), bandwidth on every cell is
within the 2 percent run-to-run of the baseline, and `mismatched` is 0.
Lesson recorded in the handbook: [[sram-and-memories]].
