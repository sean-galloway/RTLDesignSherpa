# ISSUE-025: half_threads grades 16 of 32 cells ok=0 on a latency-histogram 1:1 gap of 7 to 40 returns, data clean, every controller

> Source: granite TASK-003 board reruns (2026-10-29) of the `half_threads`
> profile at 75 MHz; the identical grading is in the 2026-10-27 CSVs for
> granite AND pumice (`char_granite75_half_threads_2026-10-27.csv`,
> `char_pumice_rdmerge50_half_threads_2026-10-27.csv`), so it is the
> harness's accounting, not either controller's data path.
> Related: BUG-010 (closed; the same 1:1 check, a different count),
> `pumice_char.py` `_half_record` (`1:1 VIOLATION: hist total != host reads`).

**Status:** open 2026-10-29 -- undiagnosed; not blocking (bandwidth and
integrity columns are valid; the `ok` flag and the run's exit code are not).

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
