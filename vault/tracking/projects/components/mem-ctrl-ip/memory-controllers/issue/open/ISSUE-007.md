# ISSUE-007: the bank_interleave row-hit cells at the phase-exact counters sit at the 583 MB/s ceiling with a per-pass draw a step below it (566 on five to seven cells, ~520 on one) that the model does not have

> Source: memory-controllers MC-020 decision 1, 2026-11-22
> (`char_results/board_mc020_default_phase_exact_sku100_2026-11-22.md`,
> section 4). Filed when the host default moved to the phase-exact derivation
> and the board was re-baselined.

**Priority:** P3 -- the `bank_interleave` preset is not the shipped SKU
(`defaults`), no cell mismatches, and the step is 3 percent on most of the
affected cells; the 11 percent step hits one cell per run. A model-vs-board
question first.
**Status:** open 2026-11-22
**Owner:** TBD

## The observation

Under the one-CK margin every `bank_interleave` row-hit cell on the board ran
387 MB/s, the tRRD-bound ACT rate, and the model matched it. At the
phase-exact counters (tRRD 1 MC) the stream reaches the port's 583 MB/s
ceiling, the model gives 585 on every cell, and the board gives three levels:

| run | 583 (ceiling) | 566 (-3 percent) | ~520 (-11 percent) |
|---|---|---|---|
| 11-21 `every` (flag) | 25 of 36 directions | 10 | 1 (`row_major_bl16` writes 521) |
| 11-22 `every` (default) | 24 of 36 | 11 | 1 (`row_major_bl4` writes 519) |

Which directions fall is a draw: the two runs disagree on every one of the
eleven cells that moved between them (`board_delta`, 66 of 77 cells within
one percent, the eleven all here but one), and the 520-level cell changed.
Single-direction passes (a write pass, a read pass) take the step, so it is
not the direction register's race (ISSUE-005). The -11 percent is one slot in
nine (583 x 8/9 = 518); the -3 percent one in thirty-three. The refresh
phase at GO against the four-bank ACT rotation is the obvious candidate: at
the ceiling a REF's tRFC 13 plus the ACTs it displaces is a fixed cost per
tREFI 780 (1.7 percent), and a rotation that re-phases badly after each REF
could pay it several times over.

## What settles it

1. The model with its GO swept against the refresh phase
   (`GRANITE_GO_OFFSET`) on a bank_interleave row-hit cell: does it show the
   566 and 520 levels on any phase? It shows 585 at phase 0. If it never does,
   the mechanism is not in the model and the proxy decides.
2. The proxy (`TEST_DUAL=1`, phase-exact default) on the same cell with
   `TEST_TREFI` moved a few cycles, the DRAM trace into
   `bin/jedec_ck_check.py` and a per-REF ACT-cadence probe: what the slot in
   nine is.
3. Then either a model term (if the RTL's refresh re-phasing is a mechanism
   the model lacks) or a pick-core question (if the slot is a hold the RTL
   need not take), priced in the model first as MC-021 did.

> 2026-11-23 (`char_results/proxy_issue007_bank_interleave_cadence_2026-11-23.md`):
> steps 1 and 2 done. The model: 584.6 on all 40 GO phases of three cells --
> the mechanism is not in it. The proxy (close page under
> SCHEME_BANK_INTERLEAVE, one generator, tREFI 776 .. 784): the levels are
> cadence ORBITS the stream locks into after a refresh, not a per-refresh
> cost -- the gap around every refresh is 24 .. 28 cycles in every run; between
> refreshes the stream runs 1.333 cycles per column (3 columns per 4 cycles,
> the 583 ceiling with the refresh) or, after some refreshes, 1.500 (8 per
> 12: the board's 519 = 8 / 9), 1.625 (8 per 13), 1.750 (8 per 14) or 1.250
> (tFAW-exact, 586), for one or several refresh periods. tREFI 780 is a
> multiple of the base (4), 1.5 (12) and 1.625 (13) orbit periods, so on the
> board every refresh re-launches the orbit the pass is in -- that is why a
> pass holds one level for 461 refreshes. In the 1.5 orbit the first ACT of
> each burst pair waits five slots past the bank's readiness for a head that
> is not there; not the pool (32: the orbit moves pass), not the generator's
> window (8: identical). The 566 level (32 / 33) had no orbit in these eleven
> phases. Step 3 waits on the pick probe across a slow re-launch (the record
> names the cycles); filed into MC-023 with the model's open self-close term.
> New tool: `mem-ctrl-ip-ddr2/bin/dram_trace_segments.py`.
