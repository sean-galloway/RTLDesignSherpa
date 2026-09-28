# ISSUE-011: every published board number predates the 2026-09-13/14 harness rewrite

> **Migrated from `PUMICE-036`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-036` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** CLOSED 2026-09-14  **Priority:** was P1

The read/write figures quoted everywhere in this area -- **571.3 MB/s read,
570.2 write, 95% of a 600 MB/s peak** -- were measured before a run of changes
that all touch the measured path:

- the data bridges were removed and the generators now drive `s_axi` through a
  direct N:1 merge plus one skid layer (8f75add68, d54103176);
- the pattern generators' data function changed from a two-multiply hash to four
  rotate-XOR rounds, deleting a 4-stage pipeline, a 16-deep staging FIFO and 48
  DSPs (475b9a53b);
- the generator array went from 2+2 to 4+4 (a78007109);
- the AXI id scheme changed so the generator index rides inside 8 bits
  (7baf98780).

None of that is expected to cost bandwidth -- the skid is full-rate, the hash is
combinational and stallable, and the W address is consumed only on a burst's
last beat so beats still issue one per cycle. **Expected is not measured.** The
simulation asserts only that bandwidth is positive, so nothing in the gate would
catch a regression here.

**Do, in order:**
1. `PUMICE_SYS_75=1 make bitstream && make program` (the 4+4 bitstream is built
   and closes at +0.016 ns).
2. `python3 bin/axlen_sweep.py` -- confirm the read/write figures and the
   Little's-law fit still hold at the new harness.
3. `python3 bin/outstanding_sweep.py` -- never run on hardware. The outstanding
   dial and the 32-deep ceiling exist precisely so this curve can be taken, and
   it is the direct evidence for [[ISSUE-001]]'s latency argument.
4. `python3 bin/bank_gap_sweep.py` then `python3 bin/plot_bank_gap.py
   reports/bank_gap_sweep.json` -- also never run on hardware. Four generators
   on four banks, concurrent read+write, gap 0..15 across three address orders.
5. Check the knees ORDER as §8 of the methodology doc predicts: rising from
   cacheline to row-major to col-major, and falling as generators are added. If
   they do not, either the sweep or the controller is not doing what it claims.

**Update when done:** AT-A-GLANCE, the char guide, and [[ISSUE-001]]'s table.

---

---

## Result — no regression, and the knees order correctly

All five steps run on the Nexys A7 (ttyUSB5, 4+4 bitstream, 75 MHz, BL4, x16,
`open_page`). `axlen_sweep.py` needed a one-line fix first: a missing
`import sys` that had been there since its original commit f02a4b569, so the
script had never once been runnable.

**Step 2 — axlen_sweep. No regression from the rewrite.**

| AxLEN | rd MB/s | % peak | latency | Little's-law prediction |
|---|---|---|---|---|
| 1 | 98.3 | 16.4% | 51.9 | 90.7 |
| 2 | 196.3 | 32.7% | 48.0 | 192.0 |
| 4 | 368.2 | 61.4% | 50.6 | 351.8 |
| 8 | 570.5 | 95.1% | 50.2 | 570.0 |
| 16 | 570.8 | 95.1% | 96.0 | 570.0 |

**Step 3 — outstanding_sweep, first hardware run.** Knees scale as 1/AxLEN,
errors 0-6.5%: AxLEN 1 no knee inside 32 (389.5 MB/s, still climbing), AxLEN 2
knee ~32 (model 25), AxLEN 4 ~24 (model 12), AxLEN 8 ~12 (model 6).

**Steps 4 and 5 — bank_gap_sweep, 192 points, knees order as predicted.**
Largest gap still within 3% of the gap-0 read bandwidth:

| order | 4+4 | 3+3 | 2+2 | 1+1 |
|---|---|---|---|---|
| cacheline | 15 | 15 | 9 | 0 |
| row_major | 15 | 15 | 9 | 0 |
| col_major | 15 | 15 | 15 | 15 |

Read MB/s gap 0 -> 15: 1+1 row_major 574 -> 206 (36% retained), 2+2 575 -> 417
(73%), 3+3 565 -> 565, 4+4 559 -> 559.

The knee rises with generator count because a gap only bends the curve once
aggregate demand drops BELOW the controller's ceiling; at 4+4 even gap 15
leaves each generator at a ~52% duty cycle across four engines, so demand still
exceeds the ceiling. The 4-bit gap field cannot inject enough idle to starve
four generators — at high counts the lever is the outstanding dial, not the gap.
col_major is flat at every count because it is page-miss bound at ~150 MB/s
(25% of peak): the DRAM is the limit, so pacing never binds. A flat col_major
curve is the expected result, not a missing measurement.

**What the run cost, and what it found.** Three defects in the instrument —
`beats_mismatched()` reading only reader 0 (three of four readers unverified at
4+4), points not independent because damage leaked forward, and a docstring
claiming bank disjointness that only holds for col_major — plus one real
correctness defect in the design, filed as **PUMICE-037 (P0)**. 22 of the 192
points carry mismatches and must not be quoted as clean operating points; the
plotter now rings them. The bandwidth numbers themselves stand.

**Still to do (carried, not blocking):** update AT-A-GLANCE, the char guide and
[[ISSUE-001]]'s table with the figures above.

---
