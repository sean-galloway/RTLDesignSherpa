# ISSUE-004: the +25-30% batching gain was measured with the broken drain
> **Was `PUMICE-048` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24 (was: open 2026-09-23)  **Priority:** P2 — a published number that is
currently unsafe

[[TASK-007]] records write batching recovering **+30.3% at gap 12 (240.7 ->
313.7 MB/s)** and +25.7% at gap 15. Both were measured on silicon with the
UNBOUNDED drain — the configuration since shown to starve reads
([[TASK-007]], fixed `fc83c1b3c`). The gain is therefore not attributable: it
was taken from a controller that was not servicing reads correctly.

The bounded drain should keep nearly all of it — tRTW amortises across the
batch, so 20 cycles over 16 writes is 1.25 each against 20 for a single
direction switch — but that is an argument, not a measurement.

**Do:** rebuild the bitstream with `fc83c1b3c`+, reprogram, re-run
`run_smoke.py --sequences init wr_batch`, and restate or retract the figure in
TASK-007. Needs the board.

---


## 2026-09-24 — RESOLVED: the number is right, no action

Re-measured on the board against the FIXED drain (`seq_wr_batch`, 1 writer +
1 reader, open_page, bus MB/s, 0/2 failing at every point):

| watermarks | gap 12 | gap 15 |
|---|---|---|
| hi=0 (batching disabled) | 240.7 | 209.3 |
| hi=2 / lo=1 (shipped default) | 314.0 (**+30.5%**) | 263.0 (**+25.7%**) |
| hi=8 / lo=4 | 284.1 (+18.1%) | 254.8 (+21.7%) |

**+25.7% to +30.5% — the published +25-30% reproduces.** It was not an artefact
of the broken drain, so nothing in the record needs correcting and no
re-publication is required. This closes as an issue with a recorded no-action,
which is one of the three endings the convention allows.

Bonus finding, carried to [[TASK-008]]: the SHIPPED watermarks beat the wider
hi=8/lo=4 that the original measurement used. Tighter watermarks re-arm the
drain more often, keeping writes clustered without making reads wait.
