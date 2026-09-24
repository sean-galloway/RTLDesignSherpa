# PUMICE-048: the +25-30% batching gain was measured with the broken drain

**Status:** open 2026-09-23  **Priority:** P2 — a published number that is
currently unsafe

[[PUMICE-039]] records write batching recovering **+30.3% at gap 12 (240.7 ->
313.7 MB/s)** and +25.7% at gap 15. Both were measured on silicon with the
UNBOUNDED drain — the configuration since shown to starve reads
([[PUMICE-039]], fixed `fc83c1b3c`). The gain is therefore not attributable: it
was taken from a controller that was not servicing reads correctly.

The bounded drain should keep nearly all of it — tRTW amortises across the
batch, so 20 cycles over 16 writes is 1.25 each against 20 for a single
direction switch — but that is an argument, not a measurement.

**Do:** rebuild the bitstream with `fc83c1b3c`+, reprogram, re-run
`run_smoke.py --sequences init wr_batch`, and restate or retract the figure in
PUMICE-039. Needs the board.

---
