<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Dropped (ended without completing)

---

## PUMICE-008 — Per-beat DFI read deskew
**Status:** dropped 2026-07-21 — superseded; the board fix was PUMICE-005, not this

The theory was that the board read blocker is a HALF-DFI-WORD PHASE SKEW: the
a7ddrphy returns the two 64b beats of a 128b DFI read word at DIFFERENT capture
latencies, so a single whole-word capture takes one beat correct and the other
STALE from the previous read -> exactly 2-of-4 device-words wrong, EVERY read,
INVARIANT to rddata_delay (which shifts both beats together and so can never
fix a skew BETWEEN them). That was offered as the reason leveling found "no
passing tap".

The work was built and it functions — but it was never the board fix. The real
cause was the PUMICE-005 tuple (rddata_delay alignment + honest metrics +
no-rmw writes), and the board reads clean at deskew 0/0.

Recorded so the effort is not mistaken for an accomplishment, and so nobody
re-derives the same theory. What was built, and does work:

- `pumice_dfi_rd_aligner.sv`: per-beat delay lines, runtime max-deskew capture
  so deskew 0/0 is BIT-IDENTICAL, zero added latency. Verified (3 existing
  aligner FUB pass; macro 398 pass — no fallout).
- Red->green FUB: `test_pumice_dfi_rd_aligner_deskew` (deskew_hi=1 realigns a
  modelled skewed stream -> correct) + `_deskew_red` (deskew_hi=0 -> the 2/4
  corruption baseline). No PHY model needed.
- CSR: `PHY_TIMING.deskew_lo[25:24]`/`deskew_hi[27:26]` (regen in lockstep,
  regmap synced). Threaded top->core->dfi_layer->aligner. Top wr_rd_roundtrip
  green (bit-identical at reset default 0/0).
- FAITHFUL model hook: opt-in per-64b-beat skew in DFISlavePHY (RDS-DV,
  `read_hi_skew`/`read_lo_skew`, default 0 = bit-identical; char rate4_x16
  skew-off 3/3 pass). Char env knobs `TEST_READ_HI_SKEW`/`TEST_DESKEW_HI`.
- Host `set_deskew()` (pumice_device -> PHY_TIMING by name) + `train_deskew.py`
  sweep (deskew_lo x deskew_hi, phase-distinct pattern, pick mism==0) +
  `make train-deskew`.
- Integration red->green: refined the model to a per-cycle 1-deep DQ-bus
  pipeline (`_skew_post`, run EVERY dfi cycle incl. idle, via `_skew_cur` set by
  the serve step) so read N's high beat lands on cycle N+1.
  `test_ddr2_char_uart_pagehit_rate4_x16_deskew` (skew=1 + deskew_hi=1) PASSES
  (mism==0); skew=1/deskew=0 fails (the 2/4). Skew-off rate4_x16 stays green.

Removal of the leftover RTL and CSR fields is tracked as PUMICE-007 (issue #39).
