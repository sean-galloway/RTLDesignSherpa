# PUMICE-045: one unattributed mismatched beat, seen once in 1008 matrix cells

### 2026-09-23: re-examine -- batching is now a candidate explanation

This beat was recorded as "unattributed" and was the evidence used to re-enable
write batching by default (`1f6a3bfdf`). Batching has since been shown to
STARVE READS outright ([[PUMICE-039]], fixed in `fc83c1b3c`), so "not clearly
attributable to batching" no longer holds as a reason to discount it. Re-check
against the bounded drain before treating this as noise.

**Status:** open 2026-09-18  **Priority:** P3
**TITLE AND PREMISE CORRECTED 2026-09-18: it does NOT break refresh_credit, and
it is not reproducible. See the repeat data below before acting on this.**

Enabling `SCHED_WR_WM` (2/1) by default broke exactly one cell of the 14-config
board matrix. Measured both ways on the same bitstream, same session:

    batching ON  (2/1) : 251/252   refresh_credit/incremental_bl16  FAILS
    batching OFF (0/0) : 252/252   zero non-OK cells

It is specific on BOTH axes:
  * 13 of 14 configs pass `incremental_bl16` -- only `refresh_credit` fails;
  * `refresh_credit` passes its own `incremental_bl4` and `incremental_bl8`.

So it is the interaction of the write drain with the refresh-CREDIT policy at
the longest burst, not batching generally and not bl16 generally.

**The default has been reverted to 0/0** (opt-in) until this is understood --
"on by default" has to mean safe everywhere. The feature itself is correct:
PUMICE-039's three defects are fixed and it measures clean over 210 runs at
open_page, worth +11.9%..+30.5%. Enable per-run with `TEST_WR_HIGH_WM=2
TEST_WR_LOW_WM=1` or by writing SCHED_WR_WM.

**Process note, recorded because it is the actual lesson:** the default was
changed on evidence from ONE config (open_page) and shipped to all fourteen.
The matrix that caught it should have been run BEFORE the change, not after.
Any future default flip on a config-selectable knob needs the full matrix first.

### CORRECTION 2026-09-18 -- not reproducible, not attributable

The original entry (written from ONE matrix) claimed batching breaks
refresh_credit at bl16. Repeating the full 14-config matrix three more times
with batching ON:

    original matrix : 1 non-OK   refresh_credit/incremental_bl16
    rep 1           : 0 non-OK   (252/252, zero mismatched beats)
    rep 2           : 0 non-OK   (252/252, zero mismatched beats)
    rep 3           : 0 non-OK   (252/252, zero mismatched beats)
    ------------------------------------------------------------
    batching ON     : 1 mismatched beat in 1008 cells

It did not recur in the 756 cells after it. The failure signature was ONE beat
of 64000 transactions (8.2 MB), with wr/rd bandwidth, utilisation and latency
IDENTICAL to the passing run to 3 significant figures -- batching perturbed the
traffic by 10 and 35 cycles out of ~19.5M. Nothing about that says "refresh
policy".

**So the premise is withdrawn.** One event in 1008 cells attributes to neither
refresh_credit nor batching. The batching-OFF comparison is a SINGLE 252-cell
matrix (0 non-OK), which at this rate is not evidence of a difference either --
matched repeat counts would be needed to claim batching is implicated at all.

**Process note, and the actual lesson of this task:** the default was flipped on
one config's evidence, then REVERTED on one matrix's evidence. Both directions
were decided at n=1. The repeats should have come first in both cases.

**What is still worth doing** (independent of this event):
`refresh_ctrl.sv` has no headroom between demanding a refresh and losing one.
While busy, `w_req = (r_pending > w_post_eff)` with post_eff clamped to 7, so
the request asserts at pending == 8 -- which is exactly MAX_PENDING, where
`else if (pend_n < MAX_PENDING)` stops incrementing and further tREFI ticks are
silently dropped ("saturate (data retention violation looming)"). The threshold
to START asking and the threshold to BEGIN LOSING refreshes are the same number,
so any grant latency past that point costs real refreshes. Worth fixing on its
own merits; it is NOT established as the cause of anything above.

**Original starting hypothesis, kept for reference but NOT supported:**
refresh_credit is the only refresh policy that banks credits
rather than pacing refreshes at a fixed interval. A long write drain delays the
refresh the credit scheme is counting on, so the suspect is drain length vs
credit accumulation -- which also explains why only the LONGEST burst fails.
Reproduce with `--profile full` and TEST_WR_HIGH_WM=2, then narrow with the ILA
on REF spacing during a drain (the tRFC decode in reports/ already does this).
