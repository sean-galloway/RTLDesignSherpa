---
title: The arbiter compliance model
summary: Three defects that made a correct arbiter look broken - wrong request vector, no r_last_valid mirror, ACKs handled live against a table built during replay. All three were model bugs, and the fix has to go where the state actually advances.
---

# The arbiter compliance model

`ArbiterCompliance` (RTLDesignSherpa-DV,
`components/shared/arbiter_compliance.py`) tracks round-robin mask state and
computes an expected winner for every grant. It is the only thing in the
arbiter suite that can catch a rotation fault. It is also, on three separate
counts, what was producing the faults.

**Every violation it reported in 2026-07/08 was a model defect. The RTL was
correct each time.** That is the prior to hold when it complains.

## It advances during replay, not live

Grants are queued (`queue_transaction`) and the mask state is advanced later,
while `run_compliance_analysis` walks that queue. Anything you change from the
monitor's sampling loop touches state the replay re-derives, and changes
nothing.

The first fix for the `block_arb` violation reset the mask live, in
`_process_grant_changes`. It looked right, it ran, and the violation was
completely unaffected. **Before fixing anything here, establish whether the
value you are correcting is computed live or on replay.**

## The replay cannot see cycles

It sees grants. Idle cycles between them have to be counted by the sampling
loop, which sees every cycle, and handed over with the transaction
(`idle_before`). Deriving them from transaction timestamps instead looks
equivalent and is not: that inference produced 40-60 false violations per run.

## The three defects

1. **Wrong request vector** (COMMON-018). The check was always paired with the
   *previous* cycle's requests. Correct for a DUT that registers its grant,
   wrong for one that drives it combinationally - and it made a correct
   arbiter look like it granted clients that never asked, 144-176 times per
   run. Now selected by the `registered_grant` constructor argument.
2. **No `r_last_valid` mirror** (COMMON-017). Two grant-less cycles drop the
   RTL's priority mask back to reset; the model carried its pre-idle winner
   across the gap and reported a violation on the first grant after every
   `block_arb` interval.
3. **ACKs processed live against a replay-built table** (COMMON-016).
   `pending_acks` is only written during replay, so an ACK handled at sample
   time looked at a table that did not contain its own grant - reported as
   `unexpected_ack`, 100-200 per run. ACKs are now queued (`queue_ack`) and
   replayed in one timestamp-ordered stream with the grants.

The ACK path still loses a grant; see COMMON-019.

## Measure the RTL, do not argue from it

The threshold in defect 2 was derived twice from reading the source and was
wrong both times - off by one in opposite directions. What settled it was a
20-line probe: park the mask on a known client, hold requests low for N cycles,
request two clients that discriminate between "rotation held" and "mask reset",
read `grant_id`.

    idle_cycles -> first_grant_id: {0: 3, 1: 0, 2: 0, ...}

Beware the probe's own timing. That result reads as "one idle cycle resets it",
but the probe presents requests the cycle *after* the counted idle cycles, so
its N=0 is the model's `idle_before=1`. The rule is two. **A probe is only
ground truth once you have accounted for when its stimulus actually lands.**

## Never quiet it by name

Both arbiter TBs used to carry a `MODEL_DEFECTS = {'round_robin_violation'}`
exclusion so the suite would pass. That hid defect 1 for as long as it existed.
The verdict is now asserted with no exclusions in no-ACK mode, and logged at
WARNING with full per-violation detail in ACK mode until COMMON-019 closes.
Print the whole record - `expected`, `actual`, `active_requests`,
`current_mask`, `last_winner` - because the type name alone starts every debug
session over from nothing.

Related: [[measure-over-the-window]], [[bfm-usage]], [[test-review]].
