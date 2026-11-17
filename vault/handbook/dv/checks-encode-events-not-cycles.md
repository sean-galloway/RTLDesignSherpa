---
title: A check that encodes the pipeline's cycle timing breaks when the pipeline shortens; check the event
summary: Shortening jet-prime's commit tail by three cycles failed three TB checks that were right about the design and wrong about the cycle: a commit watcher that started sampling one cycle after the done, a slot-state read through a claim-aware helper made two cycles before the retire, and a launch-time contract check, a deposit attributed by a reused ring tag. None was a mismatch of the design; all were mismatches of an assumed offset. Write the check on the event (the state the FSM is in, the entry no longer live, the write to the hazard) and make the first sample the current cycle.
---

# A check that encodes cycle timing breaks when the pipeline shortens

**The case (jet-prime TASK-001 step 5, 2026-11-17).** The commit tail
went from six cycles after the last fill beat to three (snapshot in the
done cycle, no done-check cycle, first deposit with the install) and the
fill launch moved to the alloc cycle. The RTL was right on the first run
of every suite. Four TB checks failed:

- **The control TB's commit watcher** was armed one cycle after
  `fill_done` and took its first sample one cycle after that -- the old
  commit's first store merge landed exactly there. With the snapshot in
  the done cycle the merge landed one cycle earlier and the watcher
  reported "D-4 store merges: got [] expected [(0, 255, ...)]". Fix: the
  first sample is the cycle the watcher starts in (`first = True`, skip
  the await once). The watcher's identification was always the FSM state
  and the entry's `(set, way)`; only the offset was wrong.
- **The core TB's armed-downgrade scenario** read the slot state right
  after the response through the claim-aware helper (`_installed_state`
  hides a way whose MSHR claim is live, mirroring the RTL's hit
  suppression). The response now arrives two cycles before the retire
  frees the claim, so the helper answered `I`. Fix: `_await_retired(line)`
  before the read -- the check wanted the post-commit state, and
  post-commit is the retire, not the response.
- **The same watcher attributed deposits by tag** (`tag in exp_tags`).
  The sequencer releases a deposited tag the cycle after and re-grants it
  at once; with the retire now one cycle after the last deposit, a hit
  granted the reused tag deposited in the retire cycle, inside the
  window, and the watcher reported a fifth deposit for a four-requester
  commit ("one deposit per requester: got [8, 9, 0, 1, 8]"). Only FULL
  reached a four-deep merge list. Fix: qualify the deposit with the
  commit's own attribution tap (`w_cmt_cpl`), not the tag -- a tag is a
  ring slot, not an identity, and the window in which it is unique
  shrank with the pipeline.
- **The core TB's and the tops' launch-time contract checks** ("no fill
  accept during a capture") encoded the old enforcement point; see
  [[enforce-the-contract-at-the-hazard]].

**The rule.** A lockstep TB may key on events (an FSM state tap, a
handshake, an entry leaving the model) and on order (install before
pend, deposits consecutive); it may not key on a distance in cycles
between two events unless that distance IS the property under test. When
a check must wait for "the design has finished X", wait on X's own event,
not on the event that used to coincide with it. And when a watcher is
started by one event to observe the next, its first sample must be the
current cycle: the next event may already be there.

**Why it matters.** All three failures read as design bugs ("the merge is
missing", "the fill committed I", "launch during a capture") and cost a
trace each to refute. A pipeline that gets shorter is the normal direction
of performance work; a TB that assumes the old length will fail every such
step the same way.
