# ISSUE-002: a snarfed write-back victim still drains after passing the line dirty; an IO WriteUnique that lands before it is overwritten

**Priority:** P3
**Status:** ACTIVE 2026-11-24 -- resolved on both sides and sim-verified; the proofs on the regenerated flats are running
**Owner:** TBD
**Filed:** 2026-11-23 (onyx TASK-001 step 7)

## Observed

Found by design review while building the IO port, not yet by a test.
jet-prime's write-back buffer answers a snoop that hits a captured victim
from the buffer (the snarf: a Modified row, DataTransfer and PassDirty) and
then still drains the victim to memory -- `jet_prime_wb_buffer`'s header
says so in as many words ("an invalidated snarfed victim still drains").
After the snarf the dirty responsibility has moved to the manager, which
absorbs the line; the drain that follows writes the same bytes again, so
between caches the duplicate is benign in practice (the absorption and the
drain carry equal data, and the per-line lock keeps the requester from
writing newer data back before the drain's AW is presented in every case
seen).

With the ACE-Lite IO port the duplicate is not benign: a WriteUnique to the
line snoops CleanInvalid, the buffer snarfs (DT + PD), onyx absorbs the
victim, then forwards the IO's bytes. If the victim's AW is presented
before the IO's write is selected, onyx lets the write-back go first (the
IO's WriteUnique is forwarded only when no cache presents an AW to its
line) and the IO's bytes land last, as they must. If the victim's AW is
presented only after the IO's write has landed (a victim queued behind
another drain in a `VICTIM_DEPTH` > 1 buffer), the stale drain overwrites
the IO's bytes in memory and the caches, invalidated, never see them.

## Why

A manager without a directory cannot tell a write-back whose line it has
since absorbed from a fresh one: the write-back arrives as a plain AXI4
burst on the cache's write port. ACE's rule is the master's: a master that
has passed a line dirty on a snoop no longer owns it and must not write it
back. jet-prime drains it anyway.

## Where it lands

- The onyx side is done: the ordering rule above, and the IO's WriteUnique
  waiting for any presented write-back to its line (HAS Chapter 4.5).
- The cache side is jet-prime's: cancel a captured victim's drain when a
  snoop with an invalidating effect has passed it dirty (drop the entry at
  the snarf's effect), or keep draining and mark the AW so the manager can
  drop it. Either is a jet-prime change (its lane is closed; this issue is
  the request).
- The pair-rig soak keeps the IO's writes in a region the caches do not
  touch until the cache side closes; the directed scenarios cover the
  array-Modified case (no victim in flight), which is airtight.

## Resolution

2026-11-24. The hazard was wider than filed: it is not an IO-port race but a
coherence bug between any two writers. jet-prime's own pair rig reproduced it
with two caches and no IO once a hot-set soak phase was added (jet-prime
BUG-002: a victim's drain, held at the fabric while a snoop passed its line
on, landed after the new owner's write-back). Both sides are now fixed:

- **The cache side (jet-prime BUG-002, its delta 05).** A WB entry a snoop
  passes on before its drain starts ends: out of the snarf CAM, retired
  without a drain. One whose drain had started cannot withdraw its AW: it
  drains, and answers no further snoop (`sn_passed_o`). `jet_prime_control`
  holds the head's drain start while a WB-sourced snoop on the head is in
  service. So the "victim whose
  AW is presented only after the IO's write has landed" above can no longer
  exist.
- **The manager side (onyx).** The IO rule above stays (the IO's WriteUnique
  waits for any presented write-back to its line). Added for caches: two
  write-backs to one line go in presentation order (`r_aw_pres` /
  `r_aw_yield` in `onyx_ccu`, `ap_wb_order` on the formal harness, cover
  `cp_wb_order_wait` reached at step 4). The same rule went into
  `jet_prime_pair_fabric`.
- **The soak.** The pair rig's IO loop now issues ReadOnce, WriteUnique and
  WriteLineUnique to the hot lines the caches fight over (the hot-set phase
  after the uniform soak); before, its writes stayed in its own region. That
  phase also exposed a model gap shared with jet-prime's rig: a second snoop
  to a line whose pending upgrade an earlier snoop had killed was resolved as
  the upgrade's resident S; the RTL's Invalid is correct (fixed in both
  models and the core model).

Closes when the onyx `prove` / `prove_book` and jet-prime's control and
pair-fabric proofs pass on the regenerated flats.
