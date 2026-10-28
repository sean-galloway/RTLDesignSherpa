<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# The Snoop Path Under Concurrency

**Status:** planned contract. The ACE-shaped responder `l1_snoop_resp` is
inherited unchanged; what changes is what it can match against: the tag
array (port B), the MSHR file (pending fills), and the writeback buffer
(draining victims). The match order is fixed: WB buffer, then MSHR file,
then the arrays — the newest claim on the line answers.

## The three answer sources

| Match | Answer | State effect |
|---|---|---|
| WB entry (draining victim) | snarf: CR/CD from the buffer, amber's SINK_WB_ACK semantics | recorded on the WB entry (drain still completes) |
| MSHR entry (pending fill) | the post-fill state, per amber's pending-fill bypass generalized per entry; CD beats only for beats the fill has landed (PF_GUARD: `beats_rcvd`) | recorded in `pend_eff`, applied at commit (amber's `pending` semantics) |
| Tag array | amber's Table 3.0 decode, unchanged | tag downgrade/invalidate on port B, as amber |

## Ordering and progress rules

1. **A snoop never stalls behind a fill or a drain** (Chinnakonda §7.8).
   AC acceptance is gated only by snoop-service occupancy, and snoops
   arbitrate ahead of new CPU accepts (J6).
2. **The anti-livelock hold-off** (ch02/01): the one bounded exception.
3. **CD before CR** — the family convention, inherited.
4. **A snoop matching both a WB entry and an MSHR entry** (the victim was
   captured for a fill of a different line in the same set) is answered
   from the WB buffer — that data exists NOW; the fill's answer would be a
   promise.
5. **Commit-vs-snoop same cycle:** a snoop matching an entry in its commit
   cycle is answered at the POST-commit state (the commit is already
   ordered before the snoop at the PoS — the entry's install is visible to
   the lookup the same cycle the tag write lands).

## What the pair rig needs from this

The pair fabric (inherited from amber) holds one snoop in flight per
direction; jet's concurrency doesn't change the wire contract, only how
many internal structures a snoop may have to consult. The fabric's
deadlock-freedom argument (amber's ctrl_snoop_safe gating) simplifies in
jet to: snoop service never allocates, never waits on a fill, and never
waits on a drain — so it always completes.
