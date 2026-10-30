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

**Status:** landed in `jet_control` (Task 7; see ch02/01's Task 7
implementation notes for the landing decisions — the grant-time PF_GUARD
deliverability gate, the commit-window hold-off, and the WB∩MSHR
double-match being unreachable by the drain-race stall). The ACE-shaped
responder `l1_snoop_resp` is inherited unchanged; what changes is what it
can match against: the tag array (port B), the MSHR file (pending fills),
and the writeback buffer (draining victims). The match order is fixed: WB
buffer, then MSHR file, then the arrays — the newest claim on the line
answers.

## The three answer sources

| Match | Answer | State effect |
|---|---|---|
| WB entry (draining victim) | snarf: CR/CD from the buffer, amber's SINK_WB_ACK semantics | recorded on the WB entry (drain still completes) |
| MSHR entry (pending fill, AR accepted) | the post-fill state, per amber's pending-fill bypass generalized per entry; CD beats only for beats the fill has landed (PF_GUARD: `beats_rcvd`) | recorded in `pend_eff`, applied at commit (amber's `pending` semantics) |
| MSHR entry (pending fill, **pre-AR**, Task 9) | the **Invalid row** — no data, and **no effect** (the amber BUG-002 analog) | none |
| Tag array | amber's Table 3.0 decode, unchanged | tag downgrade/invalidate on port B, as amber |

**The pre-AR rule (Task 9).** A snoop matching an entry whose fill AR has
not been accepted yet — the launch still held (`r_fill_pend` / the
presenting fast path), or the engine's AR outstanding (`fill_ar_done_i`
low for the oldest un-done completion-queue fill) — is answered at the
Invalid row with no effect recorded. On the pair rig the fabric holds
such a fill's AR until the snooping transaction completes, so the fill's
data necessarily post-dates the snoop and the entry's own grant
re-resolves it against the winner's committed line. jet has no replay
path (J4 re-sequencing replaces it), so recording a pend_eff there would
silently drop a write fill's merge at the commit — the no-effect answer
is what keeps the fabric's same-line kill answer-neutral instead of
lossy. (amber's blocking pipeline replays a killed pass; jet's contract
is that the kill never invalidates an in-flight fill.) Unit pin:
`snoop_pre_ar_entry` (the launch held by the stub → Invalid row, no
pend, the fill then installs M normally); pair-rig coverage: the
simultaneous-same-line-misses stress exercises it on every loser's fill.

**PassDirty and the pre-RRESP answer (inherited amber semantic, Task 8
integration note).**  A pending RNSD fill is answered at the
S row — never with DataTransfer/PassDirty before the fill's RRESP exists,
because the bypass answers from the *post-fill install state the entry
committed to at alloc* (`sn_install`: M for RU, S for RNSD) and PassDirty
is only known when the last beat returns.  If the RRESP later carries
PassDirty, the commit installs M (amber's #106 rule) — the snoop's
earlier answer stays correct: the pre-RRESP S-row answer is what a
fabric that had already shared the line would have produced, and the
install upgrade S→M is the fill's own business.  `jet_top` changes
nothing here — the semantic is jet_control's, exercised end-to-end
through the real `l1_fill` by the core TB (this bench's plain-AXI4
responders never raise RRESP[2], so the PassDirty→M install itself
remains pinned at the unit level, Tasks 6–7).

## Ordering and progress rules

1. **A snoop never stalls behind a fill or a drain** (Chinnakonda §7.8).
   AC acceptance is gated only by snoop-service occupancy, and snoops
   arbitrate ahead of new CPU accepts (J6).  The arbitration starts at
   *pend*, not at grant (Task 11): a waiting snoop throttles new CPU
   accepts, so the outstanding fills drain and the safe window opens —
   the snoop wait is bounded by the pipe drain (fills × commit length +
   capture windows), never workload-unbounded.  (Pre-fix, sustained
   max-rate miss traffic kept the commit window closed forever — the
   formal L3 counterexample.)
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

## What the pair rig needed from this (landed, Task 9)

The pair fabric (jet_pair_fabric — the amber structure hosting two jets)
holds one snoop in flight per direction; jet's concurrency doesn't change
the wire contract, only how many internal structures a snoop may have to
consult. The fabric's deadlock-freedom argument (amber's ctrl_snoop_safe
gating) simplifies in jet to: snoop service never allocates, never waits
on a fill, and never waits on a drain — so it always completes. The one
place jet's no-replay design needed new semantics was the fabric's
same-line kill: amber replays a killed pass, jet cannot, so the pre-AR
rule (above) makes the kill answer-neutral. The pair rig's
`SimultaneousSameLineMisses` and `PairShipsInTheNight` scenarios pin both
ends of that contract.
