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

# Snoop During Miss

**Stub at 0.1–0.2; J4 and J5 CLOSED 2026-10-28.** This chapter records the
ordering and snoop-during-miss decisions and what they drive.

## The J4 ordering decision (DECIDED 2026-10-28, Sean)

**Out-of-order fill completion, in-issue-order CPU responses.** The GAXI
slave (amber D2) carries no ID field, so responses release in issue order
through a response-sequence queue; fills and MSHRs complete out of order
internally. No ID sideband is added to the CPU port.

**Snoop-on-pending-line: amber's pending-fill bypass, generalized per MSHR
entry.** A probe against a pending line is answered at the post-fill state
(the bypass answers from the fill data once beats have landed; PF_GUARD
semantics included — the bypass only promises data the fill can actually
deliver). The snoop's own state effect is applied after the fill commits,
exactly as amber orders it. A snoop is never stalled waiting on a fill
(Chinnakonda §7.8: holding the snoop can deadlock the system).

## The J5 eviction decision (DECIDED 2026-10-28, Sean)

**Dirty victim captured to a global writeback buffer at miss start; the
fill proceeds immediately; the drain engine writes back oldest-first,
independently of any fill.** Buffer depth `VICTIM_DEPTH` ∈ 1–4, default 2.

- Snoop-on-writeback-buffer keeps amber's SINK_WB_ACK semantics: the snoop
  is served from the buffer (the §10.8.1 "snarfing" pattern), so a snoop
  never blocks on the drain path — and the ships-in-the-night corner
  (§10.12.2: WriteBack in flight, pre-BRESP, meets a clean-invalidating
  snoop to the same line) is answered from the buffer, never "not present".
- Per §10.10.1, the buffer entry's ADDRESS is retained until BRESP (the
  RAW hazard guard); splitting address/data lifetimes is a later area
  optimization.
- Buffer full stalls only new dirty-victim misses; drains always complete
  (the memory write path is always drainable), so the §8.2 victim-buffer
  deadlock is closed by construction.

## The anti-livelock rule (book §10.9 / §8.1, recorded with J4)

After an upgrade (CLEAN_UNIQUE) for line L is granted, snoops to L are held
off — briefly and finitely — until the write completes its commit. Once the
cache owns the line it finishes the store before reacting to incoming
snoops; otherwise two peers can shoot each other's ownership down
incessantly. The hold-off is a temporary block bounded by the commit
latency of an already-granted write — the one block §8.2 explicitly
permits; never event-dependent or indefinite.

## What these decisions drive

- a response-sequence queue between the MSHRs and the GAXI response port;
- per-MSHR-entry bypass comparators feeding the snoop responder;
- the writeback buffer (tag + line data + state) and its drain-oldest-first
  arbiter;
- the J6 formal liveness targets (ch06/02).

