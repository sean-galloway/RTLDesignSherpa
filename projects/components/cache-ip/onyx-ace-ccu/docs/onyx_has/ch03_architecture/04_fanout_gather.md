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

# Snoop Fanout and Response Gather

**Stub: open until D4, N3, and N4 close.** This chapter records the decision landscape for fanout and gather, and the invariants that bound it. No architecture is recorded here until D4, N3, and N4 close.

## Candidates

| Decision | Candidates | What it drives |
|---|---|---|
| D4 Response gather | Fixed response window (all caches respond within N beats, presumed-miss after timeout) vs tagged outstanding snoop IDs with per-transaction completion | gather buffer depth, formal surface, ACE conformance |
| N3 Snoop-response sourcing from in-flight fills | Respond not-present if no fill beat has arrived; forward from fill buffer only after the last data beat; response must never depend on an unrelated event | snoop responder comparators, fill-buffer forwarding, formal progress proof |
| N4 CD-path independence | Never share the snoop-data return path (CD) with `WDATA`; reserve credit/capacity for the WB/Ev/WC/WE family | snoop data channel, write-buffer allocation, credit logic |

## Invariant landscape

Regardless of the D4 candidate, the fanout/gather engine must respect:

- **Snoops carry no IDs and must be responded to in issue order.** CR responses are in the same order as the AC addresses; CD data is likewise in order.
- **Response bound.** A snoop may be delayed only until the last data beat of a matching fill has arrived; otherwise it must respond not-present. Holding it beyond that deadlocks.
- **No snoop to the requesting master.** onyx must not send an AC to the cache that issued the coherent transaction.
- **CD path forward progress.** Snoop data must not be blocked by ordinary writes; if CD shares resources with `WDATA`, those resources must be credit-reserved for the WB/Ev/WC/WE family.
- **Snoop responses do not depend on WU/WLU completion.** Otherwise SI buffers full of interdependent WU/WLU traffic can deadlock.

## What the decisions drive

D4 fixes how onyx knows a gather is complete. A fixed window is simple but needs a proven timeout bound; tagged IDs are exact but need more bookkeeping. N3 and N4 are elaborations of the forward-progress rules: where a snoop response may source its data, and how the CD channel is kept independent of ordinary write traffic.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §7.1 states that snoops have no IDs and the snoop channels are strictly in-order. §7.7 gives the response bound: a snoop matching an in-flight fill must respond not-present if no data beat has arrived, and may forward from the fill buffer only after the last data beat has arrived. §7.7.1 describes the WLU/WB valid/ready deadlock when SI buffers are full. §14.18 confirms that the three snoop channels are independent except for the same-address WB/Ev/WC/WE dependency. §10.6 and §14.11–14.13 emphasize an independent snoop path as the deadlock-avoidance bedrock.

## Status

No architecture recorded. D4 must choose the gather mechanism, and N3/N4 must close the fill-sourcing and CD-independence rules, before the fanout/gather engine can be drawn.
