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

# jet_rsp_seq: Response Sequencer

**Status:** planned contract. The J4 mechanism: GAXI has no ID field, so
responses must leave in request-accept order while fills and merges
complete out of order internally.

## Mechanism

- The front end stamps every accepted request with a sequence tag
  (monotonic, wrapping at the sequencer depth).
- Hits complete at lookup and deposit their response immediately.
- Misses deposit at commit (allocating and merged requesters alike — every
  tag on the entry's merge list gets its response from the commit).
- The release pointer walks tags in order: a completed response whose
  predecessors have all released leaves the port; an incomplete head blocks
  only the port, never the internal completion paths.

## Sizing

Depth = `MSHR_COUNT` + hit-pipeline depth (a hit never needs a slot longer
than the pipeline, but merged requesters can outnumber MSHR entries, so the
store is a small FIFO of per-tag completion records, depth
`MSHR_COUNT` × (max merge fan-in) bounded by the front-end accept rate —
the implementation keeps a CAM-free ring: completion records write at the
tag's slot, release reads at the release pointer).

## Backpressure

`rsp_ready` low holds the release pointer; completed responses accumulate
in their slots. CPU-visible effect: response latency grows — exactly what
the J7 hit-latency distribution measures. No internal path ever blocks on
`rsp_ready` (deadlock-free: the memory port doesn't wait on the CPU port).

## What this replaces

Amber's blocking pipeline returns the response at replay, which is
automatically in order. The sequencer is the entire ordering cost of
going non-blocking — one tag field and a release pointer.
