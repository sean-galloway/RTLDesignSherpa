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
- A deposit to the empty head slot is presented in its deposit cycle (the
  head-deposit bypass, TASK-003 step 3, 2026-11-10): `rsp_valid` rises with
  the deposit and the word is the deposit's own, so with the CPU channel
  ready the record leaves on the deposit edge and never occupies the slot.
  Stored records release from their slots as before.  The bypass release is
  not offered to the tag allocator as a same-cycle re-grant (a release from
  a slot is), which keeps the deposit cone out of the lookup accept.

## Sizing

Depth = `MSHR_COUNT` + hit-pipeline depth (a hit never needs a slot longer
than the pipeline, but merged requesters can outnumber MSHR entries, so the
store is a small FIFO of per-tag completion records, depth
`MSHR_COUNT` × (max merge fan-in) bounded by the front-end accept rate —
the implementation keeps a CAM-free ring: completion records write at the
tag's slot, release reads at the release pointer).

## Storage

The per-tag completion record is two things: a `r_valid` bit per tag (reset,
cleared at the release) and the response word `r_data[RSP_DEPTH]`. The word
store carries **no reset** and is written only by the deposit
(`r_data[cpl_tag] <= cpl_data`); every read of it is qualified by the tag's
valid bit, so an unreset word is never observable. That is the
GLOBAL_REQUIREMENTS 1.4 shape and it lets the store be a distributed RAM;
the async-cleared version was, once the larger stores had moved to RAM, the
reset synchronizer's worst recovery path on the Genesys2 (jet bin 7, FPGA
review 2026-11-07). Sequentially the block orders release before deposit
(ch02/01, Task 5 notes): a tag freed and re-granted in one cycle may be
deposited to in that same cycle.

## Backpressure

`rsp_ready` low holds the release pointer; completed responses accumulate
in their slots. CPU-visible effect: response latency grows — exactly what
the J7 hit-latency distribution measures. No internal path ever blocks on
`rsp_ready` (deadlock-free: the memory port doesn't wait on the CPU port).

## What this replaces

Amber's blocking pipeline returns the response at replay, which is
automatically in order. The sequencer is the entire ordering cost of
going non-blocking — one tag field and a release pointer.
