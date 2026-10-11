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

# Block Diagram

**Stub: the block diagram is pending D1/D3/D4/D5.** This chapter records the expected manager shape in prose. No figure is drawn at 0.1.

## Expected manager shape

The following blocks are the natural decomposition of a snoop-based ACE CCU on the house fabric:

1. **Front-end decode, per cache-side port.** Accepts the D2 subset on AR/R/AW/W/B, distinguishes read-side from write-side transactions, and presents a uniform internal request to the coherence decision layer. The exact split and buffering depend on D1 and D2.
2. **Coherence decision layer.** Decides, for each request, whether to fan out snoops, which snoops to send, and how to interpret the gathered CRRESP bits. This layer also holds the memory-read elision decision (D6) and any directory-lite state (D3).
3. **Serializer / PoS.** Orders same-address transactions before they are allowed to proceed incompatibly. The structure depends on D5: per-address scoreboard vs in-order bring-up mode, banked vs centralized, outstanding sizing per D10.8.
4. **Fanout / gather engine.** Drives AC to each peer cache, collects CR and CD, tracks completion, and forwards the chosen data source to the requester or to the memory-side master. The mechanism depends on D4, N3, and N4.
5. **Memory-side AXI4 master.** Issues reads and writes to memory when the adjudication requires it, and handles `WriteBack`/`Evict` drains from the caches. AWID policy is an open D5 detail.
6. **MonBus taps.** Non-stalling `*_monlite` observation points on the cache-side, snoop, and memory-side paths, per the D9 direction.

## What the open rows change

- D1 (functional scope: CCU-only vs interconnect territory) changes whether the memory-side port is a single AXI4 master or a striped/interleaved set of memory ports.
- D3 (broadcast vs directory-lite) changes whether the coherence decision layer maintains sharer state and how the fanout engine selects targets.
- D4 (response-gather mechanism) changes the gather engine's buffering, completion detection, and formal surface.
- D5 (same-address serialization) changes the serializer structure and the concurrency the manager can offer.

Until these rows close, no module boundaries, signal names, or data-path widths are fixed.
