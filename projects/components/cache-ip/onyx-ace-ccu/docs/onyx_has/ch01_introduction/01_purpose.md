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

# Purpose

## What this document is for

This 0.1 Hardware Architecture Specification is the first architectural checkpoint for `onyx`, the snoop-based ACE coherency unit that turns the family's caches into a coherent system on the house AXI4 fabric. Its job is to fix the parts of onyx that are already decided, make the research question explicit, and leave an honest trace of the open decisions (D1–D6, D8–D11, N1–N7) so that later revisions can show exactly what closed and why.

At 0.1 the following are real content:

- the purpose of the IP and the research claim it must support;
- the system context, use cases, and key features;
- the cache-side ACE port contract, because D7 is decided;
- the memory-side AXI4 master contract and the snoop fanout contract as the decided landscape permits;
- the seven proposed design invariants mined from the PRD;
- the verification success criteria, including the named formal proof obligations;
- the decision landscape for every open D/N row, with citations to the background material that will inform each choice.

The following are stubs at 0.1 and are labeled as such in the chapters they shape:

- manager pipeline shape (D1/D2);
- coherence decision layer and memory-read elision policy (D3/D6);
- serializer / PoS structure (D5);
- snoop fanout and response-gather mechanism (D4, N3, N4);
- MonBus event classes and counter mapping (D9);
- parameter list and sizing math (D4/D5/D11);
- synthesis/implementation cost targets (success criterion 5).

## Research question

With the cache side established by `amber` and `jet`, what does the **manager side** of coherence cost? onyx exists to measure the cost of fanout, gather, adjudication, and same-address ordering on the house fabric: gates, latency, and verification effort. The answer must be reproducible — same trace suite as amber's pair rig, MonBus evidence, golden-model parity, and formal proof of the named liveness obligations.

## What onyx is

onyx is the coherence point between the family's ACE-shaped caches and the AXI4 memory path. It receives coherent transactions from attached caches on N cache-side ACE slave ports, broadcasts snoops to the peer caches on the inter-cache snoop fanout, gathers CR responses and any CD data, decides whether the transaction can complete from cache-supplied data or whether memory must be read, and serializes same-address traffic.

ACE is AXI4 plus three snoop channels (AC, CD, CR). The repo already speaks AXI4 with skid buffers, GAXI FIFOs, `axi4_master_rd/wr` wrappers, and Pattern-B BFMs. onyx is the natural extension of that infrastructure; the new logic is the coherence decision layer, the serializer, and the fanout/gather engine.

## What onyx is not

onyx is not a cache (no tag/data arrays of its own), not a directory-based coherence engine (the D3 snoop-filter candidate is the closest it comes), not an L2, not a general NoC, and not a CPU-side or upstream-master port beyond ACE-Lite IO. These boundaries are recorded as explicit non-goals in [Scope and Non-Goals](02_scope.md).
