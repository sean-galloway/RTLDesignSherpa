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

This Hardware Architecture Specification records `onyx`, the snoop-based ACE coherency unit that turns the family's caches into a coherent system on the house AXI4 fabric. Version 0.3 (2026-11-21) is the first version with RTL behind it: the D rows were decided on 2026-11-20 (PRD v0.7) and `onyx_ccu` was built, verified against jet-prime's pair-rig grid, argued formally at two ports and placed on the Genesys2 reference rig in onyx TASK-001.

Real content at 0.3:

- the purpose of the IP and the research claim it must support;
- the system context, use cases and key features as built;
- the manager architecture: pipeline, decision layer, serializer, fanout and gather (Chapter 3);
- the cache-side contract as built (sideband plus plain AXI4 plus the ACE-shaped snoop port), the memory-side master, the fanout port (Chapter 4);
- the parameters and the configurations the rigs build (Chapter 5);
- the verification as done and the characterization as measured (Chapter 6).

Still open, labeled where they shape a chapter:

- the ACE-Lite IO port (D1) and the MonBus taps (D9): later steps of TASK-001;
- the N rows other than N1 and the invariants other than 6: proposed in the PRD, honored by construction where Chapter 3.4 says so;
- a three-port formal harness and a three-cache rig.

## Research question

With the cache side established by `amber` and `jet`, what does the **manager side** of coherence cost? onyx exists to measure the cost of fanout, gather, adjudication, and same-address ordering on the house fabric: gates, latency, and verification effort. The answer must be reproducible — same trace suite as amber's pair rig, MonBus evidence, golden-model parity, and formal proof of the named liveness obligations.

## What onyx is

onyx is the coherence point between the family's ACE-shaped caches and the AXI4 memory path. It receives coherent transactions from attached caches on N cache-side ACE slave ports, broadcasts snoops to the peer caches on the inter-cache snoop fanout, gathers CR responses and any CD data, decides whether the transaction can complete from cache-supplied data or whether memory must be read, and serializes same-address traffic.

ACE is AXI4 plus three snoop channels (AC, CD, CR). The repo already speaks AXI4 with skid buffers, GAXI FIFOs, `axi4_master_rd/wr` wrappers, and Pattern-B BFMs. onyx is the natural extension of that infrastructure; the new logic is the coherence decision layer, the serializer, and the fanout/gather engine.

## What onyx is not

onyx is not a cache (no tag/data arrays of its own), not a directory-based coherence engine (the D3 snoop-filter candidate is the closest it comes), not an L2, not a general NoC, and not a CPU-side or upstream-master port beyond ACE-Lite IO. These boundaries are recorded as explicit non-goals in [Scope and Non-Goals](02_scope.md).
