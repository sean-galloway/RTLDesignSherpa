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

# Purpose and Scope

## What this document is for

This 0.1 Hardware Architecture Specification is the first architectural checkpoint for `jet`, the lockup-free upgrade of the `amber` blocking MESI snoopy L1 cache. Its job is to fix the parts of jet that are already decided, make the research question explicit, and leave an honest trace of the open decisions (J1–J7) so that later revisions can show exactly what closed and why.

At 0.1 the following are real content:

- the purpose of the IP and the measured claim it must support;
- the system context, use cases, and key features;
- the inherited contracts from amber and onyx;
- the observation requirements that J7 will turn into experiments;
- the decision landscape for J1–J7, with citations to the background material that will inform each choice.

The following are stubs at 0.1 and are labeled as such in the chapters they shape:

- MSHR organization (J1);
- hit-under-miss scope (J2);
- miss merging policy (J3);
- ordering and snoop-during-miss guarantees (J4);
- eviction under misses (J5);
- congestion and fairness policy (J6);
- the measured claim itself (J7).

## Research question

With coherence, arrays, and observation held constant against amber, what do outstanding misses, hit-under-miss, and miss merging actually buy in latency and bandwidth? The answer must be reproducible: same trace suite, same board, MonBus evidence, and a cache_sim model extended to predict jet's concurrency numbers.

## Explicit non-goals

These are out of scope for jet, inherited from the jet PRD non-goals:

- Speculative prefetching.
- Adaptive replacement policies.
- Quality-of-service policies.
- Multi-banked parallelism beyond what the MSHR organization itself implies.

Each of these is a future IP or a later decision. The architecture must not close them off accidentally, but it does not need to implement them.

## Boundary with amber

jet reuses amber's DECIDED rows: the MESI protocol, the shared core, the tag/data arrays, the CPU-side GAXI slave, the fabric-side AXI4/ACE masters, the ACE-shaped snoop port, and the MonBus observation path. Where amber leaves an open question (D3 memory-side shape, D11 array construction), jet inherits the same working default unless a J-row explicitly overrides it.

## Boundary with the MAS

This HAS records architecture-level decisions and open questions. When J1–J7 close, the micro-architecture and signal contracts will move into the jet MAS. Until then, this book deliberately stays above the cycle-by-cycle detail.
