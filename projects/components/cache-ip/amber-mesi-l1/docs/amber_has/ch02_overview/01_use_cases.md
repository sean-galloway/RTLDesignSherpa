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

# Use Cases

## Primary use case: a correct, observable, provable L1 cache baseline

amber exists so the repo has a first cache IP whose correctness can be checked end-to-end: against a software golden model, against formal proofs, and against hardware cost measurements. The blocking design keeps the coherence protocol in the foreground and the miss-handling mechanics in the background, which is exactly the research posture.

## Secondary use cases

1. **Pair-rig coherence research.** Two `amber` instances plus shared memory form the smallest coherent system in which snoop responses, dirty write-backs, and exclusive-to-shared transitions can be observed and measured (D10).
2. **Onyx-rig CCU attachment.** `amber_ace` attaches to the `onyx` coherency manager and exercises the onyx D2 coherent-transaction subset, so the manager side can be built and verified against a real cache (F12).
3. **STREAM attachment.** The GAXI CPU-side port lets STREAM attach without an adapter; this is the documented future integration hook (D2).
4. **Teaching and trace parity.** The cache_sim trace-replay cross-check makes amber a runnable illustration of how geometry and replacement policy combine into hit/miss behavior.

## What amber is not designed for

High-throughput single-core execution, multiprocessor systems larger than the pair rig, or any workload that depends on hit-under-miss concurrency. Those belong to `jet` or to future IPs.
