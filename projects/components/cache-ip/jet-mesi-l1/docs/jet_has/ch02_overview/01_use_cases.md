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

jet serves the same two rig contexts as amber, but with the lockup-free delta applied:

1. **Pair-rig research.** Two `jet` caches snoop each other peer-to-peer and miss to shared memory. The use case is the measurement: hit latency distribution, miss concurrency, bandwidth, and MSHR occupancy captured through MonBus, compared head-to-head against `amber` on the same trace suite and board.

2. **Onyx-rig integration.** A `jet_ace` cache attaches to `onyx` as an ACE master and snoop responder. The use case is protocol compatibility under MSHR concurrency: the same onyx D2 coherent-transaction subset and D7 ACE-shaped snoop port must work when the cache has multiple outstanding misses.

3. **Golden-model parity regression.** The `cache_sim` model is extended to predict jet's concurrency behavior; RTL and model are compared per-access across the amber trace suite plus stress patterns that exercise multiple outstanding misses.
