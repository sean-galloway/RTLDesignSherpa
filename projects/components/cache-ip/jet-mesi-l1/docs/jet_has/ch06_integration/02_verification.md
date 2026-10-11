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

# Verification Strategy

**Stub: open until J5 and J6 decide.** This chapter records the verification obligations that the architecture must eventually meet. No verification plan is complete here until J5 and J6 close.

## Inherited correctness

jet inherits amber's verification baseline: every amber proof and golden-model parity result must still pass with MSHRs present. Proofs are re-run, not assumed.

## Jet-specific success criteria

Per the jet PRD:

1. **The delta, measured.** On the amber trace suite and at least one board: reported latency/bandwidth improvement with MonBus evidence, and the cache_sim cross-check extended to predict jet's concurrency numbers.
2. **The deadlock corner, proven.** J5/J6 formal targets: no deadlock when MSHRs are full and dirty victims wait behind fills.

## Future proof obligations

The following liveness scenarios from Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, will become formal or directed-test obligations once J5/J6 close:

- §8.2 "Deadlocks": reserve buffer entries for the oldest access so that speculative younger misses cannot starve allocation.
- §8.3 "Starvation": avoid fixed-priority arbitration; use timeout counters to guarantee fairness when snoop-vs-fill or CPU-vs-fill arbitration is contested.
- §10.10.3.1 "Backend victimization deadlock": either forward from the fill buffer when a snoop matches a pending fill, or reserve a victim buffer for every fill.

## Status

No verification plan recorded. J5 and J6 must close before the deadlock and starvation proof strategy can be written.
