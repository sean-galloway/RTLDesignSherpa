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

**Stub at 0.1–0.2; J5 and J6 CLOSED 2026-10-28.** The verification
obligations are now a plan outline; the detailed DV matrix lands with the
design spec and the jet MAS.

## Inherited correctness

jet inherits amber's verification baseline: every amber proof and
golden-model parity result must still pass with MSHRs present. Proofs are
re-run, not assumed.

## Jet-specific success criteria

Per the jet PRD:

1. **The delta, measured.** On the amber trace suite and at least one
   board: reported latency/bandwidth improvement with MonBus evidence, and
   the cache_sim cross-check extended to predict jet's concurrency numbers.
2. **The deadlock corner, proven.** J5/J6 formal targets, as ruled
   2026-10-28:

   - **Oldest-entry progress:** the oldest MSHR entry always retires (a
     fill once started always completes; no entry is preempted).
   - **Drain progress:** a queued writeback always completes; the drain
     engine never waits on a fill or a snoop.
   - **Snoop progress:** snoop service is never blocked by CPU-side
     congestion (MSHR-full or writeback-buffer-full); snoops arbitrate
     ahead of new CPU accepts.
   - **The composed corner:** MSHRs full + writeback buffer full + snoops
     pending → the system still makes progress (no deadlock), at the tiny
     16-set/2-way geometry under SymbiYosys, per amber D9's
     formal-scoping rule.

   The Chinnakonda §8.3 starvation guidance (avoid fixed-priority
   arbitration without a fairness bound) is met by construction at the
   two arbitration points: the W port gives fill beats priority over write
   hits (a write hit waits at most one fill-beat stream, and fills are
   finite per J1 liveness), and snoop priority over new CPU accepts is
   safe because snoop service is bounded and never allocates.

## Status

Decisions closed; the DV matrix (geometry × MSHR_COUNT × VICTIM_DEPTH ×
policy, Pattern-B GATE/FUNC/FULL grids per amber D9) and the formal harness
list are design-spec content.
