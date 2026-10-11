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

# Scope and Non-Goals

## In scope

Per the onyx PRD §"Where the block sits", onyx sits on three kinds of port:

1. **Cache-side.** N ACE-facing slave-side ports accepting coherent transactions from `amber` or `jet` instances acting as ACE masters. D7 (decided 2026-10-05) fixes onyx as the owner of the ACE-shaped AC/CD/CR snoop port; the caches adapt behind a thin adapter.
2. **Memory-side.** One AXI4 master toward the house memory path.
3. **Inter-cache.** The snoop fanout — AC requests driven into each peer cache, CD snoop data and CR snoop responses returned.

Within those ports, the D2 transaction subset is the recommended research scope: `ReadShared`, `ReadUnique`, `CleanUnique`, `MakeUnique`, `WriteBack`, and `Evict`. These are the transactions the caches need for MESI write-back coherence against a manager, and nothing that requires DVM or barrier semantics.

The 0.1 HAS records the contracts for the three port kinds where they are decided, and the open candidate landscape where the PRD leaves them open.

## Explicit non-goals

These are out of scope for onyx, inherited directly from the PRD §"Non-goals":

- **Cache storage in onyx.** It is a manager, not an L2. The gather point is the natural place to want a cache; that temptation is explicitly out.
- **Directory-based coherence.** The D3 snoop-filter candidate is the closest onyx comes; it is recorded as a candidate, not a requirement.
- **ACE DVM and full barrier semantics.** D8 records this as the recommended non-goal; N6 is a future upgrade path, not a promotion out of non-goals.
- **Cache stash / dealloc features.** Out of scope; future IP or future decision.
- **Multi-CCU / multi-domain systems.** onyx v1 is a single shareability domain with a single manager instance.
- **CPU or upstream-master port beyond ACE-Lite IO.** The only non-cache master port is the ACE-Lite IO path contemplated by D1; any richer upstream port is out.

Each non-goal is recorded so it is a decision and not an accident. None of them is closed off architecturally; they are simply not onyx v1 requirements.

## Boundary with the PRD

This book is architecture, not requirements. The PRD is the binding source for every D/N row, success criterion, and non-goal. Where this book says a chapter is a stub blocked on an open row, the PRD contains the candidates; where this book states a contract as decided, the PRD records the name and date that made it decided.

## Boundary with the MAS

When the open D/N rows close, the micro-architecture and signal contracts will move into the onyx MAS. Until then, this book deliberately stays above the cycle-by-cycle detail.
