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

# Flow Control and Deadlock

## Credit-Based Flow Control

> **PLANNED** — The mesh cell RTL is not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Delta's mesh uses credit-based flow control per VC. Each output port tracks the number of free buffer slots in the downstream neighbor. A flit leaves only when a credit is available, and a credit returns only after the downstream cell has consumed the flit. Credit-counter depth is sized to cover round-trip latency; undersizing drops the channel duty factor below one.

## Two Virtual Channels

The mesh has 2 VCs:

- **VC0** — the escape channel. It carries only reset-default and turn-model-conforming routes that form a connected, acyclic subrelation.
- **VC1** — the adaptive channel. It may carry minimal routes or routes with a bounded misroute budget.

This is Duato's Protocol: one adaptive channel set plus one deterministic escape set. The escape set breaks any cycle that could form in the adaptive set.

## VC Transition Rules

A packet may move from VC1 to VC0 at any hop. VC0 to VC1 is forbidden. Because every VC1 packet can always drain into VC0, cycles in the adaptive channel cannot close into a deadlock.

## Torus Wrap and the Dateline Rule

Per-dimension torus wrap (`--torus=x,y,z`) restores edge symmetry and halves diameter, but a wrap channel creates a cycle that plain dimension-ordered routing cannot break. For each wrapped dimension, one designated wrap channel participates in VC0 only through the escape subrelation. Other wrap traffic uses VC1 with the misroute budget. This dateline rule keeps the 2-VC budget sufficient even with wrap links.

## Livelock

Non-minimal routing is the only source of livelock. The misroute budget in the head flit bounds it: every non-minimal hop decrements the budget, and when it reaches zero the packet is dropped and counted. Minimal routing is the normal case; the budget exists to bound VC1 alternates.
