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

# Multicast Path

> **PLANNED:** This chapter describes the planned `delta_mesh_cell` microarchitecture per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). No RTL implementation exists yet.

Multicast is restricted to VC0. The routing table supplies a multi-hot output port mask, and the cell builds a BRCP-conformed path: every branch follows the base unicast routing function so multicast adds no new channel dependencies beyond the unicast proof [D9].

## Source-Side Replication

When a head flit reaches a cell whose table entry says "send out ports A and B," the cell creates one copy per destination output. This is source-side replication at the branching cell, not a broadcast-and-filter scheme. It costs buffer slots at the branch but avoids wasting downstream bandwidth on flits that would be dropped [Q7].

## Delivery-VC Assignment

Multicast *reception* uses multiple delivery VCs at each destination cell. The literature is clear: even with correct routing, a single delivery channel for multicast creates a deadlock that the unicast VC analysis does not cover [D9: §5.5.3]. The cell assigns a distinct delivery VC per multicast group or per source, depending on the build-time parameterization.

## The No-Responses Rule

Multicast connections do not carry responses. If every destination tried to acknowledge delivery, the acknowledgments would converge on the source and create a many-to-one merge problem; worse, a response could wait for a multicast channel that is held by another response, closing a dependency cycle [N3]. Many-to-one communication uses unicast, not multicast.

| Rule | Rationale |
|---|---|
| VC0 only | Keeps multicast on the escape channel; avoids adaptive-route cycles |
| BRCP paths | Adds no channel dependencies beyond unicast proof |
| Source-side replication | No wasted downstream bandwidth |
| Multiple delivery VCs | Breaks delivery-channel deadlock |
| No responses | Avoids response merge and cyclic waits |

: Multicast discipline

## Failure Mode: Tree-Based Multicast in Wormhole Networks

A naive tree multicast that forks at every hop in a wormhole network deadlocks readily because forked branches can hold buffer resources in a cycle [D9: §5.5.2]. The BRCP + source replication + delivery-VC combination is the book-recommended discipline for this reason.

## References

- Duato, Yalamanchili, Ni, *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003 — hardware multicast deadlock, BRCP, and delivery-channel VCs [D9].
- Jantsch & Tenhunen (eds.), *Networks on Chip*, Kluwer, 2003 — iEthereal connection model: multicast with no responses [N3].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — source-side replication precedent [Q7].
