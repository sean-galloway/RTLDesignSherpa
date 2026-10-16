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

# Multicast

## VC0 Only

> **IMPLEMENTED** — multicast is built into `delta_mesh_cell`. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Multicast packets use VC0 only. Restricting multicast to the escape channel keeps the multicast paths inside the same connected, acyclic subrelation used by unicast traffic, so multicast adds no new channel dependencies beyond the unicast deadlock proof.

## BRCP-Conformed Paths

Multicast routes are table entries that produce an output port mask instead of a single output. The set of paths a multicast can take is constrained to conform to the base unicast routing (BRCP — base routing conformed path-based multicast). A cell replicates a packet only onto ports that the unicast tables would also use.

## Source-Side Replication

When a packet must fan out, the branching cell enqueues one copy per destination port. This source-side replication discipline avoids broadcasting every packet everywhere and filtering later. Incremental allocation serves whichever masked outputs are free each cycle and releases the input only after all destinations have been served.

## Multiple Delivery VCs

Multicast reception can deadlock even when the forward paths are correct, because multiple deliveries can compete for the same buffer. Each cell therefore provides multiple delivery VCs for multicast reception.

## No Responses

Multicast connections do not carry responses. Responses create merge volume and ordering problems that are better handled by unicast many-to-one traffic. If software needs an acknowledgment, it sends a separate unicast gather after the multicast completes.
