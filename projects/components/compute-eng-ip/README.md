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

# Compute Engine IP

Compute systems: the engines that compute and the control planes that
orchestrate them. Family revived 2026-10-13 (created 2026-09-29 in the
component-tree regrouping) when **cell** joined and **hive-serv** returned
from its 2026-10-10..2026-10-13 stay in riscv-ip — HIVE uses RISC-V cores but
is a *system*, not a core, and it is the control half of this family.

| Directory | What | Status |
|---|---|---|
| [`hive-serv/`](hive-serv/) | Hierarchical control/monitoring system: 1 VexRiscv master (HIVE-C) + 16 SERV per-tile monitors; inband descriptor injection into delta; coordinates RAPIDS and cell | HAS/MAS v0.2; Phase 1 RTL in progress (vault hive-serv TASK-000) |
| [`cell/`](cell/) | Compute engine: `cgra` reconfigurable array (TBD) + `axon` SERV/delta result router | Scaffold (README + axon spec sketch) |
| [`tile/`](tile/) | Compute-engine tile: 16 cells as 2×2×1 tetrads (K4 at both scales) + per-level MonBus aggregation + rapids attach; **delta is the node**, instantiated 16× | [Tile Spec](tile/docs/TILE_SPEC.md) v1.1 (owner-defined 2026-10-15) |

The trio forms the compute system: **cell** is the data plane (the CGRA),
**hive-serv** is the control plane, **tile** is the subsystem that assembles
cells onto delta nodes at scale, and **delta** is the fabric between them —
nodes collectively form the network, tile is the IP that instantiates one
network segment. **RAPIDS** moves bulk data. See the [hive-serv HAS](hive-serv/docs/hive_has/hive_has_index.md),
the [cell README](cell/README.md), and the [tile spec](tile/docs/TILE_SPEC.md).
