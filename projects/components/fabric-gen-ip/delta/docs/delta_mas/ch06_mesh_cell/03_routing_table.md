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

# Routing Table

> **PLANNED:** This chapter describes the planned `delta_mesh_cell` microarchitecture per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). No RTL implementation exists yet.

## RAM Table Structure

Each cell contains a RAM lookup table. The key is the packet's destination coordinate plus its QoS class; the entry gives the output port mask and the VC assignment. The mask supports multicast on VC0 and unicast on either VC.

| Field | Width | Purpose |
|---|---|---|
| Key: `dest_x`, `dest_y`, `dest_z` | `3 × COORD_W` | Destination coordinate, sized by fabric dimensions |
| Key: QoS class | 2 | 0=config, 1=latency, 2=bulk |
| Entry: output port mask | 7 bits (one per output port) | Next-hop direction(s); one-hot for unicast, multi-hot for multicast |
| Entry: VC | 1 | 0 or 1, assigned by the table |

: Routing table entry layout

## Reset Image

At reset the table is loaded with a dimension-ordered route toward the rapids boundary. The route is minimal, connected, and acyclic by construction, which satisfies Duato's sufficient condition for the escape VC [D5][P11]. This bootstrap path is the only way to load custom tables in-band; every other mode image is loaded later through the config port.

## In-Band Load and Readback

Configuration packets target a reserved address. The ejection block intercepts them instead of delivering them to the local port. The command format is `{op, entry_index, entry_data}`; reads return response packets to the source for load-verify. Config traffic rides QoS class 0 on the reset-default route. A boundary cell or rapids DMA injects the stream.

> **Design note:** The generator can also emit preloaded ROM images for the standard fabric modes. In that build the cell still uses the same table RAMs; the image is just initialized differently.

## VC0 Acyclicity Check

VC0 is the escape channel. Its table entries must form a connected, acyclic subrelation in the extended channel-dependency graph; that is Duato's sufficient condition for deadlock freedom [D2][D7]. This check is performed *offline* on a table image before it is loaded, not by the hardware at runtime. The verification target is the table-load flow: any image that fails the acyclicity test is rejected before it reaches the fabric.

## Torus Wrap and the Dateline Rule

When a dimension is configured as a torus (`--torus=x,y,z`), the wrap link creates a cycle that plain dimension-order routing cannot break. The fix is a dateline: one designated wrap channel per dimension participates in VC0 only as part of the escape subrelation; ordinary wrap traffic uses VC1 and may consume a misroute budget [P11]. The hardware enforces the rule by gating wrap-link VC0 grants with the dateline condition.

## Standard Fabric Modes

Alongside custom per-cell tables, the generator defines eight standard modes switched by a broadcast mode-switch message. Each cell holds generator-emitted images; the switch applies only after a fabric-wide ack barrier returns through the config read-response path.

| Mode | Pattern | Routing source |
|---|---|---|
| 1 | Mesh (default) | RAM tables, reset DOR image |
| 2 | Systolic-1D | Fixed source-route paths |
| 3 | Wavefront-2D | Per-diagonal static tables |
| 4 | Stencil-3D | Nearest-neighbor tables + torus wrap |
| 5 | Broadcast | Multicast VC0 port masks to all |
| 6 | Convergecast/reduce | Reverse-broadcast tables |
| 7 | All-to-all/transpose | Per-stage table images |
| 8 | Pipeline + rapids-stream | Fixed chain + boundary tables |

: Standard fabric mode catalog

## References

- Duato, Yalamanchili, Ni, *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003 — deterministic routing, Duato's protocol, and VC0 acyclicity [D2][D5][D7].
- Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004 — table-based routing, deadlock avoidance, and the dateline technique [P8][P11][P12].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — in-band control-program precedent [Q6].
