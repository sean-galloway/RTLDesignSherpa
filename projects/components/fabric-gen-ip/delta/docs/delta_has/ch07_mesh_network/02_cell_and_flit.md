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

# Cell and Flit

## Cell Ports

> **PLANNED** — The mesh cell RTL (`delta_mesh_cell`) is not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Each cell has seven AXI4-Stream interfaces:

- **6 neighbor ports** — +X, −X, +Y, −Y, +Z, −Z. Wrap links for any dimension are parameterizable with `--torus=x,y,z`.
- **1 local port** — host-facing. Boundary cells expose this port for rapids DMA attachment; interior cells connect to local compute (SERV, CGRA, ocelus) outside delta's scope.

All ports carry `TDATA`, `TVALID`, `TREADY`, and `TLAST`. The head beat also carries the packet header in `TUSER`. Optional AMBA 5 sidebands (`TWAKEUP`, `TDATACHK` and the chapter 5 check signals) carry over from flat mode unchanged when `--amba5` is enabled.

## Clock and Reset

The mesh cell uses a single clock (`aclk`) and the active-low asynchronous reset (`aresetn`) common to the rest of delta. This is a deliberate simplification *against* the GALS direction common in the NoC literature. The trade: timing closure and generator predictability win over per-link clock flexibility. If a future system needs independent clock domains, that becomes a boundary problem solved outside the cell.

## Flit Format

A flit is one `DATA_WIDTH` beat. A packet is a head flit, zero or more body flits, and a `TLAST` tail beat. The head flit carries the header in `TUSER`; body and tail flits carry only payload and `TLAST`.

### Head-Flit Header Fields

| Field | Width | Purpose |
|-------|-------|---------|
| dest coord | 3×COORD_W | X, Y, Z destination. COORD_W is sized by the fabric dimensions. |
| src coord | 3×COORD_W | X, Y, Z source, used for responses and counters. |
| QoS class | 2 | 0 = config, 1 = latency, 2 = bulk. |
| VC | 1 | Assigned at injection per §6. |
| multicast | 1 | Set for multicast packets; group/mask reference is mode-specific. |
| misroute budget | 3 | Decremented on each non-minimal hop; packet dropped and counted at 0. |
| source-route ptr | 4 | Indexes an inline port list when source-route mode is active. |
| packet ID | 4 | Tolerates reordering at endpoints under multi-VC or adaptive routing. |

: Head-flit header fields carried in `TUSER` on the head beat.

Payload streams pass transparently through the cell once the head beat has supplied the route. This is the same pass-through principle used by flat mode's `TDEST` handling, only the routing information now lives in `TUSER` rather than `TDEST`.
