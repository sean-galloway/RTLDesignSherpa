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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to tile](../README.md)**

# Tile — Compute Engine Tile Subsystem Specification

**Version:** 1.1 (re-homed to compute-eng-ip 2026-10-15; v1.0 owner-defined 2026-10-15)
**Status:** Canonical microarchitecture definition for the compute-engine
tile. **delta is the node** (`delta_mesh_cell`) — nodes collectively form
the network; this document defines the tile IP that instantiates 16 of
them. Where this document and `delta_has/ch07_mesh_network/01_hierarchy.md`
disagree, this document wins — the hierarchy chapter predates the
2026-10-15 owner decisions (tetrad/tile naming, real wrapper modules,
MonBus aggregation, this re-home). The working design record with full
citations is
[`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`](../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md)
(§2 in particular); this spec is its distilled, decision-frozen form.

---

## 1. Scope

The **tile** is the delta mesh's subsystem unit: 16 cells arranged as
2×2×1 **tetrads** of 2×2×1 cells, fully connected at both scales, with
per-level MonBus observation aggregation and a single external attach
point for rapids. This document defines the tile's hierarchy, modules,
connectivity, observation architecture, interfaces, and mode set.

Out of scope: cell-internal microarchitecture (buffering, allocators,
VCs — design spec §3 and ch07 §§4–6), flit format (§4), the flat
crossbar modes of the delta generator's other configurations, and the
fabric-level Z stacking above one tile.

## 2. Hierarchy

| Level | Composition | RTL | Purpose |
|---|---|---|---|
| **Cell (node)** | 1 | `delta_mesh_cell` — owned by [`fabric-gen-ip/delta`](../../../fabric-gen-ip/delta) | the one module with datapath: routing tables, VCs, allocators |
| **Tetrad** | 2×2×1 cells (4) | `tetrad` (this IP) | datapath grouping (K4) + first MonBus aggregation |
| **Tile** | 2×2×1 tetrads = 4×4×1 cells (16) | `tile_top` (this IP) | the subsystem: full K4 at tetrad scale, tile-top MonBus, rapids attach |
| **Fabric** | 4×4×K tiles | generated top | planar recursion; Z lives between tile layers |

Owner-named 2026-10-15: "tetrad" (was "tile") and "tile" (was
"confluence").

## 3. Connectivity

Connectivity is the **same K4 clique at both scales** — the owner's
figure [`assets/3d-mesh-tile.drawio`](assets/3d-mesh-tile.drawio) draws
it: four fully meshed cells inside the tetrad, four fully meshed
tetrads inside the tile.

- **Cell ports**: 6 neighbors (±X, ±Y, ±Z) + 1 local (host/rapids-facing)
  + P_DIA + P_DIA2 + 1 MonBus observer out.
- **Intra-tetrad K4**: the 4 perimeter edges ride ordinary ±X/±Y links;
  both diagonals ride **P_DIA**, one link per cell to the diagonally
  opposite cell of its tetrad.
- **Intra-tile K4**: the 4 tetrads of a tile are themselves fully
  connected. Edge-adjacent tetrads share ±X/±Y boundaries; diagonal
  tetrad pairs ride **P_DIA2**, joining the diagonally adjacent corner
  cells (e.g. (1,1,0)↔(2,2,0), (1,2,0)↔(2,1,0) per tile). Out-of-grid
  mates tie P_DIA2 off — provably never selected.
- **One conceptual diagonal axis**: P_DIA and P_DIA2 are two instances
  of a single diagonal axis realized at tetrad and tile scale. A cell
  has 4 axes in-plane-plus-diagonal plus Z: 8 directional links + local
  = 9 ports.
- **Z**: entirely inter-tile; tetrads are planar (X/Y only).

## 4. Modules

- `delta_mesh_cell` — the node, owned and emitted by delta (the
  fabric-gen-ip component). The only datapath module: routing tables, VCs,
  allocators. The network is the collective of instantiated nodes; this
  IP is not it.
- `tetrad` (`rtl/tetrad.sv`, this IP) — instantiates 4 delta nodes; wires
  the K4 connectivity of §3; merges the 4 node MonBus streams into one
  tetrad MonBus (§5). No datapath function.
- `tile_top` (`rtl/tile_top.sv`, this IP — house `<ip>_top` naming) —
  instantiates 4 tetrads; merges the 4 tetrad MonBus streams into the
  single tile-top MonBus (§5); exposes boundary nodes' local ports for
  rapids attachment. No datapath function. (Working names during the
  delta-side design phase were `delta_mesh_tetrad` / `delta_mesh_tile`;
  retired with this re-home.)

## 5. Observation (MonBus aggregation)

Owner decision 2026-10-15. Every cell emits exactly **one** MonBus
stream; observation aggregates 4:1 per level:

```
cell  ┐
cell  ├─ tetrad (this IP) ────── 1 tetrad MonBus
cell  ┤
cell  ┘
tetrad ┐
tetrad ├─ tile_top (this IP) ─── 1 tile-top MonBus  ← host/board sees this
tetrad ┤
tetrad ┘
```

Aggregation uses the house AXIL MonBus group family
(`rtl/amba/ocelus/monbus_group_core` + `monbus_*_group` wrappers, AXIL
host-read flavor) — the same observation path as the amber tally
harness (merge → group → AXIL read-out), so standard host tooling
(`monbus_tally_axil`, regmaps) attaches at the tile top unchanged. Exact
leaf selection inside the wrappers is implementation detail; the
architectural contract is **one MonBus per level boundary, 4:1 merge per
level**.

This hierarchy is also the verification anchor: per-tetrad and per-tile
observability come for free, and the tile-top stream is the single
sim-vs-silicon equivalence point (the same role the UART-equivalence
cell plays for the amber harness).

## 6. Interfaces

- **Cell/tetrad/tile datapath ports**: AXI4-Stream
  (`TDATA/TVALID/TREADY/TLAST` + header sideband in `TUSER`), with the
  optional AMBA 5 TSTRB/TWAKEUP/TPARITY richness carrying over from
  flat mode unchanged.
- **CXS migration (owner plan, 2026-10-15)**: rapids gains a CXS
  interface variant — a separate model, `rapids_cxs`, replacing its AXIS
  interfaces — and delta's network ports move to CXS to match. Sequencing:
  rapids_cxs first (a working AXIS model exists to diff against), then
  delta. Header/sideband content is unchanged by the migration. Until
  both sides land, all delta ports stay AXI4-Stream.
- **MonBus ports**: per §5; cell-level streams are internal to the
  tetrad, tetrad-level streams internal to the tile.

## 7. Modes

The mode catalog (design spec §5.4) is unchanged by this spec; the
tile-relevant rows:

| Mode | Pattern | Tile relevance |
|---|---|---|
| 1 Mesh (default) | DOR over RAM tables | baseline; inter-tile dsts DOR |
| 9 Tetrad all-to-all (K4) | perimeter ±X/±Y + P_DIA diagonals | intra-tetrad 1 hop to any cell; inter-tetrad DOR |
| 10 Tile all-to-all (K4 of tetrads) | shared boundaries + P_DIA2 diagonals | any cell of any tetrad of the tile in 1–2 hops (diagonal-of-tetrad pairs 1 hop); inter-tile DOR |

Modes are table images, not new hardware — except that modes 9–10 make
P_DIA/P_DIA2 (emitted in every build) their enabling hardware.

## 8. Rapids attachment

Hive configuration (owner, 2026-10-15): one or more tiles — only one
for now — connect to a **single** rapids DMA at boundary cells' local
ports; any boundary cell can be the attachment. With the CXS migration
(§6), this link is the first CXS hop.

## 9. Clocking and reset

Single clock domain, active-low async `aresetn` (house `ALWAYS_FF_RST`)
throughout the tile — a deliberate simplification against the NoC
literature's GALS assumption; timing closure and generator
predictability win over clock flexibility (design spec §2 close).

## 10. Open items

- `tetrad` / `tile_top` RTL (this IP) — pending the in-flight node RTL
  (delta modes 9–10 diagonal ports) landing first.
- CXS leaf selection for both rapids_cxs and delta ports (§6).
- MonBus wrapper leaf selection inside tetrad/tile (§5).
- Config/address region naming per level — design spec §5, ch07 §3;
  not yet restated here.

## References

- [`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`](../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md) — working design record (§2 architecture, §5.4 mode catalog).
- [`3d-mesh-tile.drawio`](3d-mesh-tile.drawio) — owner's K4-at-both-scales figure.
- [`delta_has/ch07_mesh_network/`](../../../fabric-gen-ip/delta/docs/delta_has/ch07_mesh_network/) — the node/network chapters in delta's HAS (cell/flit, routing, flow control, QoS, multicast, modes, observability, verification).
- [`../noc-ip/delta_spec`](../../noc-ip/delta_spec) — the aspirational NoC draft this subsystem grew out of.

---

**Last Updated:** 2026-10-15
**Maintained By:** RTL Design Sherpa Project
