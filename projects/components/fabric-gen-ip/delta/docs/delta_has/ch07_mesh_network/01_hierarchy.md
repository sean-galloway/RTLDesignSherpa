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

# Mesh Hierarchy

> **SUPERSEDED in part (2026-10-15)** — the owner re-defined the hierarchy
> and made the wrappers real: tetrad (2×2×1 cells, K4) and tile (2×2×1
> tetrads, K4) are now RTL modules with MonBus aggregation, not naming-only
> groupings. The tile is a compute-engine IP
> ([`compute-eng-ip/tile`](../../../../compute-eng-ip/tile/README.md)) —
> delta is just the node. The canonical definition is
> [`TILE_SPEC.md`](../../../../compute-eng-ip/tile/docs/TILE_SPEC.md);
> this chapter's "no wrapper RTL" statements and old names ("confluence")
> hold only as pre-2026-10-15 history.

## Placement Levels

> **PLANNED** — Mesh mode is a planned generator option. The only RTL delta is expected to emit is `delta_mesh_cell`; the hierarchy below is placement and naming, not wrapper RTL. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Delta's mesh groups identical cells into four named levels so that routing tables, config images, and rapids attachment points can be named without forcing a separate module boundary at every level.

### Figure 7.1: Delta Mesh Placement Hierarchy

![Delta Mesh Hierarchy](../assets/graphviz/delta_mesh_hierarchy.png)


## Cell

A cell is `delta_mesh_cell`, the one module the generator emits for mesh mode. It has six neighbor ports (±X, ±Y, ±Z) and one local port. A cell forwards flits by looking up a destination coordinate in a RAM routing table and applying credit-based flow control per VC.

## Tile

A tile is `2×2×1` cells — four cells arranged in X and Y, one deep in Z. Tile is a routing and config grouping: cells inside one tile are close enough that their tables can share a config burst and that the generator can number their coordinates contiguously. There is no tile wrapper; an intra-tile hop is an ordinary ±X/±Y hop.

## Confluence

A confluence is `4×4×1` cells — sixteen cells, or four tiles. Rapids DMA attaches at the local ports of boundary cells, so a confluence is the natural unit that exposes enough boundary local ports to feed the fabric. The name was chosen by the owner on 2026-10-13. Like the tile, a confluence has no wrapper RTL; an intra-confluence hop is an ordinary hop.

## Fabric

A fabric is `4×4×K` confluences stacked in Z. The recursion is planar: the Z dimension lives between confluence layers, not inside a confluence. The generator produces a fabric top that instantiates the `cells-x × cells-y × cells-z` grid of `delta_mesh_cell`, parameterizes coordinate widths and per-dimension wrap links, and exposes boundary local ports as rapids attachment points.

## Why This Grouping

The grouping borrows the superswitch idea seen in ECLIPSE: clustering cells so a message can reach any cell in a local group cheaply. Delta keeps the naming and table-bounding benefit but does not promise single-cycle traversal across a tile or confluence. That trade keeps the cell simple — one module, one set of tables, one set of allocators — while still letting software reason about locality.
