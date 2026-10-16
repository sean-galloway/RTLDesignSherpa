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

**[← Back to compute-eng-ip](../README.md)**

# tile — Compute Engine Tile

The compute-engine tile: 16 compute cells arranged as 2×2×1 **tetrads**
of 2×2×1 cells, fully connected (K4) at both scales, with per-level
MonBus observation aggregation and a single rapids attachment. The tile
is the subsystem IP; **delta is just the node** — `delta_mesh_cell`,
instantiated 16 times here and collectively forming the network.

Owner-defined 2026-10-15 (re-homed from fabric-gen-ip/delta the same
day: the tile is a compute-engine IP, not a delta side-note).

## Status

Spec-only; no RTL yet. The node RTL (`delta_mesh_cell`,
modes 9–10 diagonal ports) is landing in
[`../../fabric-gen-ip/delta`](../../fabric-gen-ip/delta) first; the
`tetrad` and `tile_top` wrappers follow here.

## Documents

- [Tile Spec — subsystem uarch](docs/TILE_SPEC.md) — the canonical
  definition: hierarchy, K4 connectivity, MonBus aggregation, interfaces
  (AXI4-Stream → CXS plan), modes, rapids attach, open items.
- Owner's connectivity figure: [docs/assets/3d-mesh-tile.drawio](docs/assets/3d-mesh-tile.drawio).

## Layout (when RTL lands)

`rtl/` — `tetrad.sv` (4 cells + tetrad MonBus merge), `tile_top.sv`
(4 tetrads + tile-top MonBus merge + rapids attach). `dv/` on the
repo-wide make/tests.mk rails. The node stays in delta.
