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

# Systolic Support and Fabric Modes

## Torus Wrap Links

> **PLANNED** — The mesh cell RTL is not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Each dimension can be wrapped independently with `--torus=x,y,z`. Periodic boundaries restore edge symmetry and halve diameter. The wrap links are folded so wire length doubles rather than growing with the dimension size. Deadlock freedom on wraps is handled by the dateline rule in §4.

## Route Lookahead

The cell computes the next hop's output port one hop ahead of the flit's arrival. In steady state this collapses per-hop latency toward one cycle, which is the target for systolic repeat-cycle timing.

## Source-Route Mode

For static systolic schedules, the injection shim can place an inline port list in the head-flit header. Intermediate cells forward without a table lookup, giving fixed-latency, table-free paths. Node-table routing remains the default for dynamic traffic.

## Standard Fabric Modes

A broadcast mode-switch (§3) selects one of 8 standard fabric modes. Every cell stores generator-emitted images for these modes. Mode 0 is custom (per-cell unicast tables).

### Standard Fabric Modes

| Mode | Name | Pattern |
|------|------|---------|
| 1 | Mesh (default) | Generic packet switching using RAM tables; reset default is dimension-ordered routing. |
| 2 | Systolic-1D | Linear nearest-neighbor chains, row or column selected, optional torus ring; fixed source-route paths. |
| 3 | Wavefront-2D | 2-D diagonal ripple with skewed E/W and N/S streams; per-diagonal static tables or source routes. |
| 4 | Stencil-3D | 3-D halo/ghost-zone exchange with periodic boundaries; nearest-neighbor tables plus torus wrap on all dims. |
| 5 | Broadcast | One-to-all; multicast on VC0 with port masks to every cell. |
| 6 | Convergecast/reduce | All-to-one reduction tree; reverse-broadcast tables plus ocelus counter reduction. |
| 7 | All-to-all/transpose | Permutations such as transpose and shuffle/butterfly stages; per-stage table images. |
| 8 | Pipeline + rapids-stream | Boustrophedon serpentine chain; boundary cells stream to and from rapids DMA. |

: Standard fabric modes selected by broadcast mode-switch.

Mode images are data, not new hardware. Adding a mode means adding an image and a verification suite.
