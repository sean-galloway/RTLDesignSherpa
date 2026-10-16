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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Validation Rules

The generator validates CLI arguments through `argparse` and additional checks inside `main()`.

## CLI-level checks

| Rule | Behavior |
|------|----------|
| `--topology` must be `flat`, `tree`, `both`, or `mesh`. | Enforced by `choices`. |
| `--masters` and `--slaves` are required integers. | Enforced by `required=True`. |
| `--strb-width` must be >= 0. | Custom check; negative values raise an error. |
| `--amba5` requires `--data-width % 8 == 0`. | Custom check; `TDATACHK` is one bit per `TDATA` byte (IHI 0051B Table 5-1). |
| `--cells-x`, `--cells-y`, `--cells-z` must be >= 1 | Mesh-only; enforced in `validate_mesh`. |
| A torus wrap on a dimension requires >= 2 cells in that dimension | Mesh-only; enforced in `validate_mesh`. |
| `--fifo-impl` must be `reg` or `sram` | Mesh-only; enforced in `validate_mesh`. |
| `--user-width` must be >= the mesh header width | Mesh-only; enforced in `validate_mesh`; header width is `6 * COORD_W + 32`. |

: CLI-Level Validation Rules

## Internal checks

| Rule | Rationale |
|------|-----------|
| `num_masters >= 1` and `num_slaves >= 1` | A crossbar needs at least one master and one slave. |
| `data_width > 0` | Required for meaningful `TDATA`. |
| `user_width >= 1` | `TUSER` is always at least one bit. |
| `dest_width = ceil(log2(num_slaves))` | `TDEST` must encode all slave indices. |
| `id_width = ceil(log2(num_masters))` | `TID` must encode all master indices. |

: Internal Validation Rules

The generator does **not** currently validate that `strb_width` matches `data_width/8`; callers must ensure the width is consistent with their byte-qualifier policy.

## Mesh topology validation

> **IMPLEMENTED** These rules apply to the mesh CLI defined in the [2026-10-13 mesh design spec](../../../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md). They are enforced by `validate_mesh` in `bin/delta_mesh/config.py`.

| Rule | Rationale |
|------|-----------|
| `cells-x >= 1`, `cells-y >= 1`, `cells-z >= 1` | A fabric needs at least one cell in each dimension. `cells-z` is the K-stack height; `K = 1` is a single-layer mesh. |
| `torus` wrap in a dimension requires `>= 2` cells in that dimension | A one-cell dimension cannot form a ring. |
| `data-width > 0` | Same baseline requirement as flat mode. |
| `user-width` must fit the mesh flit header | The head-flit `TUSER` carries dest/src coordinates, QoS class, VC, multicast flag, misroute budget, source-route pointer, and packet ID. |
| `--fifo-impl` must be `reg` or `sram` | Selects the input buffer implementation style. The `sram` choice is accepted by validation but not yet wired to the cell (issue #118). |
| `--amba5` still requires whole-byte `data-width` | AMBA 5 sidebands carry over unchanged from flat mode. |

: Mesh Topology Validation Rules

### Header width budget

The implemented flit header uses these fields on the head beat:

| Field | Width |
|---|---|
| `dst_x`, `dst_y`, `dst_z` | `3 * COORD_W` |
| `src_x`, `src_y`, `src_z` | `3 * COORD_W` |
| QoS class | 2 |
| multicast | 1 |
| VC | 1 |
| misroute budget | 4 |
| source-route pointer | 8 |
| packet ID | 16 |

: Implemented Head-Flit Header Fields

`COORD_W = max(1, ceil(log2(max(cells-x, cells-y, cells-z))))`. The total header width is `6 * COORD_W + 32`. Validation rejects a `--user-width` smaller than this value. The two VCs and three QoS classes are fixed; the header must encode VC (1 bit) and QoS (2 bits) without truncation.
