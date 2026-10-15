# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Offline unit tests for the delta mesh Task 8 multicast spanning-tree
# helper (bin/delta_mesh/tables.py::mcast_tree).  Pure Python, run with
# repo pytest.

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from delta_mesh.config import DeltaMeshConfig
from delta_mesh.tables import (
    P_LOCAL,
    P_X_NEG,
    P_X_POS,
    P_Y_NEG,
    P_Y_POS,
    P_Z_NEG,
    P_Z_POS,
    PORT_TO_MASK,
    mcast_tree,
)

CFG_2X2X1 = DeltaMeshConfig(cells_x=2, cells_y=2, cells_z=1)
CFG_3X3X1 = DeltaMeshConfig(cells_x=3, cells_y=3, cells_z=1)
CFG_4X4X1 = DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)
CFG_2X3X4 = DeltaMeshConfig(cells_x=2, cells_y=3, cells_z=4)

PORT_OPPOSITE = {
    P_X_NEG: P_X_POS,
    P_X_POS: P_X_NEG,
    P_Y_NEG: P_Y_POS,
    P_Y_POS: P_Y_NEG,
    P_Z_NEG: P_Z_POS,
    P_Z_POS: P_Z_NEG,
}


def _grid_cells(cfg):
    return [(x, y, z)
            for z in range(cfg.cells_z)
            for y in range(cfg.cells_y)
            for x in range(cfg.cells_x)]


def _step(pos, port):
    x, y, z = pos
    if port == P_X_NEG:
        return (x - 1, y, z)
    if port == P_X_POS:
        return (x + 1, y, z)
    if port == P_Y_NEG:
        return (x, y - 1, z)
    if port == P_Y_POS:
        return (x, y + 1, z)
    if port == P_Z_NEG:
        return (x, y, z - 1)
    if port == P_Z_POS:
        return (x, y, z + 1)
    return pos


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_covers_every_cell_once(cfg):
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        assert set(tree.keys()) == set(_grid_cells(cfg))


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_source_has_no_parent_and_local_child(cfg):
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        parent, child_mask = tree[src]
        assert parent is None
        assert child_mask & PORT_TO_MASK[P_LOCAL]


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_parent_child_consistency(cfg):
    """Every non-source cell's parent port points back to a cell that lists
    this cell in its child mask."""
    cells = set(_grid_cells(cfg))
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        for cell, (parent_port, child_mask) in tree.items():
            if cell == src:
                continue
            assert parent_port is not None
            parent = _step(cell, parent_port)
            assert parent in cells
            assert tree[parent][1] & PORT_TO_MASK[PORT_OPPOSITE[parent_port]]


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_is_acyclic(cfg):
    """Walk parent links from every cell back to src; every path must end at
    the source without revisiting a cell."""
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        for start in _grid_cells(cfg):
            seen = set()
            cell = start
            while cell != src:
                assert cell not in seen, "cycle in multicast tree"
                seen.add(cell)
                parent_port, _ = tree[cell]
                assert parent_port is not None
                cell = _step(cell, parent_port)


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_child_mask_includes_local(cfg):
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        for cell in _grid_cells(cfg):
            _, child_mask = tree[cell]
            assert child_mask & PORT_TO_MASK[P_LOCAL]


@pytest.mark.parametrize("cfg", [CFG_2X2X1, CFG_3X3X1, CFG_4X4X1, CFG_2X3X4])
def test_mcast_tree_child_mask_only_valid_ports(cfg):
    valid_mask = sum(1 << p for p in range(9))
    for src in _grid_cells(cfg):
        tree = mcast_tree(src, cfg)
        for cell in _grid_cells(cfg):
            _, child_mask = tree[cell]
            assert child_mask & ~valid_mask == 0


def test_mcast_tree_2x2x1_source_corner_structure():
    src = (0, 0, 0)
    tree = mcast_tree(src, CFG_2X2X1)
    # Source fans to +X, +Y, and local.  (0,1,0) is on the X=0 edge so it
    # also replicates +X; the other two non-source cells are leaves.
    assert tree[(0, 0, 0)][1] & (PORT_TO_MASK[P_X_POS] | PORT_TO_MASK[P_Y_POS])
    assert tree[(1, 0, 0)] == (P_X_NEG, PORT_TO_MASK[P_LOCAL])
    assert tree[(0, 1, 0)] == (P_Y_NEG,
                               PORT_TO_MASK[P_X_POS] | PORT_TO_MASK[P_LOCAL])
    assert tree[(1, 1, 0)] == (P_X_NEG, PORT_TO_MASK[P_LOCAL])
