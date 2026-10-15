# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Offline unit tests for the delta mesh routing-table image builders
# (bin/delta_mesh/tables.py): default_dor_image, check_acyclic, entry
# packing, and the table key layout. No simulator -- pure Python, run with
# the repo pytest.

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from delta_mesh.config import DeltaMeshConfig
from delta_mesh.tables import (
    P_DIA,
    P_LOCAL,
    P_X_NEG,
    P_X_POS,
    P_Y_NEG,
    P_Y_POS,
    P_Z_NEG,
    P_Z_POS,
    PORT_IDS,
    PORT_TO_MASK,
    TableEntry,
    check_acyclic,
    default_dor_image,
    dor_port,
    pack_entry,
    table_index,
    unpack_entry,
)

CFG_4X4X1 = DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)
CFG_2X2X1 = DeltaMeshConfig(cells_x=2, cells_y=2, cells_z=1)
CFG_3X3X1 = DeltaMeshConfig(cells_x=3, cells_y=3, cells_z=1)
CFG_1X1X1 = DeltaMeshConfig(cells_x=1, cells_y=1, cells_z=1)
COORD_W_4X4 = 2


def grid_coords(cfg):
    return [(x, y, z)
            for z in range(cfg.cells_z)
            for y in range(cfg.cells_y)
            for x in range(cfg.cells_x)]


# ------------------------------------------------------------------
# Port ids / entry packing
# ------------------------------------------------------------------

def test_port_ids_pinned():
    # 8 ports (Task 6b): P_DIA takes index 6, P_LOCAL MOVES to 7.
    assert PORT_IDS == (
        ("P_X_NEG", 0), ("P_X_POS", 1),
        ("P_Y_NEG", 2), ("P_Y_POS", 3),
        ("P_Z_NEG", 4), ("P_Z_POS", 5),
        ("P_DIA", 6), ("P_LOCAL", 7),
    )
    assert (P_X_NEG, P_X_POS, P_Y_NEG, P_Y_POS,
            P_Z_NEG, P_Z_POS, P_DIA, P_LOCAL) == (0, 1, 2, 3, 4, 5, 6, 7)


def test_pack_entry_roundtrip():
    entry = pack_entry(port_mask=0x42, vc=1)
    mask, vc = unpack_entry(entry)
    assert mask == 0x42
    assert vc == 1
    # one-hot mask, vc 0 -> the low 8 bits carry the port bit (the entry
    # mask field widened to 8 with P_DIA at index 6, Task 6b)
    assert pack_entry(1 << P_X_POS, 0) == (1 << P_X_POS)
    assert pack_entry(1 << P_DIA, 0) == (1 << P_DIA)
    assert pack_entry(1 << P_LOCAL, 0) == (1 << P_LOCAL)  # top mask bit


def test_table_index_layout():
    # addr = {qos[1:0], dst_z, dst_y, dst_x} with dst_x in the LSBs, so the
    # dst space occupies the low 3*COORD_W bits (qos region per class).
    assert table_index((1, 0, 0), 0, COORD_W_4X4) == 1
    assert table_index((0, 1, 0), 0, COORD_W_4X4) == (1 << COORD_W_4X4)
    assert table_index((0, 0, 1), 0, COORD_W_4X4) == (1 << 2 * COORD_W_4X4)
    assert table_index((3, 0, 0), 0, COORD_W_4X4) == 3
    # qos sits above the full dst space: the dst space is contiguous
    dst_space = 1 << (3 * COORD_W_4X4)
    assert table_index((0, 0, 0), 1, COORD_W_4X4) == dst_space
    assert table_index((3, 3, 3), 3, COORD_W_4X4) == 3 * dst_space + dst_space - 1


# ------------------------------------------------------------------
# default_dor_image
# ------------------------------------------------------------------

def test_default_dor_image_size_and_key_space():
    image = default_dor_image(CFG_4X4X1)
    # one entry per representable dst coordinate: 2^(3*COORD_W) = 64
    assert len(image) == 64
    assert all(isinstance(e, TableEntry) for e in image)
    assert all(e.qos == 0 for e in image)
    assert all(e.vc == 0 for e in image)


def test_default_dor_image_origin_cell_routes():
    # The image is the canonical cell-at-origin (0,0,0) install: for the
    # origin cell every dst resolves with the same DOR semantics as the
    # pre-Task-5 runtime function (X then Y then Z, negative first toward
    # the coord-0 boundary, all-equal -> P_LOCAL).
    image = {(e.dst_x, e.dst_y, e.dst_z): e for e in default_dor_image(CFG_4X4X1)}
    origin = (0, 0, 0)
    assert image[(3, 0, 0)].port_mask == PORT_TO_MASK[dor_port((3, 0, 0), origin)]
    assert image[(3, 0, 0)].port_mask == 1 << P_X_POS
    assert image[(0, 2, 0)].port_mask == 1 << P_Y_POS
    assert image[(0, 0, 0)].port_mask == 1 << P_LOCAL  # dst == origin cell
    # X dimension decides before Y: dst (0,3,0) from POS (1,1,0) walks -X
    # first even though it is also above in Y (origin image: +Y).
    assert image[(0, 3, 0)].port_mask == 1 << P_Y_POS
    assert dor_port((0, 3, 0), (1, 1, 0)) == P_X_NEG


def test_default_dor_image_out_of_grid_drops():
    # Representable dst keys outside the grid carry an empty mask: the
    # runtime range check drops them before the table is consulted, and a
    # zero mask is the table-level drop encoding regardless.
    image = {(e.dst_x, e.dst_y, e.dst_z): e for e in default_dor_image(CFG_4X4X1)}
    assert image[(3, 3, 3)].port_mask == 0  # z=3 on a Z=1 grid
    assert image[(3, 3, 0)].port_mask != 0  # in-grid corner routes


def test_dor_port_negative_first_toward_zero():
    # "negative first toward 0": any dst below POS on the deciding
    # dimension takes the negative port; the deciding dimension is X,
    # then Y, then Z.
    assert dor_port((0, 1, 0), (1, 1, 0)) == P_X_NEG
    assert dor_port((1, 0, 0), (1, 1, 0)) == P_Y_NEG
    assert dor_port((1, 1, 0), (1, 1, 0)) == P_LOCAL
    assert dor_port((0, 0, 0), (1, 1, 0)) == P_X_NEG  # X first, not Y/Z
    assert dor_port((3, 3, 3), (0, 0, 0)) == P_X_POS


# ------------------------------------------------------------------
# check_acyclic -- positive and negative cases
# ------------------------------------------------------------------

@pytest.mark.parametrize("cfg", [CFG_1X1X1, CFG_2X2X1, CFG_3X3X1, CFG_4X4X1])
def test_check_acyclic_default_images_pass(cfg):
    # Generation calls this on every emitted image; the default DOR image
    # is connected and acyclic by construction (every hop strictly reduces
    # the Manhattan distance).
    check_acyclic(default_dor_image(cfg), cfg)


def _tampered_image(cfg):
    image = default_dor_image(cfg)
    return [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   (1 << P_X_POS) if (e.dst_x, e.dst_y, e.dst_z) == (0, 1, 0)
                   else e.port_mask,
                   e.vc)
        for e in image
    ]


def test_check_acyclic_detects_cycle():
    # dst (0,1,0) from the origin is redirected +X: the walk
    # (0,0,0)->(1,0,0)->DOR(-X)->(0,0,0) never reaches dst and revisits
    # the origin -- a cycle in the VC0 subrelation.
    with pytest.raises(ValueError, match="cycle in VC0 subrelation"):
        check_acyclic(_tampered_image(CFG_2X2X1), CFG_2X2X1)


def test_check_acyclic_detects_unroutable_entry():
    # An in-grid dst whose VC0 entry carries an empty mask (or is missing)
    # breaks connectivity of the subrelation.
    image = [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   0 if (e.dst_x, e.dst_y, e.dst_z) == (1, 0, 0) else e.port_mask,
                   e.vc)
        for e in default_dor_image(CFG_2X2X1)
    ]
    with pytest.raises(ValueError, match="VC0 subrelation"):
        check_acyclic(image, CFG_2X2X1)


def test_check_acyclic_verifies_walk_hop_bound():
    # DOR is minimal: exactly Manhattan(src,dst) hops. A detour that
    # exceeds the bound must be rejected even when it still delivers.
    image = [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   (1 << P_Y_POS) if (e.dst_x, e.dst_y, e.dst_z) == (1, 0, 0)
                   else e.port_mask,
                   e.vc)
        for e in default_dor_image(CFG_4X4X1)
    ]
    # (0,0,0)->(0,1,0)->DOR->(1,1,0)->(1,0,0): 3 hops vs Manhattan 1.
    with pytest.raises(ValueError, match="cycle in VC0 subrelation"):
        check_acyclic(image, CFG_4X4X1)
