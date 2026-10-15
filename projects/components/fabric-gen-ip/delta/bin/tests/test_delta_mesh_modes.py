# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Offline unit tests for the delta mesh standard-mode catalog
# (bin/delta_mesh/tables.py): mode_image / mode_port for the eight
# owner-confirmed standard modes (spec sec. 5.4), the generalized
# check_acyclic route_fn validation, and the pinned minimal images for
# the modes the DV suite exercises behaviorally (1 mesh, 2 systolic-1D,
# 5 broadcast placeholder, 6 convergecast). No simulator -- pure Python,
# run with the repo pytest.

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from delta_mesh.config import DeltaMeshConfig
from delta_mesh.tables import (
    P_LOCAL,
    P_X_POS,
    P_Y_POS,
    PORT_TO_MASK,
    TableEntry,
    check_acyclic,
    default_dor_image,
    dor_port,
    mode_image,
    mode_port,
)

CFG_4X4X1 = DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)
CFG_2X2X1 = DeltaMeshConfig(cells_x=2, cells_y=2, cells_z=1)
CFG_3X3X1 = DeltaMeshConfig(cells_x=3, cells_y=3, cells_z=1)
CFG_1X1X1 = DeltaMeshConfig(cells_x=1, cells_y=1, cells_z=1)

MODE_IDS = tuple(range(1, 9))
MODE_NAMES = {
    1: "mesh",
    2: "systolic-1d",
    3: "wavefront-2d",
    4: "stencil-3d",
    5: "broadcast",
    6: "convergecast",
    7: "all-to-all/transpose",
    8: "pipeline+rapids-stream",
}


def grid_coords(cfg):
    return [(x, y, z)
            for z in range(cfg.cells_z)
            for y in range(cfg.cells_y)
            for x in range(cfg.cells_x)]


def in_grid(dst, cfg):
    return (dst[0] < cfg.cells_x and dst[1] < cfg.cells_y
            and dst[2] < cfg.cells_z)


# ------------------------------------------------------------------
# Catalog presence and shape
# ------------------------------------------------------------------

@pytest.mark.parametrize("mode_id", MODE_IDS)
def test_mode_catalog_present(mode_id):
    # Every owner-confirmed mode (spec sec. 5.4) builds an image over the
    # full representable dst space (2^(3*COORD_W) entries at qos 0, the
    # same convention as default_dor_image).
    cfg = CFG_4X4X1
    image = mode_image(cfg, mode_id)
    cw = 2  # 4x4x1
    assert len(image) == 1 << (3 * cw)
    assert all(e.qos == 0 and e.vc == 0 for e in image)
    # in-grid dsts carry exactly one route port (unicast images this task;
    # multicast shapes arrive with Task 8 replication)
    for e in image:
        if in_grid(e.dst, cfg):
            assert e.port_mask != 0
            assert e.port_mask & (e.port_mask - 1) == 0, (
                f"mode {mode_id} dst {e.dst}: multi-bit mask {e.port_mask:#x} "
                "without Task 8 replication")
        else:
            assert e.port_mask == 0  # representable out-of-grid: drop encoding


def test_mode_names_cover_catalog():
    assert set(MODE_NAMES) == set(MODE_IDS)


# ------------------------------------------------------------------
# Pinned minimal images
# ------------------------------------------------------------------

def test_mode1_mesh_equals_default_dor():
    # Mode 1 (mesh) is pure DOR -- identical masks to the power-on default.
    d = {(e.dst_x, e.dst_y, e.dst_z): e.port_mask
         for e in default_dor_image(CFG_4X4X1)}
    m = {(e.dst_x, e.dst_y, e.dst_z): e.port_mask
         for e in mode_image(CFG_4X4X1, 1)}
    assert m == d


def test_mode2_systolic_pinned_gating():
    # Pinned minimal image (no torus wrap until Task 9): +X when
    # dst_x > pos_x, else P_LOCAL. On a 2-wide grid the right column
    # therefore delivers every dst locally (the systolic PE is the
    # endpoint; leftward delivery needs the wrap link).
    cfg = CFG_2X2X1
    origin = (0, 0, 0)
    right = (1, 0, 0)
    assert mode_port(2, (1, 0, 0), origin, cfg) == PORT_TO_MASK[P_X_POS]
    assert mode_port(2, (1, 1, 0), origin, cfg) == PORT_TO_MASK[P_X_POS]
    assert mode_port(2, (0, 1, 0), origin, cfg) == PORT_TO_MASK[P_LOCAL]
    assert mode_port(2, (0, 0, 0), right, cfg) == PORT_TO_MASK[P_LOCAL]
    assert mode_port(2, (1, 1, 0), right, cfg) == PORT_TO_MASK[P_LOCAL]


def test_mode5_broadcast_placeholder_is_dor():
    # Task 6 pin: mode 5's image routes all dsts via DOR; multicast
    # replication (true one-to-all delivery) is Task 8. The Task 6 DV
    # validates selection + single-hop spread only.
    cfg = CFG_4X4X1
    for pos in [(0, 0, 0), (1, 1, 0), (3, 3, 0)]:
        for dst in grid_coords(cfg):
            assert mode_port(5, dst, pos, cfg) == \
                PORT_TO_MASK[dor_port(dst, pos)]


def test_mode6_convergecast_to_root():
    # Every dst routes as if it were the root (0,0,0): packets injected
    # anywhere converge on the root cell and deliver there.
    cfg = CFG_4X4X1
    for dst in grid_coords(cfg):
        for pos in grid_coords(cfg):
            assert mode_port(6, dst, pos, cfg) == \
                PORT_TO_MASK[dor_port((0, 0, 0), pos)]


def test_mode_port_out_of_grid_drop():
    cfg = CFG_4X4X1  # 4x4x1: z=1 dsts are representable (COORD_W=2) but out
    for mode_id in MODE_IDS:
        assert mode_port(mode_id, (0, 0, 1), (0, 0, 0), cfg) == 0


# ------------------------------------------------------------------
# Acyclicity validation (route_fn form: every cell routes per the image)
# ------------------------------------------------------------------

@pytest.mark.parametrize("mode_id", MODE_IDS)
@pytest.mark.parametrize("cfg", [CFG_1X1X1, CFG_2X2X1, CFG_3X3X1, CFG_4X4X1])
def test_mode_images_acyclic(cfg, mode_id):
    image = mode_image(cfg, mode_id)
    check_acyclic(image, cfg,
                  route_fn=lambda dst, pos: mode_port(mode_id, dst, pos, cfg))


def test_check_acyclic_route_fn_cycle_detected():
    # A route_fn that always walks +X livelocks on any grid wider than 1
    # in x: the checker must raise, not hang.
    cfg = CFG_2X2X1
    image = mode_image(cfg, 1)
    with pytest.raises(ValueError, match="cycle in VC0 subrelation"):
        check_acyclic(image, cfg,
                      route_fn=lambda dst, pos: PORT_TO_MASK[P_X_POS])


def test_check_acyclic_route_fn_unreachable_detected():
    # An empty mask for an in-grid dst breaks connectivity even when a
    # route_fn is supplied (the origin-image preamble still applies).
    cfg = CFG_2X2X1
    image = [e for e in mode_image(cfg, 1) if e.dst != (1, 0, 0)]
    with pytest.raises(ValueError, match="unreachable in VC0 subrelation"):
        check_acyclic(image, cfg,
                      route_fn=lambda dst, pos: PORT_TO_MASK[P_X_POS]
                      if dst[0] > pos[0] else PORT_TO_MASK[P_LOCAL])


def test_check_acyclic_default_form_regression():
    # The Task 5 form (image at origin, DOR elsewhere, tight Manhattan
    # bound) is unchanged: the power-on image still validates, and a
    # detouring redirect is still caught by the hop bound.
    check_acyclic(default_dor_image(CFG_4X4X1), CFG_4X4X1)
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


# ------------------------------------------------------------------
# Broadcast mode-switch payload contract (pinned encoding)
# ------------------------------------------------------------------

# Pinned switch command: TDATA low 16 = mode-switch magic, TDATA[19:16]
# = mode id (the config entry field's low nibble). Mode 0 is the
# return-to-RAM switch. The controller's "16'hM0DE" spelling is not a
# legal SystemVerilog hex literal (M is not a hex digit); 16'hC0DE is
# the nearest legal stand-in ("config opcode"). The ack magic 16'hACED
# ("ACKED") is legal as pinned.
MSW_MAGIC = 0xC0DE
ACK_MAGIC = 0xACED


def test_msw_payload_layout():
    for mode_id in range(9):
        tdata = (mode_id << 16) | MSW_MAGIC
        assert tdata & 0xFFFF == MSW_MAGIC
        assert (tdata >> 16) & 0xF == mode_id
        # the command rides the config payload shape: {entry, index}
        # with the magic in the index field and the mode id in the
        # entry field's low nibble (entry[7:4] written 0)
        assert (tdata >> 16) & 0xFF == mode_id
