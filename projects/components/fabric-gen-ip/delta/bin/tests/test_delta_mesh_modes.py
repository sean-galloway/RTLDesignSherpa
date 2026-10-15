# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Offline unit tests for the delta mesh standard-mode catalog
# (bin/delta_mesh/tables.py): mode_image / mode_port for the ten standard
# modes (spec sec. 5.4; modes 1-8 owner-confirmed 2026-10-13, mode 9 tetrad
# all-to-all K4 and mode 10 tile K4-of-tetrads added 2026-10-15), the
# generalized check_acyclic route_fn validation, and the pinned minimal
# images for the modes the DV suite exercises behaviorally (1 mesh,
# 2 systolic-1D, 5 broadcast placeholder, 6 convergecast, 9 tetrad K4,
# 10 tile K4 of tetrads). No simulator -- pure Python, run with the
# repo pytest.

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from delta_mesh.config import DeltaMeshConfig
from delta_mesh.tables import (
    P_DIA,
    P_DIA2,
    P_LOCAL,
    P_X_NEG,
    P_X_POS,
    P_Y_NEG,
    P_Y_POS,
    PORT_IDS,
    PORT_TO_MASK,
    TableEntry,
    check_acyclic,
    check_no_diag,
    default_dor_image,
    dor_port,
    mode_image,
    mode_port,
)

CFG_4X4X1 = DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)
CFG_2X2X1 = DeltaMeshConfig(cells_x=2, cells_y=2, cells_z=1)
CFG_3X3X1 = DeltaMeshConfig(cells_x=3, cells_y=3, cells_z=1)
CFG_1X1X1 = DeltaMeshConfig(cells_x=1, cells_y=1, cells_z=1)

MODE_IDS = tuple(range(1, 11))
MODE_NAMES = {
    1: "mesh",
    2: "systolic-1d",
    3: "wavefront-2d",
    4: "stencil-3d",
    5: "broadcast",
    6: "convergecast",
    7: "all-to-all/transpose",
    8: "pipeline+rapids-stream",
    9: "tetrad all-to-all (K4)",
    10: "tile all-to-all (K4 of tetrads)",
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


# ------------------------------------------------------------------
# Mode 9: tetrad all-to-all (K4) -- owner addition 2026-10-15
# ------------------------------------------------------------------
# Every 2x2x1 tetrad is fully connected: the 4 perimeter edges over
# +/-X/+/-Y (the DOR ports for a one-dimension mate) plus BOTH diagonals
# over P_DIA -- each cell has exactly one diagonal mate, (x^1, y^1, z),
# so one diagonal port per cell suffices. The fabric wires one diagonal
# link pair per tetrad; on an odd X/Y edge the out-of-grid mate's P_DIA
# ties off (no in-grid dst can name it, so no image entry may select it).

def _dia_mask(pos, cfg):
    # In-grid diagonal mate of pos (None when the mate falls off an odd
    # grid edge).
    mate = (pos[0] ^ 1, pos[1] ^ 1, pos[2])
    return mate if in_grid(mate, cfg) else None


def test_mode9_diagonal_mate_rides_p_dia():
    for cfg in (CFG_2X2X1, CFG_4X4X1):
        for pos in grid_coords(cfg):
            mate = _dia_mask(pos, cfg)
            if mate is None:
                continue  # odd-edge cell: its P_DIA ties off, no dst names it
            assert mode_port(9, mate, pos, cfg) == PORT_TO_MASK[P_DIA], (
                f"mode 9: diagonal mate {mate} of {pos} must ride P_DIA")
            # and the reverse (the link is symmetric, both ends route)
            assert mode_port(9, pos, mate, cfg) == PORT_TO_MASK[P_DIA]


def test_mode9_edge_mates_ride_the_axis_port():
    # Intra-tetrad dsts one dimension away keep the DOR/axis port (the
    # perimeter edges of the K4) -- both parities.
    cfg = CFG_4X4X1
    for (x, y) in ((0, 0), (1, 1), (2, 3), (3, 2)):
        pos = (x, y, 0)
        same_block = ((x & ~1), (y & ~1))
        for i in (0, 1):
            for j in (0, 1):
                dst = (same_block[0] + i, same_block[1] + j, 0)
                if dst == pos:
                    continue
                if dst[0] != pos[0] and dst[1] != pos[1]:
                    continue  # the diagonal mate: covered above
                assert mode_port(9, dst, pos, cfg) == \
                    PORT_TO_MASK[dor_port(dst, pos)], (
                        f"mode 9: edge mate {dst} of {pos} must use the "
                        f"axis port")


def test_mode9_inter_tetrad_uses_dor():
    # One block over (or a Z hop) is DOR, whatever the relative direction
    # -- including diagonally-adjacent blocks, which must NOT select
    # P_DIA (mate naming is by aligned 2x2 block, not by |dx|,|dy|).
    cfg = CFG_4X4X1
    assert mode_port(9, (2, 2, 0), (1, 1, 0), cfg) == \
        PORT_TO_MASK[P_X_POS]      # inter-tetrad diagonal: DOR +X
    assert mode_port(9, (1, 1, 0), (3, 3, 0), cfg) == \
        PORT_TO_MASK[P_X_NEG]      # neighboring block the other way: DOR -X
    for pos in grid_coords(cfg):
        # out-of-tetrad dsts are exactly the DOR image
        bx, by = pos[0] >> 1, pos[1] >> 1
        for dst in grid_coords(cfg):
            if dst[2] != pos[2] or (dst[0] >> 1, dst[1] >> 1) != (bx, by) \
                    or dst == pos:
                if dst != pos:
                    assert mode_port(9, dst, pos, cfg) == \
                        PORT_TO_MASK[dor_port(dst, pos)], (
                            f"mode 9: inter-tetrad dst {dst} of {pos} "
                            f"must use DOR")


def test_mode9_image_contains_p_dia_bits():
    # The only standard image allowed to select P_DIA is mode 9's, and it
    # must do so on every in-grid diagonal pair (both parities).
    cfg = CFG_4X4X1
    image = {(e.dst_x, e.dst_y, e.dst_z): e for e in mode_image(cfg, 9)}
    dia_pairs = 0
    for pos in grid_coords(cfg):
        mate = _dia_mask(pos, cfg)
        if mate is not None:
            dia_pairs += 1
    # at the origin: the image's own entry must name P_DIA for the mate
    assert image[(1, 1, 0)].port_mask == PORT_TO_MASK[P_DIA]
    # 4 tetrads x 2 ordered diagonal pairs each (pos->mate and mate->pos)
    assert dia_pairs == 16


# ------------------------------------------------------------------
# Mode 10: tile all-to-all (K4 of tetrads) -- owner addition 2026-10-15
# ------------------------------------------------------------------
# The four tetrads of a 2x2x1-tetrad tile (= 4x4x1 cells) are themselves
# fully connected: edge-adjacent tetrads over the shared +/-X/+/-Y
# boundaries (the DOR answer), diagonal tetrad pairs over P_DIA2 -- cell
# (x,y,z) links to its diagonal-tetrad corner mate
# (x + (x&1 ? +1 : -1), y + (y&1 ? +1 : -1), z): (1,1,0) <-> (2,2,0) and
# (1,2,0) <-> (2,1,0) per tile. The parity-directed form names the mate
# exactly; on an odd X/Y edge (or a sub-tile grid) the out-of-grid mate
# ties P_DIA2 off -- no in-grid dst can name it, so no image entry may
# select it (same three-legged proof as mode 9's P_DIA).

def _dia2_mate(pos):
    # Diagonal-tetrad corner mate of pos (may be out of grid).
    return (pos[0] + (1 if (pos[0] & 1) else -1),
            pos[1] + (1 if (pos[1] & 1) else -1),
            pos[2])


def test_mode10_diagonal_tetrad_mate_rides_p_dia2():
    for cfg in (CFG_4X4X1, CFG_3X3X1):
        for pos in grid_coords(cfg):
            mate = _dia2_mate(pos)
            if not in_grid(mate, cfg):
                continue  # odd-edge cell: its P_DIA2 ties off
            assert mode_port(10, mate, pos, cfg) == PORT_TO_MASK[P_DIA2], (
                f"mode 10: diagonal-tetrad mate {mate} of {pos} must ride "
                "P_DIA2")
            # and the reverse (the link is symmetric, both ends route)
            assert mode_port(10, pos, mate, cfg) == PORT_TO_MASK[P_DIA2]


def test_mode10_everything_else_is_dor():
    # Every in-grid dst that is NOT the diagonal-tetrad mate keeps the DOR
    # answer: edge-adjacent-tetrad cells via the shared boundary (1 hop
    # for the touching pair), everything else within-tile DOR, inter-tile
    # dsts DOR (out-of-grid here: drop encoding). The intra-tetrad
    # diagonal mate (mode 9's P_DIA case) is NOT special in mode 10 --
    # (0,0,0) -> (1,1,0) rides DOR, not P_DIA.
    cfg = CFG_4X4X1
    for pos in grid_coords(cfg):
        for dst in grid_coords(cfg):
            exp = PORT_TO_MASK[dor_port(dst, pos)]
            if dst[2] == pos[2] and dst == _dia2_mate(pos):
                exp = PORT_TO_MASK[P_DIA2]
            assert mode_port(10, dst, pos, cfg) == exp, (
                f"mode 10: dst {dst} of {pos}: "
                f"{mode_port(10, dst, pos, cfg):#x} != {exp:#x}")


def test_mode10_no_p_dia_and_sub_tile_grids_degenerate_to_dor():
    # Mode 10 never names P_DIA (its K4 edge is the tetrad-level diagonal
    # only), and on grids too small to hold a diagonal-tetrad pair the
    # whole image degenerates to pure DOR.
    cfg = CFG_4X4X1
    for e in mode_image(cfg, 10):
        assert not e.port_mask & PORT_TO_MASK[P_DIA]
    for cfg in (CFG_1X1X1, CFG_2X2X1):
        d = {(e.dst_x, e.dst_y, e.dst_z): e.port_mask
             for e in default_dor_image(cfg)}
        m = {(e.dst_x, e.dst_y, e.dst_z): e.port_mask
             for e in mode_image(cfg, 10)}
        assert m == d, f"mode 10 on {cfg.cells_x}x{cfg.cells_y}x{cfg.cells_z}" \
            " must degenerate to the DOR image (no in-grid mate)"


def test_no_diag_outside_modes_9_10():
    # Controller-pinned guard (spec sec. 2.2/5.4, Task 6c): DOR -- the
    # power-on default image and modes 1-8 -- must never select either
    # diagonal port; mode 9 may select P_DIA but never P_DIA2 (it is the
    # intra-tetrad image; its dsts never name the inter-tetrad mate);
    # mode 10 may select P_DIA2 but never P_DIA. This is what lets the
    # pre-6b suites prove no regression: their images route exactly as
    # before.
    check_no_diag(default_dor_image(CFG_4X4X1), "power-on DOR image")
    for mode_id in range(1, 9):
        check_no_diag(mode_image(CFG_4X4X1, mode_id), f"mode {mode_id}")
    check_no_diag(mode_image(CFG_4X4X1, 9), "mode 9",
                  allow=(P_DIA,))
    check_no_diag(mode_image(CFG_4X4X1, 10), "mode 10",
                  allow=(P_DIA2,))
    # the negative cases: a stray diagonal bit in a non-allowed image is a
    # build error, caught at generation time
    bad9 = [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   PORT_TO_MASK[P_DIA2]
                   if (e.dst_x, e.dst_y, e.dst_z) == (2, 2, 0)
                   else e.port_mask, e.vc)
        for e in mode_image(CFG_4X4X1, 9)
    ]
    with pytest.raises(ValueError, match="P_DIA2"):
        check_no_diag(bad9, "tampered mode 9", allow=(P_DIA,))
    bad10 = [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   PORT_TO_MASK[P_DIA]
                   if (e.dst_x, e.dst_y, e.dst_z) == (1, 1, 0)
                   else e.port_mask, e.vc)
        for e in mode_image(CFG_4X4X1, 10)
    ]
    with pytest.raises(ValueError, match="P_DIA"):
        check_no_diag(bad10, "tampered mode 10", allow=(P_DIA2,))
    bad1 = [
        TableEntry(e.dst_x, e.dst_y, e.dst_z, e.qos,
                   PORT_TO_MASK[P_DIA]
                   if (e.dst_x, e.dst_y, e.dst_z) == (1, 1, 0)
                   else e.port_mask, e.vc)
        for e in mode_image(CFG_4X4X1, 1)
    ]
    with pytest.raises(ValueError, match="P_DIA"):
        check_no_diag(bad1, "tampered mode 1")


def test_check_acyclic_mode9_cyclic_variant_rejected():
    # A deliberately cyclic mode-9 variant -- every non-local dst routes
    # P_DIA regardless of geometry -- ping-pongs (0,0,0)<->(1,1,0) forever
    # on the diagonal link; the checker must raise, not hang.
    cfg = CFG_4X4X1
    with pytest.raises(ValueError, match="cycle in VC0 subrelation"):
        check_acyclic(mode_image(cfg, 9), cfg,
                      route_fn=lambda dst, pos:
                      PORT_TO_MASK[P_DIA] if dst != pos
                      else PORT_TO_MASK[P_LOCAL])


def test_check_acyclic_mode10_cyclic_variant_rejected():
    # Same construction for the P_DIA2 link: every non-local dst routes
    # P_DIA2 regardless of geometry ping-pongs (1,1,0)<->(2,2,0) forever
    # on the diagonal-tetrad link; out-of-grid mates step out of the grid.
    cfg = CFG_4X4X1
    with pytest.raises(ValueError, match="cycle in VC0 subrelation"):
        check_acyclic(mode_image(cfg, 10), cfg,
                      route_fn=lambda dst, pos:
                      PORT_TO_MASK[P_DIA2] if dst != pos
                      else PORT_TO_MASK[P_LOCAL])


def test_port_list_pinned_with_both_diagonals():
    # The 9-port pin (Task 6c): P_DIA at 6, P_DIA2 at 7, P_LOCAL MOVES to 8.
    assert PORT_IDS == (
        ("P_X_NEG", 0), ("P_X_POS", 1),
        ("P_Y_NEG", 2), ("P_Y_POS", 3),
        ("P_Z_NEG", 4), ("P_Z_POS", 5),
        ("P_DIA", 6), ("P_DIA2", 7), ("P_LOCAL", 8),
    )


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
    for mode_id in range(11):
        tdata = (mode_id << 16) | MSW_MAGIC
        assert tdata & 0xFFFF == MSW_MAGIC
        assert (tdata >> 16) & 0xF == mode_id
        # the command rides the config payload shape: {entry, index}
        # with the magic in the index field and the mode id in the
        # entry field's low nibble (entry[7:4] written 0)
        assert (tdata >> 16) & 0xFF == mode_id
