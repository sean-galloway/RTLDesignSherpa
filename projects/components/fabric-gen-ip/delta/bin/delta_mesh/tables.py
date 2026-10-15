# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: delta_mesh.tables
# Purpose: Routing-table image builders and the offline VC0 acyclicity
#          checker for the delta mesh cell's per-cell route_table RAM
#          (spec 2026-10-13-delta-mesh-design.md sec. 5.1, sec. 13).
#
# Documentation: docs/superpowers/specs/2026-10-13-delta-mesh-design.md
# Subsystem: delta
#
# Author: sean galloway
# Created: 2026-10-15

"""Routing-table images for the delta mesh route_table RAM.

Table organization (plan-pinned): per-cell RAM keyed
``{dst_x, dst_y, dst_z, qos}`` -> ``{port_mask[8:0], vc}``. The address
carries the full key width now (``qos`` included) so Task 7's QoS classes
land without reshaping the memory; the power-on image writes every QoS
region with the same DOR default (qos is decoded but not yet acted on).
The dst space occupies the low ``3*COORD_W`` address bits, so the default
image is one entry per representable dst coordinate:
``2**(3*COORD_W)`` entries (64 at COORD_W=2).

Port list (Task 6c pin, 9 ports): the six axis ports, P_DIA (index 6) --
the tetrad diagonal-mate link, owner addition 2026-10-15 -- P_DIA2 (index
7) -- the inter-tetrad diagonal link, owner addition 2026-10-15 -- and
P_LOCAL (index 8). P_LOCAL's index MOVED from 7 to 8 when P_DIA2 landed;
every harness/TB/generate-loop references the tables.py PORT_IDS single
source of truth.

``default_dor_image`` returns the canonical cell-at-origin install: the
per-cell RAM is loaded at time 0 by the generated SystemVerilog ``initial``
block, which evaluates the same DOR decision per instance from that
instance's POS_X/POS_Y/POS_Z parameters (one checked-in module serves
every grid position). ``check_acyclic`` therefore models the fabric as
"the image at the origin cell, the DOR function everywhere else" and
proves the VC0 subrelation connected and acyclic by greedy hop-by-hop
simulation (spec sec. 13 formal assist; Duato's sufficient condition,
sec. 5.1 [D2][D7]). ``check_no_diag`` is the controller-pinned guard that
DOR -- the power-on default and modes 1-8 -- never selects either
diagonal port; mode 9 may select P_DIA, mode 10 may select P_DIA2 (spec
sec. 2.2/5.4, Task 6c).
"""

from dataclasses import dataclass

from .config import DeltaMeshConfig

NUM_PORTS = 9  # 6 axis neighbors + 2 diagonal + 1 local; pinned port ids

PORT_IDS = (
    ("P_X_NEG", 0),
    ("P_X_POS", 1),
    ("P_Y_NEG", 2),
    ("P_Y_POS", 3),
    ("P_Z_NEG", 4),
    ("P_Z_POS", 5),
    ("P_DIA", 6),
    ("P_DIA2", 7),
    ("P_LOCAL", 8),
)

(P_X_NEG, P_X_POS, P_Y_NEG, P_Y_POS,
 P_Z_NEG, P_Z_POS, P_DIA, P_DIA2, P_LOCAL) = (pid for _, pid in PORT_IDS)

PORT_TO_MASK = {pid: 1 << pid for _, pid in PORT_IDS}

# Entry layout: {port_mask[8:0], vc} -- mask bit p set = route to port p;
# an all-zero mask is the table-level drop encoding. vc is 1 bit wide for
# the pinned NUM_VC=2 and rides the bit above the mask (entry width 10).
# The mask widened from 8 to 9 bits when P_DIA2 landed (Task 6c): P_DIA
# occupies bit 6, P_DIA2 bit 7, P_LOCAL bit 8.
ENTRY_MASK_W = 9
ENTRY_VC_W = 1
ENTRY_VC_LO = ENTRY_MASK_W
ENTRY_W = ENTRY_MASK_W + ENTRY_VC_W


def coord_w(cfg: DeltaMeshConfig) -> int:
    """Coordinate width, matching the emitters' derivation."""
    return max(1, (max(cfg.cells_x, cfg.cells_y, cfg.cells_z) - 1).bit_length())


def table_index(dst: tuple[int, int, int], qos: int, cw: int) -> int:
    """RAM address for a dst key and QoS class: {qos, dst_z, dst_y, dst_x}."""
    x, y, z = dst
    return ((qos & 0x3) << (3 * cw)) | ((z & ((1 << cw) - 1)) << (2 * cw)) | \
           ((y & ((1 << cw) - 1)) << cw) | (x & ((1 << cw) - 1))


def pack_entry(port_mask: int, vc: int) -> int:
    """Pack {port_mask[7:0], vc} into the RAM entry word."""
    return ((vc & ((1 << ENTRY_VC_W) - 1)) << ENTRY_VC_LO) | \
           (port_mask & ((1 << ENTRY_MASK_W) - 1))


def unpack_entry(entry: int) -> tuple[int, int]:
    """Split a RAM entry word into (port_mask, vc)."""
    return (entry & ((1 << ENTRY_MASK_W) - 1),
            (entry >> ENTRY_VC_LO) & ((1 << ENTRY_VC_W) - 1))


def dor_port(dst: tuple[int, int, int], pos: tuple[int, int, int]) -> int:
    """Dimension-ordered first-hop port: X, then Y, then Z.

    A dst coordinate below the position takes that dimension's negative
    port (negative first toward the coord-0 boundary), above takes the
    positive port, equal moves to the next dimension; all equal delivers
    to the attached host (P_LOCAL).
    """
    dx, dy, dz = (d - p for d, p in zip(dst, pos))
    if dx < 0:
        return P_X_NEG
    if dx > 0:
        return P_X_POS
    if dy < 0:
        return P_Y_NEG
    if dy > 0:
        return P_Y_POS
    if dz < 0:
        return P_Z_NEG
    if dz > 0:
        return P_Z_POS
    return P_LOCAL


@dataclass
class TableEntry:
    """One route_table image entry: dst key, QoS class, mask, VC."""

    dst_x: int
    dst_y: int
    dst_z: int
    qos: int
    port_mask: int
    vc: int = 0

    @property
    def dst(self) -> tuple[int, int, int]:
        return (self.dst_x, self.dst_y, self.dst_z)


def default_dor_image(cfg: DeltaMeshConfig) -> list[TableEntry]:
    """Power-on image: one entry per representable dst coordinate (qos 0).

    The port value is the DOR first hop for the canonical cell at the grid
    origin; the emitted per-cell ``initial`` block re-derives the same
    decision from each instance's POS parameters. Representable dst keys
    outside the grid carry an empty mask (the drop encoding) -- the
    runtime range check drops them before the table is consulted.
    """
    cw = coord_w(cfg)
    origin = (0, 0, 0)
    image = []
    for key in range(1 << (3 * cw)):
        dst = ((key >> 0) & ((1 << cw) - 1),
               (key >> cw) & ((1 << cw) - 1),
               (key >> 2 * cw) & ((1 << cw) - 1))
        in_grid = (dst[0] < cfg.cells_x and dst[1] < cfg.cells_y
                   and dst[2] < cfg.cells_z)
        mask = PORT_TO_MASK[dor_port(dst, origin)] if in_grid else 0
        image.append(TableEntry(dst[0], dst[1], dst[2], 0, mask, 0))
    return image


# Standard fabric mode catalog (spec sec. 5.4, owner-confirmed
# 2026-10-13; modes 9-10 added 2026-10-15). Mode 0 is the custom per-cell
# RAM tables (power-on default); modes 1-10 are generator-emitted images
# selected by the cell's r_mode register -- a mux in front of the
# route_table RAM, so the RAM stays user-intact and switching back to
# mode 0 restores the custom tables.
#
# Task 6 scope pin (controller resolution): modes 2-8 are
# minimal-but-correct images. Modes 2 (systolic-1D) and 6 (convergecast)
# carry their pinned distinct routing; modes 3/4/5/7/8 are DOR images
# (catalog presence + selectability + acyclicity this task). Mode 5's
# true multicast replication lands with Task 8; the torus-dependent
# patterns (2's ring wrap, 4's periodic boundaries) land with Task 9.
#
# Task 6b pin (controller resolution): mode 9 (tetrad all-to-all K4) is
# the only image allowed to select P_DIA (checked by check_no_diag on
# every other image at generation time). Intra-tetrad dsts route 1 hop
# (edge mates via the axis port -- the DOR answer for a one-dimension
# mate; the diagonal mate via P_DIA); inter-tetrad dsts route DOR.
#
# Task 6c pin (controller resolution): mode 10 (tile all-to-all, K4 of
# tetrads) is the only image allowed to select P_DIA2. Within a 4x4x1
# tile the edge-adjacent-tetrad cells route via the shared +/-X/+/-Y
# boundary (1 hop for the touching pair, else DOR within the tile);
# diagonal-tetrad corner pairs route via P_DIA2 in exactly 1 hop;
# inter-tile dsts DOR.
MODE_CATALOG = {
    1: "mesh (pure DOR)",
    2: "systolic-1D: +X when dst_x > pos_x else P_LOCAL (wrap is Task 9)",
    3: "wavefront-2D: minimal DOR (diagonal schedules are traffic patterns)",
    4: "stencil-3D: minimal DOR (halo dsts are one-hop DOR deliveries)",
    5: "broadcast: minimal DOR placeholder (replication is Task 8)",
    6: "convergecast/reduce: every dst routes toward root (0,0,0)",
    7: "all-to-all/transpose: minimal DOR (permutations are traffic patterns)",
    8: "pipeline+rapids-stream: minimal DOR (the serpentine chain routes DOR)",
    9: "tetrad all-to-all (K4): diagonal mate via P_DIA, edge mates via "
       "the axis port (1 hop); inter-tetrad dsts DOR",
    10: "tile all-to-all (K4 of tetrads): diagonal-tetrad corner pairs "
        "via P_DIA2 (1 hop); edge-adjacent tetrads via axis ports; "
        "inter-tile dsts DOR",
}

ROOT = (0, 0, 0)


def _dia2_mate(pos: tuple[int, int, int]) -> tuple[int, int, int]:
    """Inter-tetrad diagonal mate of ``pos`` (may be out of grid).

    The mate is the diagonally-adjacent cell of the diagonally-neighboring
    tetrad: (x + (x&1 ? +1 : -1), y + (y&1 ? +1 : -1), z). This is the
    parity-directed form from the spec (sec. 2.2); it names exactly one
    cell per (x,y,z), and the link is symmetric.
    """
    x, y, z = pos
    return (x + (1 if (x & 1) else -1),
            y + (1 if (y & 1) else -1),
            z)


def mode_port(mode_id: int, dst: tuple[int, int, int],
              pos: tuple[int, int, int], cfg: DeltaMeshConfig) -> int:
    """Port mask of a standard-mode image at ``pos`` toward ``dst``.

    Single source of truth for the emitted per-instance
    ``mode_default_entry`` SystemVerilog function (its mechanical twin,
    like ``dor_port``/``dor_default_entry``). Representable out-of-grid
    dsts carry the empty mask (the drop encoding). Mode 0 is the custom
    RAM tables and has no image; ids outside 0..10 raise.
    """
    if not 1 <= mode_id <= 10:
        raise ValueError(f"no standard image for mode {mode_id}")
    if not (dst[0] < cfg.cells_x and dst[1] < cfg.cells_y
            and dst[2] < cfg.cells_z):
        return 0
    if mode_id == 2:
        # Systolic-1D pinned minimal image: stream +X when the dst sits
        # to the right, else deliver to the local PE. Without the torus
        # wrap (Task 9) the right edge consumes every dst.
        if dst[0] > pos[0]:
            return PORT_TO_MASK[P_X_POS]
        return PORT_TO_MASK[P_LOCAL]
    if mode_id == 6:
        # Convergecast: every packet walks the DOR path toward the root
        # and delivers there, whatever its dst key says.
        return PORT_TO_MASK[dor_port(ROOT, pos)]
    if mode_id == 9:
        # Tetrad K4: the diagonal mate -- the unique cell at (x^1, y^1, z)
        # of this cell's aligned 2x2x1 block -- rides P_DIA in 1 hop.
        # The XOR form names the mate exactly: on an odd X/Y edge the
        # out-of-grid mate can never be an in-grid dst, so no entry of a
        # tied-off cell can select P_DIA. Everything else (edge mates one
        # dimension away, inter-tetrad dsts, Z hops) is the DOR answer;
        # dst == pos falls through to P_LOCAL.
        if (dst[2] == pos[2]
                and (dst[0] ^ pos[0]) == 1 and (dst[1] ^ pos[1]) == 1):
            return PORT_TO_MASK[P_DIA]
        return PORT_TO_MASK[dor_port(dst, pos)]
    if mode_id == 10:
        # Tile K4-of-tetrads: the diagonal-tetrad corner mate rides
        # P_DIA2 in 1 hop. The parity-directed mate is symmetric; when
        # it steps out of the grid the link ties off and no in-grid dst
        # can name it. Everything else (edge-adjacent tetrads via the
        # shared boundary, within-tile DOR, inter-tile DOR, Z hops,
        # dst == pos) keeps the DOR answer.
        if (dst[2] == pos[2] and dst == _dia2_mate(pos)):
            return PORT_TO_MASK[P_DIA2]
        return PORT_TO_MASK[dor_port(dst, pos)]
    return PORT_TO_MASK[dor_port(dst, pos)]


def mode_image(cfg: DeltaMeshConfig, mode_id: int) -> list[TableEntry]:
    """Standard-mode image at the canonical origin cell.

    Same convention as ``default_dor_image``: one qos-0 entry per
    representable dst coordinate, the port resolved at the origin; the
    emitted SystemVerilog function re-derives the decision per instance
    POS. Every image is validated by ``check_acyclic`` (route_fn form)
    before any RTL is written.
    """
    origin = (0, 0, 0)
    image = []
    for key in range(1 << (3 * coord_w(cfg))):
        cw = coord_w(cfg)
        dst = ((key >> 0) & ((1 << cw) - 1),
               (key >> cw) & ((1 << cw) - 1),
               (key >> 2 * cw) & ((1 << cw) - 1))
        mask = mode_port(mode_id, dst, origin, cfg)
        image.append(TableEntry(dst[0], dst[1], dst[2], 0, mask, 0))
    return image


def check_acyclic(image: list[TableEntry], cfg: DeltaMeshConfig,
                  route_fn=None) -> None:
    """Greedy-routing simulation over the VC0 subrelation of ``image``.

    For every ordered in-grid (src, dst) pair, walk the fabric hop by
    hop until the walk reaches a cell whose port set for dst contains
    P_LOCAL (delivery). Two routing models:

    - default (``route_fn`` None): the origin cell (0,0,0) routes per
      the image entry for dst, every other cell per the DOR function
      (exactly what the generated per-instance initial block installs).
      Each walk must deliver within its Manhattan distance (minimal
      routing).
    - ``route_fn`` given: every cell routes per ``route_fn(dst, pos)``
      (an int port mask) -- the standard-mode images, which the mode
      mux applies at every cell. The hop bound relaxes to the cell
      count (the Manhattan bound only fits unicast-per-dst routing);
      the visited set still proves acyclicity.

    The VC0 subrelation must be connected and acyclic (spec sec. 5.1):
    a walk that revisits a cell or steps out of the grid is a cycle; a
    missing entry or an empty mask for an in-grid dst breaks
    connectivity. A multi-bit mask (multicast shape, Task 8) must
    deliver on every set bit, so each bit spawns its own bounded branch.
    P_DIA steps to the diagonal mate (x^1, y^1, z) -- the mode-9 tetrad
    link (Task 6b). P_DIA2 steps to the inter-tetrad diagonal mate
    (x + (x&1 ? +1 : -1), y + (y&1 ? +1 : -1), z) -- the mode-10 tile
    K4-of-tetrads link (Task 6c). Only mode-9/10 route_fns produce these
    diagonal hops (see check_no_diag).

    Raises:
        ValueError: "cycle in VC0 subrelation" on a cyclic/invalidating
            hop walk, "unreachable in VC0 subrelation" on a missing or
            empty-mask VC0 entry for an in-grid dst.
    """
    entries = {(e.dst_x, e.dst_y, e.dst_z): e for e in image if e.qos == 0}
    origin = (0, 0, 0)
    cells = [(x, y, z)
             for z in range(cfg.cells_z)
             for y in range(cfg.cells_y)
             for x in range(cfg.cells_x)]
    n_cells = len(cells)

    def step(pos: tuple[int, int, int], port: int) -> tuple[int, int, int]:
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
        if port == P_DIA:
            return (x ^ 1, y ^ 1, z)
        if port == P_DIA2:
            return _dia2_mate(pos)
        return pos  # P_LOCAL

    # Connectivity first: every in-grid dst must have a non-empty VC0
    # entry (Duato's condition is connected AND acyclic).
    for dst in cells:
        entry = entries.get(dst)
        if entry is None or entry.port_mask == 0:
            raise ValueError(
                f"dst {dst} unreachable in VC0 subrelation "
                f"(entry {'missing' if entry is None else 'empty'})")

    def ports_for(dst, pos) -> list[int]:
        if route_fn is not None:
            mask = route_fn(dst, pos)
        elif pos == origin:
            mask = entries[dst].port_mask
        else:
            mask = PORT_TO_MASK[dor_port(dst, pos)]
        return [p for p in range(NUM_PORTS) if mask & (1 << p)]

    # Acyclicity: greedy hop-by-hop walks, each bounded (Manhattan
    # distance for the default model, cell count for arbitrary
    # route_fns) and guarded by a visited set per walk. A walk delivers
    # when the current cell's port set for dst contains P_LOCAL.
    def visit(src, dst, pos, hops, seen) -> None:
        ports = ports_for(dst, pos)
        if not ports:
            raise ValueError(
                f"unreachable in VC0 subrelation: walk {src}->{dst} at "
                f"{pos} has an empty port set")
        if P_LOCAL in ports:
            return  # delivered at this cell
        bound = (n_cells if route_fn is not None else
                 sum(abs(a - b) for a, b in zip(src, dst)))
        for port in ports:
            nxt = step(pos, port)
            if hops + 1 > bound:
                raise ValueError(
                    f"cycle in VC0 subrelation: walk {src}->{dst} exceeded "
                    f"{bound} hops (detour or cycle)")
            if nxt not in cells:
                raise ValueError(
                    f"cycle in VC0 subrelation: walk {src}->{dst} stepped "
                    f"out of the grid at {nxt}")
            if nxt in seen:
                raise ValueError(
                    f"cycle in VC0 subrelation: walk {src}->{dst} revisits "
                    f"{nxt}")
            visit(src, dst, nxt, hops + 1, seen | {nxt})

    for src in cells:
        for dst in cells:
            visit(src, dst, src, 0, {src})


def check_no_diag(image: list[TableEntry], where: str,
                  allow: tuple[int, ...] = ()) -> None:
    """Guard (controller resolution, Task 6c): only allowed modes may
    route to diagonal ports.

    DOR -- the power-on default image and modes 1-8 -- selects only the
    six axis ports and P_LOCAL (spec sec. 2.2: the diagonal ports serve
    the mode-9/10 K4 images; sec. 5.4). Mode 9 may select P_DIA; mode 10
    may select P_DIA2; no other image may select either diagonal port.
    The fabric relies on this for odd-dimension grids, where a cell on
    the last X/Y row/column has its diagonal mate out of grid and the
    corresponding diagonal port tied off: if a disallowed image could
    name that port, the cell would misroute into the tie-off.

    Args:
        allow: tuple of diagonal port ids that may appear in this image
            (P_DIA for mode 9, P_DIA2 for mode 10).

    Raises:
        ValueError: ``where`` names the offending image and dst.
    """
    for e in image:
        for p in (P_DIA, P_DIA2):
            if p not in allow and (e.port_mask & PORT_TO_MASK[p]):
                name = "P_DIA" if p == P_DIA else "P_DIA2"
                raise ValueError(
                    f"{where}: dst {(e.dst_x, e.dst_y, e.dst_z)} routes to "
                    f"{name} -- only the allowed mode image may select the "
                    "diagonal port")
