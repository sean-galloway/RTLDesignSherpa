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
``{dst_x, dst_y, dst_z, qos}`` -> ``{port_mask[6:0], vc}``. The address
carries the full key width now (``qos`` included) so Task 7's QoS classes
land without reshaping the memory; the power-on image writes every QoS
region with the same DOR default (qos is decoded but not yet acted on).
The dst space occupies the low ``3*COORD_W`` address bits, so the default
image is one entry per representable dst coordinate:
``2**(3*COORD_W)`` entries (64 at COORD_W=2).

``default_dor_image`` returns the canonical cell-at-origin install: the
per-cell RAM is loaded at time 0 by the generated SystemVerilog ``initial``
block, which evaluates the same DOR decision per instance from that
instance's POS_X/POS_Y/POS_Z parameters (one checked-in module serves
every grid position). ``check_acyclic`` therefore models the fabric as
"the image at the origin cell, the DOR function everywhere else" and
proves the VC0 subrelation connected and acyclic by greedy hop-by-hop
simulation (spec sec. 13 formal assist; Duato's sufficient condition,
sec. 5.1 [D2][D7]).
"""

from dataclasses import dataclass

from .config import DeltaMeshConfig

NUM_PORTS = 7  # 6 neighbors + 1 local; pinned port ids below

PORT_IDS = (
    ("P_X_NEG", 0),
    ("P_X_POS", 1),
    ("P_Y_NEG", 2),
    ("P_Y_POS", 3),
    ("P_Z_NEG", 4),
    ("P_Z_POS", 5),
    ("P_LOCAL", 6),
)

(P_X_NEG, P_X_POS, P_Y_NEG, P_Y_POS,
 P_Z_NEG, P_Z_POS, P_LOCAL) = (pid for _, pid in PORT_IDS)

PORT_TO_MASK = {pid: 1 << pid for _, pid in PORT_IDS}

# Entry layout: {port_mask[6:0], vc} -- mask bit p set = route to port p;
# an all-zero mask is the table-level drop encoding. vc is 1 bit wide for
# the pinned NUM_VC=2 and rides the bit above the mask (entry width 8).
ENTRY_MASK_W = 7
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
    """Pack {port_mask[6:0], vc} into the RAM entry word."""
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
# 2026-10-13). Mode 0 is the custom per-cell RAM tables (power-on
# default); modes 1-8 are generator-emitted images selected by the
# cell's r_mode register -- a mux in front of the route_table RAM, so
# the RAM stays user-intact and switching back to mode 0 restores the
# custom tables.
#
# Task 6 scope pin (controller resolution): modes 2-8 are
# minimal-but-correct images. Modes 2 (systolic-1D) and 6 (convergecast)
# carry their pinned distinct routing; modes 3/4/5/7/8 are DOR images
# (catalog presence + selectability + acyclicity this task). Mode 5's
# true multicast replication lands with Task 8; the torus-dependent
# patterns (2's ring wrap, 4's periodic boundaries) land with Task 9.
MODE_CATALOG = {
    1: "mesh (pure DOR)",
    2: "systolic-1D: +X when dst_x > pos_x else P_LOCAL (wrap is Task 9)",
    3: "wavefront-2D: minimal DOR (diagonal schedules are traffic patterns)",
    4: "stencil-3D: minimal DOR (halo dsts are one-hop DOR deliveries)",
    5: "broadcast: minimal DOR placeholder (replication is Task 8)",
    6: "convergecast/reduce: every dst routes toward root (0,0,0)",
    7: "all-to-all/transpose: minimal DOR (permutations are traffic patterns)",
    8: "pipeline+rapids-stream: minimal DOR (the serpentine chain routes DOR)",
}

ROOT = (0, 0, 0)


def mode_port(mode_id: int, dst: tuple[int, int, int],
              pos: tuple[int, int, int], cfg: DeltaMeshConfig) -> int:
    """Port mask of a standard-mode image at ``pos`` toward ``dst``.

    Single source of truth for the emitted per-instance
    ``mode_default_entry`` SystemVerilog function (its mechanical twin,
    like ``dor_port``/``dor_default_entry``). Representable out-of-grid
    dsts carry the empty mask (the drop encoding). Mode 0 is the custom
    RAM tables and has no image; ids outside 0..8 raise.
    """
    if not 1 <= mode_id <= 8:
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
