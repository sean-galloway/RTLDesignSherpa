# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: delta_mesh.header
# Purpose: TUSER header field offsets for the delta mesh cell -- the single
#          source of truth shared by cell RTL emission and the DV tests.
#
# Documentation: docs/superpowers/specs/2026-10-13-delta-mesh-design.md (sec. 4)
# Subsystem: delta
#
# Author: sean galloway
# Created: 2026-10-14

"""Mesh head-flit header layout (lives in TUSER on the first beat of a packet).

Field order is LSB-first, pinned by the plan (2026-10-14-delta-mesh-implementation,
Global Constraints):

    dst_x, dst_y, dst_z, src_x, src_y, src_z   (each COORD_W bits)
    qos[1:0], mcast, vc, misroute_budget[3:0],
    sr_ptr[7:0], packet_id[15:0]

Total header width: 6 * COORD_W + 32 bits. The generator rejects
--user-width below that floor (see config.header_width).
"""

COORD_FIELDS = ("dst_x", "dst_y", "dst_z", "src_x", "src_y", "src_z")

# Fixed-width tail fields after the six coordinates.
TAIL_WIDTHS = {
    "qos": 2,
    "mcast": 1,
    "vc": 1,
    "misroute_budget": 4,
    "sr_ptr": 8,
    "packet_id": 16,
}

HEADER_FIELDS = COORD_FIELDS + tuple(TAIL_WIDTHS)


def build_header_offsets(coord_w: int) -> dict[str, tuple[int, int]]:
    """LSB offset and width of every header field for a given coordinate width.

    Returns:
        dict mapping field name to (lsb_offset, width) in bits, LSB-first.
    """
    offsets: dict[str, tuple[int, int]] = {}
    lo = 0
    for field in COORD_FIELDS:
        offsets[field] = (lo, coord_w)
        lo += coord_w
    for field, width in TAIL_WIDTHS.items():
        offsets[field] = (lo, width)
        lo += width
    return offsets


def header_width_for(coord_w: int) -> int:
    """Total header width for a given coordinate width (6*COORD_W + 32)."""
    return 6 * coord_w + 32


# Offsets for the default 4x4x1 configuration (COORD_W = 2). Consumers with a
# different coordinate width call build_header_offsets() themselves.
FIELD_OFFSETS = build_header_offsets(2)
