#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: bin/delta_mesh_perf.py
# Purpose: Analytical performance model for the delta mesh topology.
#
# Design authority: docs/superpowers/specs/2026-10-13-delta-mesh-design.md §10.
#
# Formulas (spec §10):
#   Zero-load latency: T0 = H*tr + D/v + L/b
#       H  = hop count
#       tr = per-hop router delay (cycles)
#       D  = serialization distance (bytes; caller maps to flits/packets)
#       v  = propagation speed (bytes/cycle)
#       L  = packet length (bytes)
#       b  = channel bandwidth (bytes/cycle)
#   Loaded latency (M/D/1 deterministic flit service, [P20]):
#       T(load) = T0 * (2 - rho) / (2 * (1 - rho)), rho = load
#   Saturation throughput gamma is capped at 1.0; below saturation it is
#   modeled as rho/(1 - rho) per the brief pin at load=0.5.
#
# Default tr = 4 cycles/hop is the measured ring latency from Task 9.
# The aspirational 1 cycle/hop lookahead target is deferred (issue #120).
#
# Example invocation:
#   python3 bin/delta_mesh_perf.py --cells-x 4 --cells-y 4 --cells-z 1 \
#       --pattern tornado --load 0.5

import argparse
import sys
from dataclasses import dataclass
from typing import Iterable, List, Tuple


@dataclass
class MeshPerfParams:
    """Parameters for the delta mesh analytical performance model."""

    hops: float
    tr: float
    serialization_d: float
    v: float
    l: float
    b: float
    load: float


def latency(params: MeshPerfParams) -> float:
    """Return zero-load latency T0 = H*tr + D/v + L/b (spec §10)."""
    return params.hops * params.tr + params.serialization_d / params.v + params.l / params.b


def loaded_latency(params: MeshPerfParams) -> float:
    """Return M/D/1 loaded latency at params.load.

    Standard M/D/1 sojourn time under deterministic service time T0:
        T(load) = T0 * (2 - rho) / (2 * (1 - rho)),  rho = load.
    See spec §10 and Dally & Towles, Ch.23 [P20].
    """
    rho = params.load
    if rho >= 1.0:
        return float("inf")
    t0 = latency(params)
    return t0 * (2.0 - rho) / (2.0 * (1.0 - rho))


def throughput_gamma(params: MeshPerfParams) -> float:
    """Return saturation throughput gamma (normalized to channel capacity).

    Per spec §10, gamma_max is the saturation throughput from max channel load.
    The brief pins throughput_gamma(load=0.5) == 0.5/(1 - 0.5) == 1.0 and
    requires saturation at load >= 1.0.  Below the saturation knee the curve
    follows rho/(1 - rho); it is clamped to 1.0 once it reaches capacity.
    """
    rho = params.load
    if rho >= 1.0:
        return 1.0
    value = rho / (1.0 - rho)
    return 1.0 if value >= 1.0 else value


def _manhattan(src: Tuple[int, ...], dst: Tuple[int, ...]) -> int:
    return sum(abs(s - d) for s, d in zip(src, dst))


def _parse_dims(dims: Tuple[int, ...]) -> Tuple[int, int, int]:
    if len(dims) == 2:
        return dims[0], dims[1], 1
    if len(dims) == 3:
        return dims[0], dims[1], dims[2]
    raise ValueError("dims must be (x, y) or (x, y, z)")


def _all_nodes(dims: Tuple[int, int, int]) -> Iterable[Tuple[int, int, int]]:
    for z in range(dims[2]):
        for y in range(dims[1]):
            for x in range(dims[0]):
                yield (x, y, z)


def _node_2d_or_3d(node: Tuple[int, int, int], dims_len: int) -> Tuple[int, ...]:
    return node[:2] if dims_len == 2 else node


def pattern_traffic(name: str, dims: Tuple[int, ...]) -> List[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
    """Generate (src, dst) pairs for a named traffic pattern on an X*Y(*Z) grid.

    The returned coordinate tuples match the length of ``dims`` (2-D for an
    ``(x, y)`` argument, 3-D for ``(x, y, z)``).

    Supported patterns:
        tornado       - rotate in the X dimension by (k-1)//2 hops
                        (Dally & Towles, Ch.3 §3.2 [P1]).
        bit-complement - complement coordinate bits in each dimension.
        transpose     - swap X and Y coordinates.
        uniform       - all source/destination pairs (including self).
    """
    x, y, z = _parse_dims(dims)
    nodes = list(_all_nodes((x, y, z)))
    name = name.lower().replace("_", "-")
    dims_len = len(dims)

    def _n(node: Tuple[int, int, int]) -> Tuple[int, ...]:
        return _node_2d_or_3d(node, dims_len)

    if name == "tornado":
        offset = max(1, (x - 1) // 2) if x > 1 else 0
        return [(src_n, _n(((src[0] + offset) % x, src[1], src[2])))
                for src, src_n in zip(nodes, [_n(n) for n in nodes])]

    if name == "bit-complement":
        mask_x = x - 1 if (x & (x - 1)) == 0 else None
        mask_y = y - 1 if (y & (y - 1)) == 0 else None
        mask_z = z - 1 if (z & (z - 1)) == 0 else None
        if mask_x is None or mask_y is None or mask_z is None:
            raise ValueError("bit-complement requires power-of-two dimensions")
        return [
            (_n((sx, sy, sz)), _n((sx ^ mask_x, sy ^ mask_y, sz ^ mask_z)))
            for sx, sy, sz in nodes
        ]

    if name == "transpose":
        if x != y:
            raise ValueError("transpose requires square X*Y dimensions")
        return [(_n(src), _n((src[1], src[0], src[2]))) for src in nodes]

    if name == "uniform":
        node_views = [_n(n) for n in nodes]
        return [(src, dst) for src in node_views for dst in node_views]

    raise ValueError(f"unsupported pattern: {name}")


def _average_hops(pairs: List[Tuple[Tuple[int, ...], Tuple[int, ...]]]) -> float:
    if not pairs:
        return 0.0
    return sum(_manhattan(src, dst) for src, dst in pairs) / len(pairs)


def _fmt_table(pattern: str, dims: Tuple[int, int, int], params: MeshPerfParams,
               pairs: List[Tuple[Tuple[int, ...], Tuple[int, ...]]]) -> str:
    avg_hops = _average_hops(pairs)
    params = MeshPerfParams(
        hops=avg_hops,
        tr=params.tr,
        serialization_d=params.serialization_d,
        v=params.v,
        l=params.l,
        b=params.b,
        load=params.load,
    )
    t0 = latency(params)
    t_load = loaded_latency(params)
    gamma = throughput_gamma(params)

    lines = [
        "Delta mesh performance model",
        "----------------------------",
        f"Grid:        {dims[0]} x {dims[1]} x {dims[2]}",
        f"Pattern:     {pattern}",
        f"Pairs:       {len(pairs)}",
        f"Avg hops:    {avg_hops:.2f}",
        f"tr:          {params.tr} cycles/hop  (measured Task 9; issue #120)",
        f"Serialization: D={params.serialization_d}, v={params.v}",
        f"Packet:      L={params.l}, b={params.b}",
        f"Load (rho):  {params.load}",
        "",
        "Result:",
        f"  T0 (zero-load latency):  {t0:.2f} cycles",
        f"  T(load) (M/D/1):         {t_load:.2f} cycles",
        f"  gamma (saturation):      {gamma:.3f}",
    ]
    return "\n".join(lines)


def main(argv: List[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Delta mesh analytical performance model (spec §10)."
    )
    parser.add_argument("--cells-x", type=int, default=4, help="X dimension (default 4)")
    parser.add_argument("--cells-y", type=int, default=4, help="Y dimension (default 4)")
    parser.add_argument("--cells-z", type=int, default=1, help="Z dimension (default 1)")
    parser.add_argument(
        "--pattern",
        choices=["tornado", "bit-complement", "transpose", "uniform"],
        default="uniform",
        help="Traffic pattern (default uniform)",
    )
    parser.add_argument("--load", type=float, default=0.0, help="Offered load rho (default 0.0)")
    parser.add_argument("--tr", type=float, default=4.0,
                        help="Per-hop router latency in cycles (default 4, measured Task 9)")
    parser.add_argument("--serialization-d", type=float, default=64.0,
                        help="Serialization distance in bytes (default 64)")
    parser.add_argument("--v", type=float, default=1.0, help="Propagation speed bytes/cycle (default 1)")
    parser.add_argument("--l", type=float, default=64.0, help="Packet length in bytes (default 64)")
    parser.add_argument("--b", type=float, default=8.0, help="Channel bandwidth bytes/cycle (default 8)")

    args = parser.parse_args(argv)
    if args.cells_x < 1 or args.cells_y < 1 or args.cells_z < 1:
        parser.error("cell counts must be >= 1")
    if args.load < 0:
        parser.error("load must be >= 0")

    dims = (args.cells_x, args.cells_y, args.cells_z)
    pairs = pattern_traffic(args.pattern, dims)
    params = MeshPerfParams(
        hops=0.0,  # replaced by per-pattern average in the report
        tr=args.tr,
        serialization_d=args.serialization_d,
        v=args.v,
        l=args.l,
        b=args.b,
        load=args.load,
    )
    print(_fmt_table(args.pattern, dims, params, pairs))


if __name__ == "__main__":
    main()
