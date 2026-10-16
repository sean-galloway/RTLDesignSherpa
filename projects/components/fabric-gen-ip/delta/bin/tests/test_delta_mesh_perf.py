# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Offline unit tests for the delta mesh performance model
# (bin/delta_mesh_perf.py): zero-load latency, M/D/1 loaded latency,
# saturation throughput gamma, and traffic-pattern generators.

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(REPO_ROOT / "bin"))

from delta_mesh_perf import (
    MeshPerfParams,
    latency,
    loaded_latency,
    main,
    pattern_traffic,
    throughput_gamma,
)

BASE = MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8, load=0.0)


def test_zero_load_latency_pinned():
    # Spec §10: T0 = H*tr + D/v + L/b
    assert latency(BASE) == 3 * 1 + 4 / 1 + 64 / 8  # == 15


def test_loaded_latency_zero_load_is_T0():
    p = MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8, load=0.0)
    assert loaded_latency(p) == latency(p)


def test_loaded_latency_MD1_formula():
    # Standard M/D/1 sojourn time under deterministic flit service
    # (spec §10, [P20]): T(load) = T0 * (2 - rho) / (2 * (1 - rho))
    p = MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8, load=0.5)
    t0 = latency(p)
    assert loaded_latency(p) == pytest.approx(t0 * (2 - 0.5) / (2 * (1 - 0.5)))


def test_throughput_gamma_load_half():
    # Brief pin: gamma at load=0.5 equals 0.5/(1 - 0.5) == 1.0
    p = MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8, load=0.5)
    assert throughput_gamma(p) == pytest.approx(0.5 / (1 - 0.5))


def test_throughput_gamma_saturates_at_one_for_overload():
    for load in (1.0, 1.25, 2.0):
        p = MeshPerfParams(hops=3, tr=1, serialization_d=4, v=1, l=64, b=8, load=load)
        assert throughput_gamma(p) == pytest.approx(1.0)


def test_pattern_tornado_4x4_rotation():
    pairs = pattern_traffic("tornado", (4, 4))
    # tornado is a rotation in the X dimension by (k-1)//2 hops
    assert len(pairs) == 16
    assert set(pairs) == {((x, y), ((x + 1) % 4, y)) for x in range(4) for y in range(4)}
    assert ((0, 0), (1, 0)) in pairs
    assert ((3, 2), (0, 2)) in pairs


def test_pattern_bit_complement_flips_bits():
    pairs = pattern_traffic("bit-complement", (4, 4))
    assert len(pairs) == 16
    # 2-bit complement on each coordinate
    assert ((0, 0), (3, 3)) in pairs
    assert ((1, 2), (2, 1)) in pairs
    assert all((dst_x == 3 - src_x and dst_y == 3 - src_y) for (src_x, src_y), (dst_x, dst_y) in pairs)


def test_pattern_transpose_swaps_xy():
    pairs = pattern_traffic("transpose", (4, 4))
    assert len(pairs) == 16
    assert set(pairs) == {((x, y), (y, x)) for x in range(4) for y in range(4)}
    assert ((0, 1), (1, 0)) in pairs
    assert ((2, 3), (3, 2)) in pairs


def test_pattern_uniform_includes_all_pairs():
    pairs = pattern_traffic("uniform", (2, 2))
    assert len(pairs) == 16
    assert set(pairs) == {((x, y), (dx, dy))
                          for x in range(2) for y in range(2)
                          for dx in range(2) for dy in range(2)}


def test_pattern_invalid_name_raises():
    with pytest.raises(ValueError, match="unsupported pattern"):
        pattern_traffic("hotspot", (4, 4))


def test_CLI_table_runs(capsys):
    # Smoke-test the CLI entry point directly; no external deps.
    sys.argv = [
        "delta_mesh_perf.py",
        "--cells-x", "4",
        "--cells-y", "4",
        "--cells-z", "1",
        "--pattern", "tornado",
        "--load", "0.5",
    ]
    main()
    captured = capsys.readouterr()
    assert "T0" in captured.out or "latency" in captured.out.lower()
    assert "gamma" in captured.out.lower() or "throughput" in captured.out.lower()


def test_CLI_subprocess():
    result = subprocess.run(
        [sys.executable, str(REPO_ROOT / "bin" / "delta_mesh_perf.py"),
         "--cells-x", "4", "--cells-y", "4", "--cells-z", "1",
         "--pattern", "transpose", "--load", "0.5"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert "latency" in result.stdout.lower()
