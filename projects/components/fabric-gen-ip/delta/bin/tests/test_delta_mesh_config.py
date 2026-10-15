import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pytest
from delta_mesh import DeltaMeshConfig, validate_mesh, header_width


DELTA_GENERATOR = Path(__file__).resolve().parents[1] / "delta_generator.py"


def test_torus_requires_two_cells():
    with pytest.raises(ValueError, match="torus.*>= 2"):
        validate_mesh(DeltaMeshConfig(cells_x=1, torus_x=True))


def test_user_width_below_header_rejected():
    with pytest.raises(ValueError, match="user-width"):
        validate_mesh(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1, user_width=8))


def test_header_width_formula():
    assert header_width(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)) == 6 * 2 + 32


def test_mesh_parses_without_masters_or_slaves():
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "mesh",
            "--cells-x", "4",
            "--cells-y", "4",
            "--cells-z", "1",
            "--user-width", "64",
            "--output-dir", "/tmp/delta_mesh_cli_test",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "mesh RTL generation lands in Task 2" in (result.stdout + result.stderr)


def test_flat_requires_masters_and_slaves():
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "flat",
            "--output-dir", "/tmp/delta_flat_cli_test",
        ],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 2
    err = result.stdout + result.stderr
    assert "--masters" in err or "--slaves" in err
    assert "required" in err.lower()
