import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pytest
from delta_mesh import DeltaMeshConfig, header_width, validate_mesh

DELTA_GENERATOR = Path(__file__).resolve().parents[1] / "delta_generator.py"


def test_torus_requires_two_cells():
    with pytest.raises(ValueError, match="torus.*>= 2"):
        validate_mesh(DeltaMeshConfig(cells_x=1, torus_x=True))


def test_user_width_below_header_rejected():
    with pytest.raises(ValueError, match="user-width"):
        validate_mesh(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1, user_width=8))


def test_fifo_impl_sram_rejected_in_mesh():
    with pytest.raises(ValueError, match="sram.*not supported in mesh"):
        validate_mesh(DeltaMeshConfig(cells_x=2, cells_y=2, fifo_impl="sram"))


def test_amba5_rejected_in_mesh():
    with pytest.raises(ValueError, match="amba5.*not supported in mesh"):
        validate_mesh(DeltaMeshConfig(cells_x=2, cells_y=2, amba5=True))


def test_header_width_formula():
    assert header_width(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)) == 6 * 2 + 32


def test_mesh_parses_without_masters_or_slaves(tmp_path):
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "mesh",
            "--cells-x", "4",
            "--cells-y", "4",
            "--cells-z", "1",
            "--user-width", "64",
            "--output-dir", str(tmp_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert (tmp_path / "delta_mesh_cell.sv").is_file()
    assert (tmp_path / "delta_mesh_fabric_4x4x1.sv").is_file()
    assert (tmp_path / "filelists" / "delta_mesh.f").is_file()


def test_mesh_fabric_supports_torus_task_9(tmp_path):
    # Torus wrap links are now supported (Task 9); generation succeeds and
    # emits the expected artifacts.
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "mesh",
            "--cells-x", "2",
            "--cells-y", "2",
            "--cells-z", "1",
            "--torus-x",
            "--user-width", "64",
            "--output-dir", str(tmp_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert (tmp_path / "delta_mesh_cell.sv").is_file()
    assert (tmp_path / "delta_mesh_fabric_2x2x1.sv").is_file()
    assert (tmp_path / "filelists" / "delta_mesh.f").is_file()


def test_mesh_fabric_accepts_torus_comma_form(tmp_path):
    # --torus=x,y,z is the spec CLI form; it must produce the same artifacts
    # as the boolean --torus-x/--torus-y/--torus-z aliases.
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "mesh",
            "--cells-x", "2",
            "--cells-y", "2",
            "--cells-z", "2",
            "--torus", "x,y,z",
            "--user-width", "64",
            "--output-dir", str(tmp_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert (tmp_path / "delta_mesh_cell.sv").is_file()
    assert (tmp_path / "delta_mesh_fabric_2x2x2.sv").is_file()
    assert (tmp_path / "filelists" / "delta_mesh.f").is_file()


def test_mesh_fabric_rejects_bad_torus_comma_form(tmp_path):
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "mesh",
            "--cells-x", "2",
            "--cells-y", "2",
            "--cells-z", "1",
            "--torus", "x,y",
            "--user-width", "64",
            "--output-dir", str(tmp_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 2


def test_flat_requires_masters_and_slaves(tmp_path):
    result = subprocess.run(
        [
            sys.executable,
            str(DELTA_GENERATOR),
            "--topology", "flat",
            "--output-dir", str(tmp_path),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 2
    err = result.stdout + result.stderr
    assert "--masters" in err or "--slaves" in err
    assert "required" in err.lower()
