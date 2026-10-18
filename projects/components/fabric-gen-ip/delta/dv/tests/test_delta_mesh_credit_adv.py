# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh fabric: cell credit advertisement (delta DELTA-010, TILE_SPEC
# 11.10) on delta_mesh_fabric_2x2x1, generated at run time at a 128-bit data
# width (the tile header is one 128-bit beat):
#   --topology mesh --cells-x 2 --cells-y 2 --cells-z 1 --data-width 128
#   --user-width 64
# through the flattening harness dv/tb/delta_mesh_fabric_2x2_th.sv with
# CELL_CREDITS set and TILE_IO_X/Y/Z naming the tile I/O's attach cell.
#
#   adv[b0]  attach cell (0,0,0): every cell's node advertises once, the
#            attach cell (0 hops) included; nothing reaches b1..b3
#   adv[b3]  attach cell (1,1,0): the same, routed the other way

import os
import subprocess
import sys

import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.filelist_utils import get_sources_from_multiple_filelists
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_TBCLASSES = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tbclasses'))
if _TBCLASSES not in sys.path:
    sys.path.insert(0, _TBCLASSES)
from delta_mesh_tb import DeltaMeshFabricTB

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_th.sv'
DUT_TOP = 'delta_mesh_fabric_2x2_th'
FABRIC_SV = 'delta_mesh_fabric_2x2x1.sv'
CELL_SV = 'delta_mesh_cell.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
DEP_FILELISTS = (
    'rtl/amba/filelists/reset_defs.f',
    'rtl/amba/filelists/gaxi_skid_buffer.f',
    'rtl/common/filelists/arbiter_matrix.f',
)
DATA_WIDTH = 128
CELL_CREDITS = 24


@pytest.fixture(scope="module")
def fabric_gen_dir(tmp_path_factory):
    """Generate the 128-bit 2x2x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_credit_adv")
    result = subprocess.run(
        [sys.executable, DELTA_GENERATOR, "--topology", "mesh",
         "--cells-x", "2", "--cells-y", "2", "--cells-z", "1",
         "--data-width", str(DATA_WIDTH), "--user-width", "64",
         "--output-dir", str(gen_dir)],
        capture_output=True, text=True, check=False)
    assert result.returncode == 0, (
        f"delta_generator.py mesh failed:\n{result.stdout}\n{result.stderr}")
    assert (gen_dir / CELL_SV).is_file() and (gen_dir / FABRIC_SV).is_file()
    return gen_dir


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_credit_adv(dut):
    tb = DeltaMeshFabricTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_credit_advertisement(
        int(os.environ['TEST_CELL_CREDITS']), tile_io_idx=int(os.environ['TEST_TILE_IO_IDX']))


def _run(testcase, test_level, gen_dir, tile_io_idx):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dep_sources, dep_includes = get_sources_from_multiple_filelists(
        repo_root=repo_root, filelist_paths=list(DEP_FILELISTS))
    verilog_sources = [*dep_sources, str(gen_dir / CELL_SV), str(gen_dir / FABRIC_SV),
                       os.path.join(repo_root, HARNESS)]
    includes = list(dict.fromkeys([os.path.join(repo_root, RESET_DEFS_INCDIR), *dep_includes]))
    io = DeltaMeshFabricTB.BOUNDARY_COORDS[tile_io_idx]

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{DUT_TOP}_{testcase}_b{tile_io_idx}_{test_level}{worker_suffix}"
    log_path = os.path.join(log_dir, f'{sim_build_name}.log')
    results_path = os.path.join(log_dir, f'results_{sim_build_name}.xml')
    sim_build = sim_build_path(tests_dir, sim_build_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    waves = get_wave_config(sim_build)
    run(
        python_search=[tests_dir, os.path.join(tests_dir, '..', 'tbclasses')],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=DUT_TOP,
        module=module,
        testcase=testcase,
        sim_build=sim_build,
        parameters={'DATA_WIDTH': DATA_WIDTH, 'COORD_W': 1, 'CELL_CREDITS': CELL_CREDITS,
                    'TILE_IO_X': io[0], 'TILE_IO_Y': io[1], 'TILE_IO_Z': io[2]},
        waves=False,
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'TEST_COORD_W': '1',
            'TEST_DATA_WIDTH': str(DATA_WIDTH),
            'TEST_CELL_CREDITS': str(CELL_CREDITS),
            'TEST_TILE_IO_IDX': str(tile_io_idx),
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("tile_io_idx", [0, 3])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_credit_adv(request, test_level, tile_io_idx, fabric_gen_dir):
    _run("cocotb_test_delta_mesh_credit_adv", test_level, fabric_gen_dir, tile_io_idx)
