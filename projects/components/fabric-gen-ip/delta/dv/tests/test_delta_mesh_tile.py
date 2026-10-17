# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh mode 10 tile K4-of-tetrads + P_DIA2 inter-tetrad diagonal link:
# delta_mesh_fabric_4x4x1 (generated at run time: --topology mesh
#  --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64), through the
#  flattening harness dv/tb/delta_mesh_fabric_4x4_th.sv. Task 6c
#  (owner addition 2026-10-15): the 4x4x1 fabric is ONE tile, the K4-of-
#  tetrads unit (spec sec. 5.4 mode 10, sec. 2.2 P_DIA2).
#
#   tile_one_hop  (a) the two diagonal-tetrad corner pairs
#             (b5=(1,1,0)<->b10=(2,2,0) and b6=(2,1,0)<->b9=(1,2,0))
#             deliver in exactly 1 hop under mode 10, calibrated live
#             against power-on DOR where the same pairs are 2 hops.
#   bandwidth     (b) sustained back-to-back P_DIA2 streams on both
#             diagonal-tetrad pairs concurrently: every packet keeps the
#             exact 1-hop latency, the delivery window matches full-rate
#             pipeline arithmetic, a per-cycle witness samples all
#             inter-cell axis ports and sees zero activity during the
#             isolated P_DIA2 bursts, and non-participating boundaries
#             stay silent.

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
from delta_mesh_tb import DeltaMeshTileTB

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_4x4_th.sv'
DUT_TOP = 'delta_mesh_fabric_4x4_th'
FABRIC_SV = 'delta_mesh_fabric_4x4x1.sv'
CELL_SV = 'delta_mesh_cell.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
# The cell's dependencies, from their owning areas' filelists (mirrors the
# -f set in rtl/filelists/delta_mesh.f).
DEP_FILELISTS = (
    'rtl/amba/filelists/reset_defs.f',
    'rtl/amba/filelists/gaxi_skid_buffer.f',
    'rtl/common/filelists/arbiter_matrix.f',
)


@pytest.fixture(scope="module")
def fabric_gen_dir(tmp_path_factory):
    """Generate the 4x4x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_fabric_4x4")
    result = subprocess.run(
        [
            sys.executable,
            DELTA_GENERATOR,
            "--topology", "mesh",
            "--cells-x", "4",
            "--cells-y", "4",
            "--cells-z", "1",
            "--user-width", "64",
            "--output-dir", str(gen_dir),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, (
        f"delta_generator.py mesh failed:\n{result.stdout}\n{result.stderr}")
    assert (gen_dir / CELL_SV).is_file(), "mesh cell artifact not emitted"
    assert (gen_dir / FABRIC_SV).is_file(), (
        "delta_mesh_fabric_4x4x1.sv not emitted")
    return gen_dir


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tile_k4_one_hop(dut):
    tb = DeltaMeshTileTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_tile_k4_one_hop()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tile_diag2_bandwidth(dut):
    tb = DeltaMeshTileTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_tile_diag2_bandwidth()


def _run(testcase, test_level, gen_dir):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    dep_sources, dep_includes = get_sources_from_multiple_filelists(
        repo_root=repo_root, filelist_paths=list(DEP_FILELISTS))
    verilog_sources = [
        *dep_sources,
        str(gen_dir / CELL_SV),
        str(gen_dir / FABRIC_SV),
        os.path.join(repo_root, HARNESS),
    ]
    includes = list(dict.fromkeys([os.path.join(repo_root, RESET_DEFS_INCDIR), *dep_includes]))

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    worker_suffix = f"_{worker_id}" if worker_id else ""
    sim_build_name = f"test_{DUT_TOP}_{testcase}_{test_level}{worker_suffix}"
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
        waves=False,
        extra_args=['--assert', '-Wno-WIDTHEXPAND', '-Wno-DECLFILENAME'] + waves['extra_args'],
        plus_args=waves['sim_args'],
        extra_env={
            'COCOTB_LOG_LEVEL': 'INFO',
            'LOG_PATH': log_path,
            'COCOTB_RESULTS_FILE': results_path,
            'TEST_COORD_W': '2',
            # The 4x4 fabric is large; -O0 cuts Verilator C++ compile time
            # dramatically while the gate test runs only a few packets.
            'OPT_FAST': '-O0',
            'OPT_SLOW': '-O0',
            'OPT_GLOBAL': '-O0',
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("testcase", (
    "cocotb_test_delta_mesh_tile_k4_one_hop",
    "cocotb_test_delta_mesh_tile_diag2_bandwidth",
))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_tile(request, testcase, test_level, fabric_gen_dir):
    _run(testcase, test_level, fabric_gen_dir)
