# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh mode 9 tetrad K4 + P_DIA diagonal link:
# delta_mesh_fabric_2x2x1 (generated at run time: --topology mesh
#  --cells-x 2 --cells-y 2 --cells-z 1 --user-width 64), through the
#  flattening harness dv/tb/delta_mesh_fabric_2x2_th.sv. Task 6b
#  (owner addition 2026-10-15): the 2x2x1 fabric is a single tetrad, the
#  K4 unit (spec sec. 5.4 mode 9, sec. 2.2 diagonal port).
#
#   k4_one_hop  (a) all 12 ordered intra-tetrad pairs (plus the 4
#             self-pairs) deliver exactly-once; every non-self pair
#             measures EXACTLY the 1-hop injection->ejection latency
#             (calibrated live against the power-on DOR mode, where the
#             diagonal pair is 2 hops) -- a 2-hop detour adds a full hop
#             of latency and cannot masquerade as 1 hop
#   bandwidth   (b) sustained back-to-back diagonal-mate streams in both
#             directions concurrently (b0<->b3): every packet keeps the
#             exact 1-hop latency, the delivery window matches full-rate
#             pipeline arithmetic, a per-cycle witness samples the
#             inter-cell axis ports and sees zero activity (any hidden
#             2-hop detour would toggle an intermediate cell's axis
#             port), and the non-participating cells b1/b2 stay silent

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
from delta_mesh_tb import DeltaMeshTetradTB

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_th.sv'
DUT_TOP = 'delta_mesh_fabric_2x2_th'
FABRIC_SV = 'delta_mesh_fabric_2x2x1.sv'
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
    """Generate the 2x2x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_fabric_2x2")
    result = subprocess.run(
        [
            sys.executable,
            DELTA_GENERATOR,
            "--topology", "mesh",
            "--cells-x", "2",
            "--cells-y", "2",
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
        "delta_mesh_fabric_2x2x1.sv not emitted -- fabric emission is the "
        "Task 3 deliverable under test")
    return gen_dir


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tetrad_k4_one_hop(dut):
    tb = DeltaMeshTetradTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_tetrad_k4_one_hop()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tetrad_diag_bandwidth(dut):
    tb = DeltaMeshTetradTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_tetrad_diag_bandwidth()


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
            'TEST_COORD_W': '1',
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("testcase", (
    "cocotb_test_delta_mesh_tetrad_k4_one_hop",
    "cocotb_test_delta_mesh_tetrad_diag_bandwidth",
))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_tetrad(request, testcase, test_level, fabric_gen_dir):
    _run(testcase, test_level, fabric_gen_dir)
