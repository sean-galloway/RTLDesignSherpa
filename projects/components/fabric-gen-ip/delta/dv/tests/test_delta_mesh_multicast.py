# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh multicast: delta_mesh_fabric_2x2x1
# (generated at run time: --topology mesh --cells-x 2 --cells-y 2 --cells-z 1
#  --user-width 64), through the flattening harness
# dv/tb/delta_mesh_fabric_2x2_th.sv, with RDS-DV AXIS BFMs on all four
# boundary locals.
#
#   full_fabric   one multicast from (0,0,0) reaches every local exactly once
#   response_drop response-shaped packet dropped at injection + err_drop_cnt
#   deadlock_soak random unicast background + periodic multicast, no deadlock

import os
import subprocess
import sys

import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_TBCLASSES = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tbclasses'))
if _TBCLASSES not in sys.path:
    sys.path.insert(0, _TBCLASSES)
from delta_mesh_tb import DeltaMeshMulticastTB

DELTA_GENERATOR = os.path.abspath(
    os.path.join(os.path.dirname(__file__), '..', '..', 'bin', 'delta_generator.py'))
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_fabric_2x2_th.sv'
DUT_TOP = 'delta_mesh_fabric_2x2_th'
FABRIC_SV = 'delta_mesh_fabric_2x2x1.sv'
CELL_SV = 'delta_mesh_cell.sv'
RESET_DEFS_INCDIR = 'rtl/amba/includes'
FIFO_DEPS = (
    'rtl/common/counter_bin.sv',
    'rtl/common/fifo_control.sv',
    'rtl/amba/gaxi/gaxi_fifo_sync.sv',
    'rtl/common/arbiter_matrix.sv',
)


@pytest.fixture(scope="module")
def fabric_gen_dir(tmp_path_factory):
    """Generate the 2x2x1 cell + fabric into a scratch dir via the CLI."""
    gen_dir = tmp_path_factory.mktemp("delta_mesh_multicast")
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
        "delta_mesh_fabric_2x2x1.sv not emitted")
    return gen_dir


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_multicast_full_fabric(dut):
    tb = DeltaMeshMulticastTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_mcast_full_fabric(src_bidx=0)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_multicast_response_drop(dut):
    tb = DeltaMeshMulticastTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_mcast_response_drop(src_bidx=0)


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_delta_mesh_multicast_deadlock_soak(dut):
    tb = DeltaMeshMulticastTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_mcast_deadlock_soak()


def _run(testcase, test_level, gen_dir):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    verilog_sources = [
        *[os.path.join(repo_root, dep) for dep in FIFO_DEPS],
        str(gen_dir / CELL_SV),
        str(gen_dir / FABRIC_SV),
        os.path.join(repo_root, HARNESS),
    ]
    includes = [os.path.join(repo_root, RESET_DEFS_INCDIR)]

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
    "cocotb_test_delta_mesh_multicast_full_fabric",
    "cocotb_test_delta_mesh_multicast_response_drop",
    "cocotb_test_delta_mesh_multicast_deadlock_soak",
))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_multicast(request, testcase, test_level, fabric_gen_dir):
    _run(testcase, test_level, fabric_gen_dir)
