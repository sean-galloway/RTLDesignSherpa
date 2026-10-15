# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh routing tables: rtl/delta_mesh_cell.sv
# (generated: --topology mesh --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64),
# through dv/tb/delta_mesh_cell_th.sv (GRID 4x4x1, POS (1,1,0)), exercising
# the per-cell route_table RAM: power-on default image, in-band config
# read/write on the local port, reroute via table rewrite, and the
# out-of-range-dst drop path with o_err_drop_cnt.
#
#   config   read the power-on entry for dst (3,0,0); rewrite dst (2,2,0)
#            to P_Y_POS (DOR would say P_X_POS); traffic follows the new
#            route; readback confirms -- all with zero config writes to
#            the rest of the table (Review Focus #1 companion: the default
#            image itself routes, see the cell/fabric all-pairs suites)
#   errdrop  Review Focus #2: dst (0,0,1) on the Z=1 grid is representable
#            (COORD_W=2) and out of range: the head flit is dropped and
#            err_drop_cnt counts heads only (body beats drain silently);
#            post-drop traffic is unaffected

import os
import sys

import cocotb
import pytest
from cocotb_test.simulator import run
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from TBClasses.shared.utilities import get_paths, get_wave_config, sim_build_path

_TBCLASSES = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', 'tbclasses'))
if _TBCLASSES not in sys.path:
    sys.path.insert(0, _TBCLASSES)
from delta_mesh_tb import DeltaMeshTablesTB

FILELIST = 'projects/components/fabric-gen-ip/delta/rtl/filelists/delta_mesh.f'
# test-side harness (pure wiring; lives with the test, not in an RTL filelist)
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_cell_th.sv'
DUT_TOP = 'delta_mesh_cell_th'


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tables_config(dut):
    tb = DeltaMeshTablesTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_config_read_write_reroute()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_tables_err_drop(dut):
    tb = DeltaMeshTablesTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_err_drop()


def _run(testcase, test_level):
    module, repo_root, tests_dir, log_dir, _ = get_paths({})
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root, filelist_path=FILELIST)
    verilog_sources = verilog_sources + [os.path.join(repo_root, HARNESS)]

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
            **level_env(test_level),
            **waves['extra_env'],
        },
    )


@pytest.mark.parametrize("testcase", (
    "cocotb_test_delta_mesh_tables_config",
    "cocotb_test_delta_mesh_tables_err_drop",
))
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_tables(request, testcase, test_level):
    _run(testcase, test_level)
