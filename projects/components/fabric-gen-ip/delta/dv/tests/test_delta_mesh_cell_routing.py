# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh cell: rtl/delta_mesh_cell.sv
# (generated: --topology mesh --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64),
# through the flattening harness dv/tb/delta_mesh_cell_th.sv,
# with RDS-DV AXIS BFMs (plain flavor, header in TUSER) on all seven ports.
#
#   dor   power-on default DOR, no config write: local@POS(1,1,0) with
#         dst (3,0,0) exits P_X_POS; a flit from src (0,1,0) arriving on
#         P_X_NEG bound for dst (1,0,0) exits P_Y_NEG (hop toward y=0);
#         header and payload intact, all other ports silent

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
from delta_mesh_tb import DeltaMeshCellTB

FILELIST = 'projects/components/fabric-gen-ip/delta/rtl/filelists/delta_mesh.f'
# test-side harness (pure wiring; lives with the test, not in an RTL filelist)
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_cell_th.sv'
DUT_TOP = 'delta_mesh_cell_th'


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_cell_dor(dut):
    tb = DeltaMeshCellTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_dor_routing()


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


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_cell_routing(request, test_level):
    _run("cocotb_test_delta_mesh_cell_dor", test_level)
