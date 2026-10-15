# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta mesh cell flow control: rtl/delta_mesh_cell.sv
# (generated: --topology mesh --cells-x 4 --cells-y 4 --cells-z 1 --user-width 64),
# through dv/tb/delta_mesh_cell_th.sv, which exposes the per-port s_credit
# inputs so this suite can model the downstream neighbor's credits.
#
#   exhaust   downstream credits at zero: producer stalls once the input
#             FIFO (DEPTH=4) fills, no flit presented, nothing dropped;
#             releasing credits drains the payload complete and in order
#   atomic    Review Focus #3: one flit of credit space left on the xpos
#             link, two 4-beat packets from two sources to the same
#             output: no interleaving, no loss
#   steady    back-to-back packets on one output sustain 1 flit/clk with
#             no worse than the documented 1-cycle-per-packet-boundary
#             bubble

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
from delta_mesh_tb import DeltaMeshFlowControlTB

FILELIST = 'projects/components/fabric-gen-ip/delta/rtl/filelists/delta_mesh.f'
# test-side harness (pure wiring; lives with the test, not in an RTL filelist)
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_mesh_cell_th.sv'
DUT_TOP = 'delta_mesh_cell_th'

SCENARIOS = (
    ("cocotb_test_delta_mesh_fc_exhaustion", "exhaustion"),
    ("cocotb_test_delta_mesh_fc_atomicity", "atomicity"),
    ("cocotb_test_delta_mesh_fc_steady_state", "steady-state"),
)


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_fc_exhaustion(dut):
    tb = DeltaMeshFlowControlTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_credit_exhaustion_and_drain()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_fc_atomicity(dut):
    tb = DeltaMeshFlowControlTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_atomicity_one_credit_left()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_mesh_fc_steady_state(dut):
    tb = DeltaMeshFlowControlTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_back_to_back_steady_state()


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


@pytest.mark.parametrize("testcase,label", SCENARIOS,
                         ids=[s[1] for s in SCENARIOS])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_mesh_flow_control(request, testcase, label, test_level):
    _run(testcase, test_level)
