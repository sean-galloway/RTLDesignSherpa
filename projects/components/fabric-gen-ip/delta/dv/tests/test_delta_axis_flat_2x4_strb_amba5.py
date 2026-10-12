# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# delta AMBA 5 crossbar: rtl_test/delta_axis_flat_2x4_strb_amba5.sv
# (generated: --masters 2 --slaves 4 --data-width 32 --strb-width 4 --amba5),
# through the flattening harness dv/tb/delta_axis_flat_2x4_strb_amba5_th.sv,
# with RDS-DV AXIS5 BFMs (enable_parity=True) on all six ports.
#
#   routing   every master -> every slave, concurrent; payload *CHK carried
#             odd-parity clean, control *CHK generated as inversions, no flag
#   wakeup    TWAKEUP before TVALID reaches only the TDEST slave
#   errors    bad TDATACHK / TVALIDCHK / TREADYCHK each set the right sticky
#             s<m>_parity_error / m<s>_parity_error, and reset clears it
#
# IHI 0051B ch. 5 (Check_Type = Odd_Parity_Byte_All). Pattern B.

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
from delta_axis_amba5_tb import DeltaAxisAmba5TB

FILELIST = 'projects/components/fabric-gen-ip/delta/rtl_test/filelists/delta_axis_flat_2x4_strb_amba5.f'
# test-side harness (pure wiring; lives with the test, not in an RTL filelist)
HARNESS = 'projects/components/fabric-gen-ip/delta/dv/tb/delta_axis_flat_2x4_strb_amba5_th.sv'
DUT_TOP = 'delta_axis_flat_2x4_strb_amba5_th'


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_amba5_routing(dut):
    tb = DeltaAxisAmba5TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_routing_with_checks()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_amba5_wakeup(dut):
    tb = DeltaAxisAmba5TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_wakeup_steering()


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_test_delta_amba5_chk_errors(dut):
    tb = DeltaAxisAmba5TB(dut)
    await tb.setup_clocks_and_reset()
    await tb.run_error_injection()


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
def test_delta_axis_flat_2x4_strb_amba5_routing(request, test_level):
    _run("cocotb_test_delta_amba5_routing", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_axis_flat_2x4_strb_amba5_wakeup(request, test_level):
    _run("cocotb_test_delta_amba5_wakeup", test_level)


@pytest.mark.parametrize("test_level", reg_level_grid())
def test_delta_axis_flat_2x4_strb_amba5_chk_errors(request, test_level):
    _run("cocotb_test_delta_amba5_chk_errors", test_level)
