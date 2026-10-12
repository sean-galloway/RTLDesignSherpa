# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_apb5_slave_cg
# Purpose: Test runner for APB5 slave clock-gated variant
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-23

"""
APB5 Slave Clock-Gated Test Runner

Tests APB5 slave with clock gating for power management.
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.apb5_wakeup import check_completer_cg_wakes_on_pwakeup
from TBClasses.amba.apb5_slave_cg_tb import APB5SlaveCGBasicTB
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_apb5_slave_cg_basic(dut):
    """Basic APB5 slave clock-gated test."""
    tb = APB5SlaveCGBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Configure idle count
    dut.cfg_cg_idle_count.value = 8

    # Initialize APB signals
    dut.s_apb_PSEL.value = 0
    dut.s_apb_PENABLE.value = 0
    dut.s_apb_PADDR.value = 0
    dut.s_apb_PWRITE.value = 0
    dut.s_apb_PWDATA.value = 0
    dut.s_apb_PSTRB.value = 0xF
    dut.s_apb_PPROT.value = 0

    if hasattr(dut, 's_apb_PAUSER'):
        dut.s_apb_PAUSER.value = 0
    if hasattr(dut, 's_apb_PWUSER'):
        dut.s_apb_PWUSER.value = 0

    # Initialize response interface (backend ready)
    dut.cmd_ready.value = 1
    dut.rsp_valid.value = 0
    dut.rsp_prdata.value = 0
    dut.rsp_pslverr.value = 0

    if hasattr(dut, 'rsp_pruser'):
        dut.rsp_pruser.value = 0
    if hasattr(dut, 'rsp_pbuser'):
        dut.rsp_pbuser.value = 0

    # Wake-up control
    dut.s_apb_PWAKEUP.value = 0

    # Test clock gating enable/disable
    tb.log.info("=== Test: Clock Gating Control ===")

    # Disable clock gating first
    await tb.enable_clock_gating(False)
    await tb.wait_clocks('pclk', 10)

    # Enable clock gating
    await tb.enable_clock_gating(True)
    await tb.wait_clocks('pclk', 20)

    # Disable clock gating
    await tb.enable_clock_gating(False)
    await tb.wait_clocks('pclk', 10)

    tb.log.info("=== APB5 Slave CG Basic Test PASSED ===")


@cocotb.test(timeout_time=200, timeout_unit="us")
async def cocotb_test_apb5_slave_cg_pwakeup_wake(dut):
    """PWAKEUP is a Requester output and a clock-controller input (IHI
    0024E 3.7.1/3.7.2; issue #102 item 7): with gating closed, PWAKEUP alone
    -- no PSEL -- must open the gate and hold it open. The pre-fix RTL had
    s_apb_PWAKEUP as a slave OUTPUT, so it could not wake on it."""
    tb = APB5SlaveCGBasicTB(dut)
    for name in ('s_apb_PSEL', 's_apb_PENABLE', 's_apb_PADDR', 's_apb_PWRITE',
                 's_apb_PWDATA', 's_apb_PSTRB', 's_apb_PPROT', 's_apb_PAUSER',
                 's_apb_PWUSER', 's_apb_PWAKEUP', 'cmd_ready', 'rsp_valid',
                 'rsp_prdata', 'rsp_pslverr', 'rsp_pruser', 'rsp_pbuser',
                 'cfg_cg_enable'):
        getattr(dut, name).value = 0
    dut.cfg_cg_idle_count.value = 4
    await tb.setup_clocks_and_reset()
    await check_completer_cg_wakes_on_pwakeup(dut, tb.log)


def generate_apb5_slave_cg_params():
    """Generate test parameters for APB5 slave clock-gated."""
    return [
        (12, 32, 4, 0),  # Basic
        (16, 32, 8, 0),  # 16-bit address
        (12, 64, 4, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "addr_width, data_width, auser_width, enable_parity",
    generate_apb5_slave_cg_params()
)
def test_apb5_slave_cg(request, addr_width, data_width, auser_width, enable_parity):
    """APB5 slave clock-gated test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_apb5': 'rtl/amba/apb5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_shared': 'rtl/amba/shared',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "apb5_slave_cg"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='apb5_slave_cg')

    # Test identifier
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    au_str = TBBase.format_dec(auser_width, 1)
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = f"test_{worker_id}_apb5_slave_cg_aw{aw_str}_dw{dw_str}_au{au_str}_{pr_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AUSER_WIDTH': str(auser_width),
        'WUSER_WIDTH': str(auser_width),
        'RUSER_WIDTH': str(auser_width),
        'BUSER_WIDTH': str(auser_width),
        'ENABLE_PARITY': str(enable_parity),
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AUSER_WIDTH': str(auser_width),
        'TEST_ENABLE_PARITY': str(enable_parity),
    }

    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # One run() per cocotb test: a comma-joined testcase string selects
    # nothing under the conftest exact-name anchor (BUG-015 patch).
    testcases = ["cocotb_test_apb5_slave_cg_basic", "cocotb_test_apb5_slave_cg_pwakeup_wake"]
    try:
        for testcase in testcases:
            run(
                python_search=[tests_dir],
                verilog_sources=verilog_sources,
                includes=includes,
                toplevel=toplevel,
                module=module,
                parameters=rtl_parameters,
                sim_build=sim_build,
                extra_env=extra_env,
                waves=enable_waves,
                plus_args=(['--trace'] if enable_waves else []),
                keep_files=True,
                compile_args=compile_args,
                testcase=testcase,
                simulator="verilator",
            )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
