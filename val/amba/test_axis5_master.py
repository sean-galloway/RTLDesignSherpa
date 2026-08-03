# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axis5_master
# Purpose: Test runner for AXIS5 master with AMBA5 extensions
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-21

"""
AXIS5 Master Test Runner

Tests AXIS5 master functionality with AMBA5 extensions:
- TWAKEUP: Wake-up signaling
- TPARITY: Data parity protection
"""
import os
import random

import pytest
import cocotb
from cocotb.triggers import Timer, RisingEdge
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.axis5_master_tb import AXIS5MasterBasicTB
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_axis5_master_basic(dut):
    """Basic AXIS5 master test - verifies FUB to AXIS conversion."""
    tb = AXIS5MasterBasicTB(dut)

    # Setup
    await tb.setup_clocks_and_reset()

    # Configure slave side (drive TREADY high)
    dut.m_axis_tready.value = 1

    await tb.wait_clocks('aclk', 5)

    # Test 1: Basic data transfer
    tb.log.info("=== Test 1: Basic Data Transfer ===")
    await tb.drive_fub_packet(data=0x12345678, last=1)
    success = await tb.wait_for_transaction()
    assert success, "Data transfer timeout"
    await tb.wait_clocks('aclk', 10)

    # Test 2: Multiple packets
    tb.log.info("=== Test 2: Multiple Packets ===")
    for i in range(5):
        data = 0xABCD0000 + i
        await tb.drive_fub_packet(data=data, last=1, id=i)
        success = await tb.wait_for_transaction()
        assert success, f"Packet {i} timeout"
        await tb.wait_clocks('aclk', 5)

    # Test 3: Wakeup signaling (if enabled)
    tb.log.info("=== Test 3: Wakeup Signaling ===")
    if hasattr(dut, 'fub_axis_twakeup'):
        await tb.drive_fub_packet(data=0xFEED0001, last=1, wakeup=1)
        success = await tb.wait_for_transaction()
        assert success, "Wakeup transfer timeout"
        await tb.wait_clocks('aclk', 10)

    tb.log.info("=== AXIS5 Master Basic Test PASSED ===")


def generate_axis5_master_params():
    """Generate test parameters for AXIS5 master."""
    return [
        # skid_depth, data_width, id_width, dest_width, user_width, enable_wakeup, enable_parity
        (4, 32, 8, 4, 1, 1, 0),  # Basic with wakeup
        (4, 64, 8, 4, 1, 1, 0),  # 64-bit data
        (8, 32, 8, 4, 1, 1, 1),  # With parity
    ]


@pytest.mark.parametrize(
    "skid_depth, data_width, id_width, dest_width, user_width, enable_wakeup, enable_parity",
    generate_axis5_master_params()
)
def test_axis5_master(request, skid_depth, data_width, id_width, dest_width, user_width,
                      enable_wakeup, enable_parity):
    """AXIS5 master test runner."""
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axis5': 'rtl/amba/axis5',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    toplevel = "axis5_master"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/axis5_master.f")

    # Test identifier
    sd_str = TBBase.format_dec(skid_depth, 1)
    dw_str = TBBase.format_dec(data_width, 2)
    wk_str = 'wk' if enable_wakeup else 'nw'
    pr_str = 'pr' if enable_parity else 'np'
    test_name_plus_params = f"test_{worker_id}_axis5_master_sd{sd_str}_dw{dw_str}_{wk_str}_{pr_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)

    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    includes=includes

    # RTL parameters
    rtl_parameters = {
        'SKID_DEPTH': str(skid_depth),
        'AXIS_DATA_WIDTH': str(data_width),
        'AXIS_ID_WIDTH': str(id_width),
        'AXIS_DEST_WIDTH': str(dest_width),
        'AXIS_USER_WIDTH': str(user_width),
        'ENABLE_WAKEUP': str(enable_wakeup),
        'ENABLE_PARITY': str(enable_parity),
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': toplevel,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_SKID_DEPTH': str(skid_depth),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_DEST_WIDTH': str(dest_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_ENABLE_WAKEUP': str(enable_wakeup),
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

    try:
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
            testcase="cocotb_test_axis5_master_basic",
            simulator="verilator",
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
