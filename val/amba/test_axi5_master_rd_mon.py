# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi5_master_rd_mon
# Purpose: AXI5 Master Read Monitor Integration Test
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-20

"""
AXI5 Master Read Monitor Integration Test

Thin wrapper that uses the reusable AXI5MasterMonitorTB testbench class.
All test logic is in bin/CocoTBFramework/tbclasses/axi5/monitor/axi5_master_monitor_tb.py
"""

import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args

from CocoTBFramework.tbclasses.axi5.monitor.axi5_master_monitor_tb import AXI5MasterMonitorTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi5_master_rd_mon_test(dut):
    """AXI5 master read monitor integration test"""

    # Get test level
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    # Create testbench (is_write=False for read master)
    tb = AXI5MasterMonitorTB(dut, is_write=False, aclk=dut.aclk, aresetn=dut.aresetn)

    # Initialize
    await tb.initialize()

    # Run all integration tests
    await tb.run_integration_tests(test_level=test_level)


def generate_axi5_monitor_params():
    """
    Generate AXI5 monitor parameter combinations based on REG_LEVEL.

    Parameter tuple: (id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 9 tests - Comprehensive testing
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'basic'),
        ]
    elif reg_level == 'FUNC':
        params = [
            (8, 32, 32, 1, 16, 2, 4, 'basic'),
            (8, 32, 32, 1, 16, 4, 8, 'medium'),
            (8, 32, 32, 1, 32, 2, 4, 'medium'),
        ]
    else:  # FULL
        test_levels = ['basic', 'medium', 'full']
        configs = [
            (8, 32, 32, 1, 16, 2, 4),
            (8, 32, 32, 1, 16, 4, 8),
            (8, 32, 32, 1, 32, 2, 4),
        ]
        params = [
            (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r, level)
            for (id_w, addr_w, data_w, user_w, max_t, skid_ar, skid_r) in configs
            for level in test_levels
        ]

    return params


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level",
    generate_axi5_monitor_params()
)
def test_axi5_master_rd_mon(id_width, addr_width, data_width, user_width, max_trans, skid_ar, skid_r, test_level):
    """
    Integration test runner for AXI5 master read monitor.

    Controlled by REG_LEVEL environment variable:
        GATE: 1 test  - Quick smoke test
        FUNC: 3 tests - Functional validation (default)
        FULL: 9 tests - Comprehensive testing
    """

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi5': 'rtl/amba/axi5/',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_shared': 'rtl/amba/shared',
    })

    dut_name = "axi5_master_rd_mon"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_{dut_name}_iw{id_width}_aw{addr_width}_dw{data_width}_mt{max_trans}_sk{skid_ar}x{skid_r}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Verilog sources
    verilog_sources = [
        # Monitor packages (must be compiled in order)
        os.path.join(rtl_dict['rtl_includes'], "monitor_common_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba4_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_amba5_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_arbiter_pkg.sv"),
        os.path.join(rtl_dict['rtl_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_load_clear.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "counter_freq_invariant.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axi5'], "axi5_master_rd.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_trans_mgr.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timer.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_timeout.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_reporter.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_base.sv"),
        os.path.join(rtl_dict['rtl_shared'], "axi_monitor_filtered.sv"),
        os.path.join(rtl_dict['rtl_axi5'], f"{dut_name}.sv"),
    ]

    # Check files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    rtl_parameters = {
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'UNIT_ID': '1',
        'AGENT_ID': '10',
        'MAX_TRANSACTIONS': str(max_trans),
        'ENABLE_FILTERING': '1',
        'SKID_DEPTH_AR': str(skid_ar),
        'SKID_DEPTH_R': str(skid_r),
    }

    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_LEVEL': test_level,
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_STUB': '0',
        'SEED': str(random.randint(0, 100000)),
        'TEST_CLK_PERIOD': '10',
    }

    compile_args = [
        "-Wall", "-Wno-SYNCASYNCNET", "-Wno-UNUSED", "-Wno-DECLFILENAME", "-Wno-PINMISSING",
        "-Wno-UNDRIVEN", "-Wno-WIDTHEXPAND", "-Wno-WIDTHTRUNC",
        "-Wno-SELRANGE", "-Wno-CASEINCOMPLETE", "-Wno-TIMESCALEMOD",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    print(f"\n{'='*80}")
    print(f"AXI5 Master Read Monitor Integration Test")
    print(f"Test Level: {test_level}")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[rtl_dict['rtl_includes'], rtl_dict['rtl_common'], sim_build],
            toplevel=dut_name,
            module="test_axi5_master_rd_mon",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            simulator="verilator",
        )
        print(f"PASSED: {test_name}")
    except Exception as e:
        print(f"FAILED: {test_name}")
        print(f"Error: {str(e)}")
        raise
