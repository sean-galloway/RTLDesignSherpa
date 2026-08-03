# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBSlaveCDCCGTB
# Purpose: Enhanced APB-GAXI CDC testbench with comprehensive clock gating testing and vali
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import random
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import create_apb_master, create_apb_monitor
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from TBClasses.apb.apbgaxiconfig import APBGAXIConfig
from TBClasses.amba.apb_slave_cdc_cg_tb import APBSlaveCDCCGTB
from TBClasses.amba.amba_cg_ctrl import AxiClockGateCtrl
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=90, timeout_unit="ms")  # Longer timeout for clock gating tests
async def comprehensive_apb_cdc_cg_test(dut):
    """Comprehensive APB-GAXI CDC + Clock Gating test with cross-domain and power validation."""

    tb = APBSlaveCDCCGTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using CDC + Clock Gating test seed: {seed}")

    # Start both clocks for CDC testing
    await tb.start_clock('aclk',  1, 'ns')  # Fast AXI clock - 1GHz
    await tb.start_clock('pclk', 10, 'ns')  # Slower APB clock - 100MHz

    # Reset DUT with CDC + Clock Gating specific reset sequence
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:
        # First run the basic CDC + Clock Gating comprehensive test
        result = await tb.run_cdc_cg_comprehensive_test()

        if result:
            tb.log.info("🎉 APB-GAXI CDC + CLOCK GATING BASIC TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI CDC + CLOCK GATING BASIC TEST FAILED ❌")
            tb.log.error("Check the detailed CDC + Clock Gating analysis above to identify issues")
            assert False, "APB-GAXI CDC + Clock Gating basic test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_cdc_cg_test_suite()

        # Final verification with CDC + Clock Gating timing
        final_result = await tb.verify_scoreboard(timeout=8000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE CDC + CLOCK GATING TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE CDC + CLOCK GATING TEST SUITE FAILED ❌")
            assert False, f"CDC + Clock Gating test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        # Final CDC + Clock Gating synchronization wait
        await tb.wait_clocks('aclk', 30)
        await tb.wait_clocks('pclk', 30)


@pytest.mark.parametrize("addr_width, data_width, depth, cg_idle_count_width", [(32, 32, 2, 4), (32, 32, 2, 12)])
def test_apb_slave_cdc_cg_robust(request, addr_width, data_width, depth, cg_idle_count_width):
    """Robust APB-GAXI CDC + Clock Gating test with comprehensive validation."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':        'rtl/common',
        'rtl_amba':       'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_amba_cdc': 'rtl/amba/cdc',
        'rtl_apb':        'rtl/amba/apb',
        'rtl_gaxi':       'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc_cg"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_slave_cdc_cg.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cg_str = TBBase.format_dec(cg_idle_count_width, 2)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_cg{cg_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth", "cg_idle_count_width"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CG_IDLE_COUNT_WIDTH': str(cg_idle_count_width),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-max-width", "512",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plus_args = ["--trace"]

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
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )

        print(f"✓ APB-GAXI CDC + Clock Gating robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Clock Gating Analysis Available in Logs")

    except Exception as e:
        print(f"❌ APB-GAXI CDC + Clock Gating robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC + Clock Gating analysis.")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Robust APB-GAXI CDC + Clock Gating test with comprehensive validation."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn':        'rtl/common',
        'rtl_amba':       'rtl/amba',
        'rtl_amba_shared':'rtl/amba/shared',
        'rtl_amba_cdc': 'rtl/amba/cdc',
        'rtl_apb':        'rtl/amba/apb',
        'rtl_gaxi':       'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave_cdc_cg"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_slave_cdc_cg.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    cg_str = TBBase.format_dec(cg_idle_count_width, 2)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_cg{cg_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth", "cg_idle_count_width"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
        'TEST_CG_IDLE_COUNT_WIDTH': str(cg_idle_count_width),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
        "--trace-max-width", "512",
    ]


    # Add coverage compile args if COVERAGE=1

    compile_args.extend([])


    sim_args = [
        "--trace",
        
        "--trace-depth", "99",
    ]

    plus_args = ["--trace"]

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
            waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )

        print(f"✓ APB-GAXI CDC + Clock Gating robust test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Clock Gating Analysis Available in Logs")

    except Exception as e:
        print(f"❌ APB-GAXI CDC + Clock Gating robust test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed CDC + Clock Gating analysis.")
        raise
