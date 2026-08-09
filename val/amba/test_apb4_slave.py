# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: APBGAXIDebugTB
# Purpose: APB-GAXI Debug testbench - focus on finding refactor issues.
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
from TBClasses.amba.apb4_slave_tb import APBGAXIDebugTB
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist




@cocotb.test(timeout_time=300, timeout_unit="us")  # Increased timeout for comprehensive tests
async def comprehensive_apb_gaxi_test(dut):
    """Comprehensive APB-GAXI test with all sequences."""

    tb = APBGAXIDebugTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('pclk', 10, 'ns')

    # Reset DUT
    await tb.reset_dut()

    # Start command handler
    await tb.cmd_handler.start()

    try:

        # Simple refactor debug test
        result = await tb.run_refactor_debug_test()

        if result:
            tb.log.info("🎉 APB-GAXI DEBUG TEST PASSED! 🎉")
        else:
            tb.log.error("❌ APB-GAXI DEBUG TEST FAILED ❌")
            tb.log.error("Check the detailed analysis above to identify refactor issues")
            assert False, "APB-GAXI debug test failed"

        # Run comprehensive test suite
        await tb.run_comprehensive_test_suite()

        # Final verification
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result and tb.test_stats['failed_tests'] == 0:
            tb.log.info("🎉 COMPREHENSIVE TEST SUITE PASSED! 🎉")
        else:
            tb.log.error("❌ COMPREHENSIVE TEST SUITE FAILED ❌")
            assert False, f"Test suite failed: {tb.test_stats['failed_tests']} failed tests"

    finally:
        # Clean shutdown
        tb.done = True
        await tb.cmd_handler.stop()
        await tb.wait_clocks('pclk', 10)


@pytest.mark.parametrize("addr_width, data_width, depth", [(32, 32, 2)])
def test_apb_gaxi_refactor_debug(request, addr_width, data_width, depth):
    """APB-GAXI refactor debug test."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba': 'rtl/amba'
    , 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb4_slave"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb4_slave.f")

    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    rtl_parameters = {
        k.upper(): str(v) for k, v in locals().items()
        if k in ["addr_width", "data_width", "depth"]
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'DEBUG',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(42),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "--trace-max-array", "1024",
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

        print(f"✓ APB-GAXI refactor debug test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")

    except Exception as e:
        print(f"❌ APB-GAXI refactor debug test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        print(f"Check the log file for detailed refactor issue analysis.")
        raise


