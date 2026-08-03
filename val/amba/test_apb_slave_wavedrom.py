# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ComprehensiveAPBSlaveTB
# Purpose: Comprehensive APB Slave Test Suite
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Comprehensive APB Slave Test Suite

This enhanced test suite exercises all randomizer configurations and includes
extensive edge case testing for robust verification coverage.
"""

import os
import random
import itertools
from collections import deque

import pytest
import cocotb
from cocotb.utils import get_sim_time
from cocotb_test.simulator import run

from CocoTBFramework.components.shared.memory_model import MemoryModel
from CocoTBFramework.components.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.apb.apb_packet import APBTransaction, APBPacket
from CocoTBFramework.components.apb.apb_sequence import APBSequence
from CocoTBFramework.components.apb.apb_factories import \
    create_apb_master, create_apb_monitor, create_apb_scoreboard
from CocoTBFramework.components.gaxi.gaxi_factories import \
    create_gaxi_master, create_gaxi_slave, create_gaxi_monitor
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from TBClasses.apb.apbgaxiconfig import APBGAXIConfig
from TBClasses.amba.apb_slave_wavedrom_tb import ComprehensiveAPBSlaveTB
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard
from TBClasses.shared.tbbase import TBBase
from TBClasses.amba.amba_random_configs import (
    APB_MASTER_RANDOMIZER_CONFIGS,
    APB_SLAVE_RANDOMIZER_CONFIGS,
    AXI_RANDOMIZER_CONFIGS
)
from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Import WaveDrom components
from CocoTBFramework.components.wavedrom.constraint_solver import (
    TemporalConstraintSolver, ClockEdge
)
from CocoTBFramework.components.wavedrom.wavejson_gen import (
    WaveJSONGenerator, create_apb_wavejson_generator
)
from CocoTBFramework.components.wavedrom.utility import (
    create_temporal_annotations_from_solution, create_wavejson_from_packet_and_signals,
    get_apb_field_config
)
from TBClasses.wavedrom_user.apb import (
    APBPresets, APBDebug, APBConstraints,
    setup_apb_constraints_with_boundaries, get_apb_boundary_pattern
)




@cocotb.test(timeout_time=300, timeout_unit="us")  # Increased timeout for comprehensive tests
async def comprehensive_apb_slave_test(dut):
    """Comprehensive APB slave test with all randomizer configurations."""
    tb = ComprehensiveAPBSlaveTB(dut)

    # Set seed for reproducibility
    seed = int(os.environ.get('SEED', '42'))
    random.seed(seed)
    tb.log.info(f"Using seed: {seed}")

    # Start clock
    await tb.start_clock('pclk', 10, 'ns')

    # Reset DUT
    await tb.reset_dut()

    # Set up WaveDrom
    tb.setup_wavedrom(preset_type="comprehensive")

    # Start command handler
    await tb.cmd_handler.start()

    # Start WaveDrom sampling
    if tb.wave_solver:
        await tb.wave_solver.start_sampling()

    try:
        # Generate all APB waveform scenarios
        await tb.generate_all_wavedrom_scenarios()

        # Stop WaveDrom sampling and get results
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
            tb.wave_solver.debug_status()
            results = tb.wave_solver.get_results()

            tb.log.info(f"WaveDrom Results: {len(results['solutions'])} solutions, "
                       f"{results['satisfied_constraints']} satisfied, "
                       f"{results['failed_constraints']} failed")

            # Check if all required waveforms were generated
            if not results['all_required_satisfied']:
                tb.log.error(f"❌ NOT ALL REQUIRED WAVEFORMS GENERATED ❌")
                tb.log.error(f"Failed constraints: {results['failed_constraints']}")
                assert False, f"Required waveforms not generated: {results['failed_constraints']}"

        # Final verification
        final_result = await tb.verify_scoreboard(timeout=5000)

        if final_result:
            tb.log.info("🎉 APB WAVEDROM GENERATION COMPLETE! 🎉")
        else:
            tb.log.error("❌ APB WAVEDROM GENERATION FAILED ❌")
            assert False, "Waveform generation test failed"

    finally:
        # Clean shutdown
        tb.done = True
        if tb.wave_solver:
            await tb.wave_solver.stop_sampling()
        await tb.cmd_handler.stop()
        await tb.wait_clocks('pclk', 10)


# Keep the original test parameters
@pytest.mark.parametrize("addr_width, data_width, depth",
    [
        (32, 32, 2),
    ])
def test_comprehensive_apb_slave(request, addr_width, data_width, depth):
    """Comprehensive APB slave test with all configurations."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_slave.f")

    # Create test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'WAVEDROM_SHOW_STATUS': '1',
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # Disable FST tracing to avoid Verilator bug
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = []

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    sim_args = []
    plus_args = []

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
            waves=enable_waves,  # Disable waves to avoid Verilator FST bug
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
    except Exception as e:
        print(f"Comprehensive test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Comprehensive APB slave test with all configurations."""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba': 'rtl/amba', 'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "apb_slave"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path="rtl/amba/filelists/apb_slave.f")

    # Create test identifier
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    d_str = TBBase.format_dec(depth, 3)
    test_name_plus_params = f"test_{worker_id}_{dut_name}_aw{aw_str}_dw{dw_str}_d{d_str}_wd"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    rtl_parameters = {k.upper(): str(v) for k, v in locals().items() if k in ["addr_width", "data_width", "depth"]}

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'WAVEDROM_SHOW_STATUS': '1',
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_DEPTH': str(depth),
    }

    # Disable FST tracing to avoid Verilator bug
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = []

    # Add coverage compile args if COVERAGE=1
    compile_args.extend([])

    sim_args = []
    plus_args = []

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
            waves=enable_waves,  # Disable waves to avoid Verilator FST bug
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
    except Exception as e:
        print(f"Comprehensive test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
