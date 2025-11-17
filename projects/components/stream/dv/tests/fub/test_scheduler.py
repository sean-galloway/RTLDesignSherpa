# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler
# Purpose: STREAM Scheduler Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19
# Updated: 2025-11-07 - Refactored to standard pattern

"""
STREAM Scheduler Test Runner - v1.0

Test Types:
- 'basic_flow': Basic descriptor flow
- 'descriptor_chaining': Descriptor chaining (chain_length=3)
- 'descriptor_error': Descriptor error handling
- 'read_engine_error': Read engine error handling
- 'timeout_detection': Timeout detection

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import random

# Setup Python path BEFORE any other imports
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Now import utilities to get proper repo root
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

import pytest
import cocotb
from cocotb_test.simulator import run

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.stream.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=400, timeout_unit="ms")
async def cocotb_test_scheduler(dut):
    """Unified scheduler test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic_flow': Basic descriptor flow
    - 'descriptor_chaining': Descriptor chaining
    - 'descriptor_error': Descriptor error handling
    - 'read_engine_error': Read engine error handling
    - 'timeout_detection': Timeout detection
    - 'irq_generation': IRQ generation via MonBus
    - 'concurrent_read_write': Validate concurrent rd/wr (deadlock fix)
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_flow')
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Branch on test type
    if test_type == 'basic_flow':
        result = await tb.test_basic_descriptor_flow(num_descriptors=5)
        tb.generate_test_report()
        assert result, "Basic descriptor flow test failed"

    elif test_type == 'descriptor_chaining':
        result = await tb.test_descriptor_chaining(chain_length=3)
        tb.generate_test_report()
        assert result, "Descriptor chaining test failed"

    elif test_type == 'descriptor_error':
        result = await tb.test_descriptor_error()
        tb.generate_test_report()
        assert result, "Descriptor error test failed"

    elif test_type == 'read_engine_error':
        result = await tb.test_read_engine_error()
        tb.generate_test_report()
        assert result, "Read engine error test failed"

    elif test_type == 'timeout_detection':
        result = await tb.test_timeout_detection()
        tb.generate_test_report()
        assert result, "Timeout detection test failed"

    elif test_type == 'irq_generation':
        result = await tb.test_irq_generation()
        tb.generate_test_report()
        assert result, "IRQ generation test failed"

    elif test_type == 'concurrent_read_write':
        result = await tb.test_concurrent_read_write()
        tb.generate_test_report()
        assert result, "Concurrent read/write test failed"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests.

    Returns:
        List of tuples: (test_type, channel_id, num_channels, addr_width, data_width, timeout_cycles)
    """
    test_types = [
        'basic_flow',
        'descriptor_chaining',
        'descriptor_error',
        'read_engine_error',
        'timeout_detection',
        'irq_generation',
        'concurrent_read_write',  # NEW: Validate deadlock fix
    ]
    base_params = [
        # (channel_id, num_channels, addr_width, data_width, timeout_cycles)
        (0, 8, 64, 512, 1000),  # Standard STREAM configuration
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params

scheduler_params = generate_scheduler_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, channel_id, num_channels, addr_width, data_width, timeout_cycles", scheduler_params)
def test_scheduler(request, test_type, channel_id, num_channels, addr_width, data_width, timeout_cycles, test_level):
    """Pytest wrapper for scheduler tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_stream_includes': '../../../../rtl/includes'
    })

    dut_name = "scheduler"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/scheduler.f'
    )

    # Format parameters for unique test name
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    dw_str = TBBase.format_dec(data_width, 4)
    tc_str = TBBase.format_dec(timeout_cycles, 5)
    test_name_plus_params = f"test_{dut_name}_{test_type}_cid{cid_str}_nc{nc_str}_aw{aw_str}_dw{dw_str}_tc{tc_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'TIMEOUT_CYCLES': timeout_cycles,
    }

    extra_env = {
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'TEST_DEBUG': '0',
    }

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_scheduler",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
                "-Wno-TIMESCALEMOD",
            ],
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plusargs=[
                "--trace",
            ]
        )
        print(f"✓ Scheduler {test_type} test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Scheduler {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
