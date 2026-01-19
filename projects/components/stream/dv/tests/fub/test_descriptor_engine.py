# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_descriptor_engine
# Purpose: STREAM Descriptor Engine Test Runner - v1.0
#
# Documentation: projects/components/stream/PRD.md
# Subsystem: stream
#
# Author: sean galloway
# Created: 2025-10-19
# Updated: 2025-11-07 - Refactored to standard pattern

"""
STREAM Descriptor Engine Test Runner - v1.0

Tests APB→AXI→Descriptor flow only (no RDA/CDA interfaces in STREAM).

Test Types:
- 'apb_basic': Basic APB→AXI→Descriptor flow
- 'apb_with_delays': APB with various delay profiles (minimal delay)
- 'apb_fast_producer': APB with fast producer profile
- 'apb_backpressure': APB with backpressure

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.stream.dv.tbclasses.descriptor_engine_tb import DescriptorEngineTB, DelayProfile

# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_descriptor_engine(dut):
    """Unified descriptor engine test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'apb_basic': Basic APB→AXI→Descriptor flow
    - 'apb_with_delays': APB with various delay profiles (minimal delay)
    - 'apb_fast_producer': APB with fast producer profile
    - 'apb_backpressure': APB with backpressure
    """
    test_type = os.environ.get('TEST_TYPE', 'apb_basic')
    tb = DescriptorEngineTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Branch on test type
    if test_type == 'apb_basic':
        tb.log.info("=== Scenario DESC-ENG-01: Single descriptor fetch ===")
        tb.log.info("=== Also covers: DESC-ENG-08 (descriptor field extraction), DESC-ENG-10 (reset during fetch) ===")
        result = await tb.run_apb_basic_test(num_requests=5)
        report_pass = tb.generate_final_report()
        assert result and report_pass, "APB basic test failed"

    elif test_type == 'apb_with_delays':
        tb.log.info("=== Scenario DESC-ENG-02: Descriptor chain fetch ===")
        tb.log.info("=== Also covers: DESC-ENG-03 (last descriptor detection), DESC-ENG-06 (AXI AR channel stall), DESC-ENG-07 (AXI R channel stall) ===")
        # Test with minimal delay profile
        result = await tb.run_test_with_profile(num_packets=10, profile=DelayProfile.MINIMAL_DELAY)
        report_pass = tb.generate_final_report()
        assert result and report_pass, "APB minimal delay test failed"

    elif test_type == 'apb_fast_producer':
        tb.log.info("=== Scenario DESC-ENG-09: Rapid descriptor requests ===")
        result = await tb.run_test_with_profile(num_packets=8, profile=DelayProfile.FAST_PRODUCER)
        report_pass = tb.generate_final_report()
        assert result and report_pass, "APB fast producer test failed"

    elif test_type == 'apb_backpressure':
        tb.log.info("=== Scenario DESC-ENG-05: Backpressure from scheduler ===")
        tb.log.info("=== Also covers: DESC-ENG-04 (AXI read error handling) ===")
        result = await tb.run_test_with_profile(num_packets=8, profile=DelayProfile.BACKPRESSURE)
        report_pass = tb.generate_final_report()
        assert result and report_pass, "APB backpressure test failed"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_descriptor_engine_test_params():
    """Generate test parameters for descriptor engine tests.

    Returns:
        List of tuples: (test_type, channel_id, num_channels, addr_width, axi_id_width, fifo_depth)
    """
    test_types = ['apb_basic', 'apb_with_delays', 'apb_fast_producer', 'apb_backpressure']
    base_params = [
        # (channel_id, num_channels, addr_width, axi_id_width, fifo_depth)
        # Note: DATA_WIDTH removed - descriptor_engine.sv uses fixed 256-bit descriptors
        (0, 8, 64, 8, 8),  # Standard STREAM configuration
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params

descriptor_engine_params = generate_descriptor_engine_test_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, channel_id, num_channels, addr_width, axi_id_width, fifo_depth", descriptor_engine_params)
def test_descriptor_engine(request, test_type, channel_id, num_channels, addr_width, axi_id_width, fifo_depth, test_level):
    """Pytest wrapper for descriptor engine tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
        'rtl_stream_includes': '../../../../rtl/includes'
    })

    dut_name = "descriptor_engine"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/descriptor_engine.f'
    )

    # Format parameters for unique test name
    # Note: dw (data_width) removed - descriptor_engine.sv uses fixed 256-bit descriptors
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 3)
    aid_str = TBBase.format_dec(axi_id_width, 2)
    fd_str = TBBase.format_dec(fifo_depth, 2)
    test_name_plus_params = f"test_{dut_name}_{test_type}_cid{cid_str}_nc{nc_str}_aw{aw_str}_aid{aid_str}_fd{fd_str}"

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
        # DATA_WIDTH removed - descriptor_engine.sv uses fixed 256-bit descriptors
        'AXI_ID_WIDTH': axi_id_width,
        'FIFO_DEPTH': fifo_depth,
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
            testcase="cocotb_test_descriptor_engine",  # ← Single cocotb test
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
        print(f"✓ Descriptor engine {test_type} test completed! Logs: {log_path}")
    except Exception as e:
        print(f"❌ Descriptor engine {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
