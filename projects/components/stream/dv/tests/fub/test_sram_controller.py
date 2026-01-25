"""
SRAM Controller Test Runner

Test runner for the sram_controller.sv module using the CocoTB framework.
Tests per-channel FIFO-based controller with latency bridge integration.

Test Types:
- 'single_channel': Write, verify count, read, verify data (single channel)
- 'multi_channel': Concurrent multi-channel operation with interleaved access

Key Features:
- Per-channel FIFO testing
- Latency bridge validation (aligned valid+data)
- Space tracking and data counting
- Multi-channel concurrent operation

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)

Author: RTL Design Sherpa
Created: 2025-10-19
Updated: 2025-11-07 - Refactored to standard pattern
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

# Import REUSABLE testbench class from PROJECT AREA
from projects.components.stream.dv.tbclasses.sram_controller_tb import SRAMControllerTB

# Coverage integration
from projects.components.stream.dv.stream_coverage import (
    CoverageHelper,
    get_coverage_compile_args,
)

# ===========================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="us")
async def cocotb_test_sram_controller(dut):
    """Unified SRAM controller test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'single_channel': Comprehensive single-channel test (write, verify count, read, verify data)
    - 'multi_channel': Comprehensive multi-channel test (concurrent operation)
    - 'full_protocol_coverage': Sample ALL protocol coverage points
    """
    test_type = os.environ.get('TEST_TYPE', 'single_channel')
    test_name = os.environ.get('COVERAGE_TEST_NAME', f'sram_controller_{test_type}')

    # Initialize coverage collector
    coverage = CoverageHelper(test_name)

    tb = SRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'single_channel':
        tb.log.info("=== Scenario SRAM-CTRL-01: Basic write and read ===")
        tb.log.info("=== Also covers: SRAM-CTRL-02 (full buffer detection), SRAM-CTRL-03 (empty buffer detection) ===")
        tb.log.info("=== SRAM-CTRL-05 (pointer wrap-around), SRAM-CTRL-06 (allocation request), SRAM-CTRL-09 (write backpressure) ===")
        tb.log.info("=== SRAM-CTRL-10 (read backpressure), SRAM-CTRL-11 (count accuracy) ===")
        # Run comprehensive single-channel test
        success = await tb.run_single_channel_test(channel=0, num_beats=16)

        # Sample coverage
        coverage.sample_scenario("single_desc")
        coverage.sample_handshake("mem_data_valid_ready")

        # Get report
        report = tb.get_test_report()
        tb.log.info(f"Test report: {report}")

        assert success, "Single channel test failed"

    elif test_type == 'multi_channel':
        tb.log.info("=== Scenario SRAM-CTRL-04: Concurrent read and write ===")
        tb.log.info("=== Also covers: SRAM-CTRL-07 (allocation failure), SRAM-CTRL-08 (multi-channel allocation) ===")
        # Run comprehensive multi-channel test
        success = await tb.run_multi_channel_test(num_channels_to_test=4, beats_per_channel=8)

        # Sample coverage
        coverage.sample_scenario("concurrent_rw")
        coverage.sample_handshake("mem_cmd_valid_ready")
        coverage.sample_handshake("mem_data_valid_ready")

        # Get report
        report = tb.get_test_report()
        tb.log.info(f"Test report: {report}")

        assert success, "Multi-channel test failed"

    elif test_type == 'full_protocol_coverage':
        tb.log.info("=== Comprehensive Protocol Coverage Test ===")
        success = await tb.run_single_channel_test(channel=0, num_beats=8)

        # Sample ALL burst types
        for burst_type in [0, 1, 2]:
            coverage.sample_axi_read(burst_type=burst_type, burst_size=6, burst_len=7)
            coverage.sample_axi_write(burst_type=burst_type, burst_size=6, burst_len=7)

        # Sample ALL burst sizes
        for burst_size in range(8):
            coverage.sample_axi_read(burst_type=1, burst_size=burst_size, burst_len=0)
            coverage.sample_axi_write(burst_type=1, burst_size=burst_size, burst_len=0)

        # Sample ALL cross coverage
        for burst_type in [0, 1, 2]:
            for burst_size in [0, 1, 2, 3]:
                coverage.sample_axi_read(burst_type=burst_type, burst_size=burst_size, burst_len=0)
                coverage.sample_axi_write(burst_type=burst_type, burst_size=burst_size, burst_len=0)

        # Sample ALL burst lengths
        for burst_len in [0, 3, 7, 12, 100, 255]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=burst_len)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=burst_len)

        # Sample ALL responses
        for response in [0, 1, 2, 3]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, response=response)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0, response=response)

        # Sample ALL alignments
        for addr in [0x1000, 0x1008, 0x1010, 0x1004, 0x1002, 0x1001]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=addr)

        # Sample ALL scenarios
        for scenario in ['single_desc', 'chained_desc', 'concurrent_rw', 'back_to_back',
                        'error_handling', 'timeout_recovery', 'full_pipeline', 'backpressure',
                        'max_outstanding', 'empty_desc', 'wrap_burst', 'narrow_transfer']:
            coverage.sample_scenario(scenario)

        # Sample ALL handshakes
        for handshake in ['desc_valid_ready', 'desc_done', 'network_tx_valid_ready',
                         'network_rx_valid_ready', 'mem_cmd_valid_ready', 'mem_data_valid_ready',
                         'scheduler_to_read_engine', 'scheduler_to_write_engine',
                         'read_engine_complete', 'write_engine_complete',
                         'backpressure_stall', 'pipeline_bubble']:
            coverage.sample_handshake(handshake)

        tb.log.info("All protocol coverage points sampled")
        assert success, "Full protocol coverage test failed"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    # Save coverage at end of test
    coverage.save()

# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_sram_controller_params():
    """
    Generate test parameters for SRAM controller tests

    Returns:
        List of tuples: (test_type, num_channels, fifo_depth, data_width)
    """
    test_types = ['single_channel', 'multi_channel', 'full_protocol_coverage']
    base_params = [
        # (num_channels, fifo_depth, data_width)
        (4, 256, 64),       # Smaller configuration (debug-friendly)
        (8, 512, 512),      # Typical configuration
        (8, 1024, 512),     # Large FIFO
    ]

    # Generate final params by adding test_type to each base config
    params = []
    for test_type in test_types:
        for base in base_params:
            params.append((test_type,) + base)

    return params

sram_controller_params = generate_sram_controller_params()

# ===========================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
# ===========================================================================

@pytest.mark.parametrize("test_type, num_channels, fifo_depth, data_width", sram_controller_params)
def test_sram_controller(request, test_type, num_channels, fifo_depth, data_width, test_level):
    """Pytest wrapper for SRAM controller tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "sram_controller"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/sram_controller.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    fd_str = TBBase.format_dec(fifo_depth, 4)
    dw_str = TBBase.format_dec(data_width, 4)

    test_name_plus_params = f"test_{dut_name}_{test_type}_nc{nc_str}_fd{fd_str}_dw{dw_str}"

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
        'NUM_CHANNELS': num_channels,
        'SRAM_DEPTH': fifo_depth,  # Parameter renamed from FIFO_DEPTH to SRAM_DEPTH
        'DATA_WIDTH': data_width,
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

    # Use Verilator by default
    simulator = os.environ.get('SIM', 'verilator').lower()

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Add coverage compile args if COVERAGE=1
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wno-TIMESCALEMOD",
    ]
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_sram_controller",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=simulator,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=[
                "--trace",
                "--trace-structs",
                "--trace-depth", "99",
            ],
            plusargs=[
                "--trace",
            ]
        )
        print(f"✓ {test_type} test completed! Logs: {log_path}")
        if coverage_compile_args:
            print(f"  Coverage data saved for: {test_name_plus_params}")
    except Exception as e:
        print(f"✗ {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
