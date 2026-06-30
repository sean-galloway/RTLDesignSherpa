"""
Test runner for stream_latency_bridge module

Verifies:
1. Occupancy tracking (0, 1, 2 beats in pipeline)
2. Data integrity through pipeline
3. Backpressure handling

Test Types:
- 'occupancy': Occupancy tracking with 4-deep skid buffer
- 'streaming': Streaming flow with occupancy verification
- 'backpressure': Backpressure when 4-deep skid buffer fills

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)

Author: RTL Design Sherpa
Created: 2025-11-06
Updated: 2025-11-07 - Refactored to standard pattern
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from TBClasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import testbench
from projects.components.stream.dv.tbclasses.stream_latency_bridge_tb import StreamLatencyBridgeTB

# Coverage integration
from projects.components.stream.dv.stream_coverage import (
    CoverageHelper,
    get_coverage_compile_args,
)


#===============================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
#
# All occupancy / streaming / backpressure stimulus + checking lives in the TB
# (StreamLatencyBridgeTB), which drives the s/m interfaces through GAXI BFMs.
# This runner only dispatches by TEST_TYPE and handles coverage sampling.
#===============================================================================

async def run_full_protocol_coverage_test(tb, coverage):
    """Sample ALL protocol coverage points for 100% protocol coverage"""
    tb.log.info("=== Comprehensive Protocol Coverage Test ===")

    # Run basic streaming test first
    occupancies = await tb.test_streaming(num_beats=10)

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


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_stream_latency_bridge(dut):
    """Unified stream latency bridge test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'occupancy': Occupancy tracking with 4-deep skid buffer
    - 'streaming': Streaming flow with occupancy verification
    - 'backpressure': Backpressure when 4-deep skid buffer fills
    - 'full_protocol_coverage': Sample ALL protocol coverage points
    """
    test_type = os.environ.get('TEST_TYPE', 'occupancy')
    test_name = os.environ.get('COVERAGE_TEST_NAME', f'stream_latency_bridge_{test_type}')

    # Initialize coverage collector
    coverage = CoverageHelper(test_name)

    tb = StreamLatencyBridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'occupancy':
        tb.log.info("=== Scenario LATENCY-BRIDGE-05: Buffer empty condition ===")
        tb.log.info("=== Also covers: LATENCY-BRIDGE-04 (buffer full condition), LATENCY-BRIDGE-09 (reset during transfer) ===")
        await tb.test_occupancy()
        coverage.sample_handshake("backpressure_stall")

    elif test_type == 'streaming':
        tb.log.info("=== Scenario LATENCY-BRIDGE-01: Basic streaming transfer ===")
        tb.log.info("=== Also covers: LATENCY-BRIDGE-06 (burst transfer), LATENCY-BRIDGE-07 (variable latency compensation), LATENCY-BRIDGE-08 (data integrity) ===")
        await tb.test_streaming()
        coverage.sample_scenario("back_to_back")
        coverage.sample_handshake("mem_data_valid_ready")

    elif test_type == 'backpressure':
        tb.log.info("=== Scenario LATENCY-BRIDGE-02: Upstream backpressure ===")
        tb.log.info("=== Also covers: LATENCY-BRIDGE-03 (downstream stall) ===")
        await tb.test_backpressure()
        coverage.sample_scenario("backpressure")
        coverage.sample_handshake("backpressure_stall")

    elif test_type == 'full_protocol_coverage':
        await run_full_protocol_coverage_test(tb, coverage)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    # Save coverage at end of test
    coverage.save()


#===============================================================================
# PARAMETER GENERATION
#===============================================================================

def generate_params():
    """
    Generate parameters for latency bridge tests based on REG_LEVEL.

    GATE: 1 test (256-bit)
    FUNC: 2 tests (256-bit, 512-bit)
    FULL: 3 tests (128-bit, 256-bit, 512-bit)

    Returns:
        List of tuples: (test_type, data_width)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal smoke test
        data_widths = [256]
        sweep_profiles = []
    elif reg_level == 'FUNC':
        # Functional coverage
        data_widths = [256, 512]
        sweep_profiles = ['slow_producer', 'gaxi_backpressure', 'gaxi_realistic']
    else:  # FULL
        # Comprehensive
        data_widths = [128, 256, 512]
        sweep_profiles = ['constrained', 'slow_producer', 'high_throughput',
                          'gaxi_backpressure', 'gaxi_stress', 'gaxi_realistic']

    # Generate params for all test types at the default (back-to-back) profile.
    test_types = ['occupancy', 'streaming', 'backpressure', 'full_protocol_coverage']
    params = []
    for test_type in test_types:
        for data_width in data_widths:
            params.append((test_type, data_width, 'default'))
    # Profile sweep on the occupancy/streaming/backpressure types at 256-bit
    # (full_protocol_coverage is coverage-only, no need to sweep timing).
    for test_type in ['occupancy', 'streaming', 'backpressure']:
        for profile in sweep_profiles:
            params.append((test_type, 256, profile))

    return params


params = generate_params()


#===============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#===============================================================================

@pytest.mark.parametrize("test_type, data_width, timing_profile", params)
def test_stream_latency_bridge(request, test_type, data_width, timing_profile):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Pytest wrapper for stream latency bridge tests - handles all test types."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "stream_latency_bridge"

    # Format parameter for unique test name (xdist compatibility)
    dw_str = f"{data_width:04d}"
    test_name = f"test_latency_bridge_{test_type}_dw{dw_str}_{timing_profile}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/stream_latency_bridge.f'
    )

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # Create log and results paths
    log_path = os.path.join(log_dir, f'{test_name}.log')
    results_path = os.path.join(log_dir, f'results_{test_name}.xml')

    parameters = {'DATA_WIDTH': str(data_width)}

    extra_env = {
        'TEST_TYPE': test_type,  # ← Pass test type to cocotb
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
    }
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    compile_args = ['-Wno-TIMESCALEMOD', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

    # Enable VCD waveforms if WAVES=1 (not FST, which has Verilator bugs)
    # We need to temporarily unset WAVES to prevent cocotb-test from auto-adding FST
    waves_requested = bool(int(os.environ.get('WAVES', '0')))
    if waves_requested:
        compile_args.extend(['--trace', '--trace-structs', '--trace-max-array', '512'])
        # Temporarily hide WAVES from cocotb-test
        waves_value = os.environ.pop('WAVES', None)

    # Create view command helper script
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name)

    run(
        python_search=[tests_dir, os.path.join(repo_root, 'projects/components/stream/dv/tbclasses')],
        verilog_sources=verilog_sources,
        includes=includes,
        toplevel=dut_name,
        module=module,
        testcase="cocotb_test_stream_latency_bridge",  # ← Single cocotb test
        parameters=parameters,
        sim_build=sim_build,
        results_xml=results_path,
        simulator='verilator',
        compile_args=compile_args,
        extra_env=extra_env,
        waves=enable_waves,
        plus_args=['--trace'] if enable_waves else [],
    )

    # Restore WAVES if it was set
    if waves_requested and waves_value is not None:
        os.environ['WAVES'] = waves_value

    print(f"✓ Stream latency bridge {test_type} test completed! Logs: {log_path}")
    if coverage_compile_args:
        print(f"  Coverage data saved for: {test_name}")
