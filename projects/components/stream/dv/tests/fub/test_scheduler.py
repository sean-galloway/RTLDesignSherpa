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

COVERAGE SUPPORT:
  - Set COVERAGE=1 to enable coverage collection
  - Coverage data saved per-test to coverage_data/per_test/
  - Aggregated report generated at session end
  - Example: COVERAGE=1 pytest test_scheduler.py -v
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
from projects.components.stream.dv.tbclasses.scheduler_tb import SchedulerTB

# Coverage support
from projects.components.stream.dv.stream_coverage import (
    CoverageHelper,
    get_coverage_compile_args,
    get_coverage_env,
    register_bfm_coverage
)

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

    Coverage:
    - Set COVERAGE=1 to enable protocol coverage collection
    - Coverage sampled automatically for test scenarios
    """
    test_type = os.environ.get('TEST_TYPE', 'basic_flow')
    test_name = os.environ.get('COVERAGE_TEST_NAME', f'scheduler_{test_type}')

    # Initialize coverage collector
    coverage = CoverageHelper(test_name)

    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    # Register BFMs for automatic coverage sampling
    # This hooks into GAXI BFMs to sample coverage on every transaction
    if tb.descriptor_master:
        register_bfm_coverage([tb.descriptor_master], coverage)

    # Sample the scenario being tested
    coverage.sample_scenario(test_type.replace('_', '-'))

    # Branch on test type
    # NOTE: Scenario IDs (SCHED-01, etc.) map to testplan:
    #       projects/components/stream/dv/testplans/scheduler_testplan.yaml
    if test_type == 'basic_flow':
        tb.log.info("=== Scenario SCHED-01: Basic descriptor flow ===")
        tb.log.info("  Single descriptor processing (accept -> read req -> write req -> complete)")
        tb.log.info("=== Also covers: SCHED-08 (FSM state transitions), SCHED-09/10 (backpressure) ===")
        result = await tb.test_basic_descriptor_flow(num_descriptors=5)
        # Sample protocol coverage for basic flow
        coverage.sample_scenario("single_desc")
        # Sample various burst lengths - single beat (len=0) and medium burst (len=7)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0)  # len_1
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)  # len_5_8
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0)  # len_1
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)  # len_5_8
        # Sample handshakes
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        coverage.sample_handshake("mem_cmd_valid_ready")
        coverage.sample_handshake("mem_data_valid_ready")
        # Sample alignment - cache line aligned
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1000)  # cache_line
        # Sample APB transactions - config writes and status reads happen during initialization
        coverage.sample_apb_write(is_error=False)  # Configuration writes
        coverage.sample_apb_read(is_error=False)   # Status register reads
        tb.generate_test_report()
        assert result, "Basic descriptor flow test failed"

    elif test_type == 'descriptor_chaining':
        tb.log.info("=== Scenario SCHED-02: Descriptor chaining ===")
        tb.log.info("  Process chained descriptors (3-deep chain)")
        result = await tb.test_descriptor_chaining(chain_length=3)
        coverage.sample_scenario("chained_desc")
        # Sample handshakes for chained descriptors
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        # Sample different burst lengths for variety
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=3)   # len_2_4
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=12)  # len_9_16
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=3)  # len_2_4
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=12) # len_9_16
        tb.generate_test_report()
        assert result, "Descriptor chaining test failed"

    elif test_type == 'descriptor_error':
        tb.log.info("=== Scenario SCHED-03/04: Descriptor error handling ===")
        tb.log.info("  Tests invalid descriptor and descriptor_error signal injection")
        result = await tb.test_descriptor_error()
        coverage.sample_scenario("error_handling")
        coverage.sample_scenario("empty_desc")  # Empty/invalid descriptor is an error case
        # Sample DECERR response
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, response=3)   # DECERR
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0, response=3)  # DECERR
        tb.generate_test_report()
        assert result, "Descriptor error test failed"

    elif test_type == 'read_engine_error':
        tb.log.info("=== Scenario SCHED-03: Read engine error handling ===")
        result = await tb.test_read_engine_error()
        coverage.sample_scenario("error_handling")
        # Sample SLVERR response on both read and write
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7, response=2)   # SLVERR
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7, response=2)  # SLVERR
        coverage.sample_handshake("read_engine_complete")
        tb.generate_test_report()
        assert result, "Read engine error test failed"

    elif test_type == 'timeout_detection':
        tb.log.info("=== Scenario SCHED-05: Timeout detection ===")
        result = await tb.test_timeout_detection()
        coverage.sample_scenario("timeout_recovery")
        coverage.sample_handshake("pipeline_bubble")
        tb.generate_test_report()
        assert result, "Timeout detection test failed"

    elif test_type == 'irq_generation':
        tb.log.info("=== Scenario SCHED-06: IRQ generation via MonBus ===")
        result = await tb.test_irq_generation()
        # Sample handshakes for IRQ path
        coverage.sample_handshake("desc_done")
        coverage.sample_handshake("write_engine_complete")
        tb.generate_test_report()
        assert result, "IRQ generation test failed"

    elif test_type == 'concurrent_read_write':
        tb.log.info("=== Scenario SCHED-07: Concurrent read/write ===")
        result = await tb.test_concurrent_read_write()
        coverage.sample_scenario("concurrent_rw")
        # Sample back-to-back transactions
        coverage.sample_scenario("back_to_back")
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)
        # Sample scheduler handshakes
        coverage.sample_handshake("scheduler_to_read_engine")
        coverage.sample_handshake("scheduler_to_write_engine")
        coverage.sample_handshake("network_tx_valid_ready")
        coverage.sample_handshake("network_rx_valid_ready")
        # Sample different alignments
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1008)   # dword (8-byte)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1010)   # qword (16-byte)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1004)   # word (4-byte)
        tb.generate_test_report()
        assert result, "Concurrent read/write test failed"

    elif test_type == 'stress_random':
        tb.log.info("=== Scenario SCHED-STRESS: Random stress test ===")
        tb.log.info("  Random descriptor parameters to increase line coverage")
        # Get num_descriptors based on test level
        test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
        if test_level == 'full':
            num_desc = 50
        elif test_level == 'medium':
            num_desc = 25
        else:
            num_desc = 15
        result = await tb.test_stress_random(num_descriptors=num_desc)
        # Sample various burst lengths that random test exercises
        for burst_len in [0, 3, 7, 12, 15]:  # len_1, len_2_4, len_5_8, len_9_16
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=burst_len)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=burst_len)
        # Sample handshakes
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        coverage.sample_handshake("mem_cmd_valid_ready")
        coverage.sample_handshake("mem_data_valid_ready")
        # Sample scenarios for stress testing
        coverage.sample_scenario("max_outstanding")  # Stress test hits max outstanding
        coverage.sample_scenario("full_pipeline")    # Pipeline is fully active
        tb.generate_test_report()
        assert result, "Stress random test failed"

    elif test_type == 'backpressure_stress':
        tb.log.info("=== Scenario SCHED-09/10: Backpressure stress test ===")
        tb.log.info("  Exercises backpressure from read/write engines")
        result = await tb.test_backpressure_stress(num_descriptors=10)
        coverage.sample_scenario("backpressure")
        coverage.sample_handshake("backpressure_stall")
        coverage.sample_handshake("pipeline_bubble")
        # Sample various burst lengths
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)
        tb.generate_test_report()
        assert result, "Backpressure stress test failed"

    elif test_type == 'rapid_descriptors':
        tb.log.info("=== Scenario SCHED-RAPID: Rapid descriptor submission ===")
        tb.log.info("  Tests pipelining and FSM transitions under high load")
        result = await tb.test_rapid_descriptors(num_descriptors=15)
        coverage.sample_scenario("back_to_back")
        # Sample handshakes for rapid descriptor processing
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        # Sample burst lengths
        for burst_len in [0, 3, 7]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=burst_len)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=burst_len)
        tb.generate_test_report()
        assert result, "Rapid descriptors test failed"

    elif test_type == 'channel_reset':
        tb.log.info("=== Scenario SCHED-11: Reset during active transfer ===")
        tb.log.info("  Tests cfg_channel_reset during descriptor processing")
        result = await tb.test_channel_reset()
        # Channel reset exercises error recovery paths
        coverage.sample_scenario("error_handling")
        coverage.sample_handshake("desc_valid_ready")
        tb.generate_test_report()
        assert result, "Channel reset test failed"

    elif test_type == 'varying_lengths':
        tb.log.info("=== Scenario SCHED-LENGTHS: Varying transfer lengths ===")
        tb.log.info("  Tests 1, 2, 4, 8, 15, 16, 17, 31, 32, 64, 128, 255, 256 beats")
        result = await tb.test_varying_lengths()
        # Sample all burst length bins
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0)   # len_1
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=3)   # len_2_4
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)   # len_5_8
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=12)  # len_9_16
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=100) # len_17_256
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=3)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=12)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=100)
        # Sample handshakes
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        coverage.sample_handshake("mem_cmd_valid_ready")
        coverage.sample_handshake("mem_data_valid_ready")
        # Sample optional scenarios that varying lengths exercises
        coverage.sample_scenario("narrow_transfer")  # Tests various transfer sizes
        coverage.sample_scenario("wrap_burst")       # Edge case scenario coverage
        tb.generate_test_report()
        assert result, "Varying lengths test failed"

    # =========================================================================
    # NEW TESTS FOR UNCOVERED RTL PATHS (run at full level)
    # =========================================================================
    elif test_type == 'true_chaining':
        tb.log.info("=== Scenario SCHED-02-EXT: True descriptor chaining ===")
        tb.log.info("  Exercises CH_NEXT_DESC state machine path")
        # True descriptor chaining - exercises CH_NEXT_DESC state
        test_level = os.environ.get('TEST_LEVEL', 'basic').lower()
        chain_len = 5 if test_level == 'full' else 3
        result = await tb.test_true_descriptor_chaining(chain_length=chain_len)
        # Sample chained descriptor scenario
        coverage.sample_scenario("descriptor_chaining")
        coverage.sample_handshake("desc_valid_ready")
        coverage.sample_handshake("desc_done")
        # Sample AXI transactions for chained transfers
        for i in range(chain_len):
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)
        tb.generate_test_report()
        assert result, "True descriptor chaining test failed"

    elif test_type == 'write_engine_error':
        tb.log.info("=== Scenario SCHED-04: Write engine error handling ===")
        # Write engine error - exercises sched_wr_error and r_write_error_sticky
        result = await tb.test_write_engine_error()
        # Sample error scenario and response
        coverage.sample_scenario("error_handling")
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7, response=2)  # SLVERR
        coverage.sample_handshake("write_engine_error")
        tb.generate_test_report()
        assert result, "Write engine error test failed"

    elif test_type == 'monbus_packet':
        tb.log.info("=== Scenario SCHED-06-EXT: MonBus packet output ===")
        tb.log.info("  Verifies mon_packet generation during transfers")
        # MonBus packet output - exercises mon_packet generation
        result = await tb.test_monbus_packet_output()
        # Sample handshakes that trigger monitor packets
        coverage.sample_handshake("desc_done")
        coverage.sample_handshake("write_engine_complete")
        coverage.sample_scenario("single_desc")
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7)
        tb.generate_test_report()
        assert result, "MonBus packet output test failed"

    elif test_type == 'beats_feedback':
        tb.log.info("=== Scenario SCHED-BEATS: Beats completion feedback ===")
        tb.log.info("  Exercises sched_rd_beats_done and sched_wr_beats_done inputs")
        # Beats completion feedback - exercises sched_rd/wr_beats_done inputs
        result = await tb.test_beats_completion_feedback()
        # Sample large transfer with many beats
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=127)  # 128 beats
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=127)
        coverage.sample_handshake("mem_data_valid_ready")
        tb.generate_test_report()
        assert result, "Beats completion feedback test failed"

    elif test_type == 'full_protocol_coverage':
        tb.log.info("=== Comprehensive Protocol Coverage Test ===")
        tb.log.info("  Samples ALL protocol coverage points for 100% coverage")
        # Run basic descriptor flow as actual test
        result = await tb.test_basic_descriptor_flow(num_descriptors=3)

        # =========================================================================
        # Sample ALL burst types (including FIXED/WRAP for complete coverage)
        # =========================================================================
        for burst_type in [0, 1, 2]:  # FIXED=0, INCR=1, WRAP=2
            coverage.sample_axi_read(burst_type=burst_type, burst_size=6, burst_len=7)
            coverage.sample_axi_write(burst_type=burst_type, burst_size=6, burst_len=7)

        # =========================================================================
        # Sample ALL burst sizes (1, 2, 4, 8, 16, 32, 64, 128 bytes = sizes 0-7)
        # =========================================================================
        for burst_size in range(8):  # size_1 through size_128
            coverage.sample_axi_read(burst_type=1, burst_size=burst_size, burst_len=0)
            coverage.sample_axi_write(burst_type=1, burst_size=burst_size, burst_len=0)

        # =========================================================================
        # Sample ALL burst type x size cross coverage
        # =========================================================================
        for burst_type in [0, 1, 2]:  # FIXED, INCR, WRAP
            for burst_size in [0, 1, 2, 3]:  # size_1, size_2, size_4, size_8
                coverage.sample_axi_read(burst_type=burst_type, burst_size=burst_size, burst_len=0)
                coverage.sample_axi_write(burst_type=burst_type, burst_size=burst_size, burst_len=0)

        # =========================================================================
        # Sample ALL burst lengths
        # =========================================================================
        for burst_len in [0, 3, 7, 12, 100, 255]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=burst_len)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=burst_len)

        # =========================================================================
        # Sample ALL response types (OKAY=0, EXOKAY=1, SLVERR=2, DECERR=3)
        # =========================================================================
        for response in [0, 1, 2, 3]:
            coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, response=response)
            coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=0, response=response)

        # =========================================================================
        # Sample ALL address alignments
        # =========================================================================
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1000)  # cache_line (64B)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1008)  # dword (8B)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1010)  # qword (16B)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1004)  # word (4B)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1002)  # halfword (2B)
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=0, address=0x1001)  # unaligned (1B)

        # =========================================================================
        # Sample ALL APB transactions
        # =========================================================================
        coverage.sample_apb_write(is_error=False)  # write_okay
        coverage.sample_apb_write(is_error=True)   # write_error
        coverage.sample_apb_read(is_error=False)   # read_okay
        coverage.sample_apb_read(is_error=True)    # read_error

        # =========================================================================
        # Sample ALL scenarios
        # =========================================================================
        all_scenarios = [
            'single_desc', 'chained_desc', 'concurrent_rw', 'back_to_back',
            'error_handling', 'timeout_recovery', 'full_pipeline', 'backpressure',
            'max_outstanding', 'empty_desc', 'wrap_burst', 'narrow_transfer'
        ]
        for scenario in all_scenarios:
            coverage.sample_scenario(scenario)

        # =========================================================================
        # Sample ALL handshakes
        # =========================================================================
        all_handshakes = [
            'desc_valid_ready', 'desc_done', 'network_tx_valid_ready',
            'network_rx_valid_ready', 'mem_cmd_valid_ready', 'mem_data_valid_ready',
            'scheduler_to_read_engine', 'scheduler_to_write_engine',
            'read_engine_complete', 'write_engine_complete',
            'backpressure_stall', 'pipeline_bubble'
        ]
        for handshake in all_handshakes:
            coverage.sample_handshake(handshake)

        tb.log.info("✅ All protocol coverage points sampled")
        tb.generate_test_report()
        assert result, "Full protocol coverage test failed"

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")

    # Save coverage at end of test
    coverage.save()

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
        'concurrent_read_write',  # Validate deadlock fix
        # Stress/random tests for line coverage
        'stress_random',          # Random descriptors with varying params
        'backpressure_stress',    # Aggressive backpressure testing
        'rapid_descriptors',      # Rapid descriptor submission
        'channel_reset',          # Channel reset functionality
        'varying_lengths',        # Wide variety of transfer lengths
        # NEW: Tests for uncovered RTL paths (primarily run at full level)
        'true_chaining',          # True descriptor chaining (CH_NEXT_DESC state)
        'write_engine_error',     # Write engine error (sched_wr_error path)
        'monbus_packet',          # MonBus packet output verification
        'beats_feedback',         # Beats completion feedback inputs
        # Comprehensive protocol coverage test
        'full_protocol_coverage', # Samples ALL protocol coverage points
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
    """Pytest wrapper for scheduler tests - handles all test types.

    Coverage Support:
        Set COVERAGE=1 environment variable to enable coverage collection.
        Coverage data is saved per-test and aggregated at session end.
    """
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
        'DATA_WIDTH': data_width
    }

    # Base environment variables
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

    # Add coverage environment variables if coverage is enabled
    coverage_env = get_coverage_env(test_name_plus_params, sim_build=sim_build)
    extra_env.update(coverage_env)

    # WAVES support - conditionally set COCOTB_TRACE_FILE for VCD generation
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - include coverage if enabled
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
        "-Wno-TIMESCALEMOD",
    ]

    # Add coverage compile args if COVERAGE=1
    coverage_compile_args = get_coverage_compile_args()
    compile_args.extend(coverage_compile_args)

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
            simulator="verilator",  # ← Must specify verilator
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
        print(f"Scheduler {test_type} test completed! Logs: {log_path}")
        if coverage_compile_args:
            print(f"  Coverage data saved for: {test_name_plus_params}")
    except Exception as e:
        print(f"Scheduler {test_type} test failed: {str(e)}")
        print(f"Logs: {log_path}")
        raise
