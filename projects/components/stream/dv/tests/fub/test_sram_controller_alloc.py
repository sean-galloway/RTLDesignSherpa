"""
SRAM Controller Allocation Tests

Tests allocation controller functionality (stream_alloc_ctrl):
- Pre-allocation before data arrival (like AXI read engine)
- Space tracking with reserved vs. committed beats
- Filling FIFO via allocation
- Timing verification (wr_drain_data_avail should have 1-2 clock delay)

Test Types:
- 'basic': Basic allocation test (pre-allocate then write data)
- 'full': Fill FIFO completely via allocation
- 'multi_channel': Multi-channel allocation test
- 'timing': Verify wr_drain_data_avail timing (1-2 cycle delay)

STRUCTURE FOLLOWS REPOSITORY STANDARD:
  - Single CocoTB test function (dispatches based on TEST_TYPE)
  - Single parameter generator (includes test_type as first parameter)
  - Single pytest wrapper (fully parametrized)

Author: RTL Design Sherpa
Created: 2025-10-31
Updated: 2025-11-07 - Refactored to standard pattern
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge
from cocotb_test.simulator import run

from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd, get_repo_root
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import testbench from project area
from projects.components.stream.dv.tbclasses.sram_controller_tb import SRAMControllerTB


#==============================================================================
# Helper Functions - Allocation Tests
#==============================================================================

async def run_basic_allocation_test(tb):
    """Basic allocation test: pre-allocate then write data"""
    success = await tb.run_allocation_test(channel=0, num_beats=32)
    assert success, "Allocation test failed"
    tb.log.info("✓ Basic allocation test completed successfully")


async def run_full_allocation_test(tb):
    """Fill FIFO completely via allocation"""
    success = await tb.run_full_allocation_test(channel=0)
    assert success, "Full allocation test failed"
    tb.log.info("✓ Full allocation test completed successfully")


async def run_multi_channel_allocation_test(tb):
    """Multi-channel allocation test"""
    # Test allocation on multiple channels concurrently
    num_channels = min(4, tb.num_channels)  # Test first 4 channels
    beats_per_channel = 16

    tb.log.info(f"=== Multi-Channel Allocation Test: {num_channels} channels, {beats_per_channel} beats each ===")

    # Allocate on all channels
    for ch in range(num_channels):
        success = await tb.allocate_space(ch, beats_per_channel)
        assert success, f"Allocation failed on channel {ch}"
        tb.log.info(f"✓ Channel {ch}: allocated {beats_per_channel} beats")

    # Verify all allocations reduced space correctly
    for ch in range(num_channels):
        space_free = await tb.get_space_free(ch)
        expected_space = tb.fifo_depth - beats_per_channel  # Use actual FIFO depth
        if abs(space_free - expected_space) > 2:  # Allow small tolerance
            tb.log.error(f"✗ Channel {ch} space mismatch: expected~{expected_space}, got {space_free}")
            assert False, f"Space verification failed on channel {ch}"

    # Write data to all channels (interleaved)
    for beat in range(beats_per_channel):
        for ch in range(num_channels):
            beat_num = beat + 1
            data = (beat_num << 32) | (ch << 16) | beat_num
            success = await tb.write_channel_data(ch, data)
            assert success, f"Write failed: channel={ch}, beat={beat}"

    # Wait for data to propagate
    await tb.wait_clocks(tb.clk_name, 5)

    # Verify data available on all channels
    for ch in range(num_channels):
        data_count = await tb.get_data_available(ch)
        if data_count < beats_per_channel - 2:  # Allow for pipeline
            tb.log.error(f"✗ Channel {ch} data_count too low: expected~{beats_per_channel}, got {data_count}")
            assert False, f"Data count verification failed on channel {ch}"
        tb.log.info(f"✓ Channel {ch}: {data_count} beats available")

    tb.log.info("✓ Multi-channel allocation test completed successfully")


async def run_timing_allocation_test(tb):
    """
    Verify wr_drain_data_avail timing - should NOT be combinatorial with writes

    Expected: 1-2 clock cycles delay through FIFO + latency bridge
    """
    channel = 0
    num_beats = 8

    tb.log.info(f"=== Allocation Timing Test: Verify wr_drain_data_avail delay ===")

    # Pre-allocate
    success = await tb.allocate_space(channel, num_beats)
    assert success, "Allocation failed"

    # Check data_available before writing (should be 0)
    data_count_before = await tb.get_data_available(channel)
    if data_count_before != 0:
        tb.log.error(f"✗ Data available before write should be 0, got {data_count_before}")
        assert False, "Data available before write should be 0"

    # Write first beat
    data = 0x100000001
    tb.dut.axi_rd_sram_valid.value = 1
    tb.dut.axi_rd_sram_id.value = channel
    tb.dut.axi_rd_sram_data.value = data
    await RisingEdge(tb.clk)
    tb.dut.axi_rd_sram_valid.value = 0

    # Check data_available IMMEDIATELY after write (same cycle)
    # Should still be 0 - data not yet visible due to FIFO + latency bridge pipeline
    data_count_cycle0 = await tb.get_data_available(channel)
    tb.log.info(f"Cycle 0 (write cycle): wr_drain_data_avail={data_count_cycle0}")

    # Wait one more cycle
    await RisingEdge(tb.clk)
    data_count_cycle1 = await tb.get_data_available(channel)
    tb.log.info(f"Cycle 1 (after write): wr_drain_data_avail={data_count_cycle1}")

    # Wait one more cycle
    await RisingEdge(tb.clk)
    data_count_cycle2 = await tb.get_data_available(channel)
    tb.log.info(f"Cycle 2 (after write): wr_drain_data_avail={data_count_cycle2}")

    # Data should appear after 1-2 cycles (FIFO registered + latency bridge)
    # Expected: cycle 0 = 0, cycle 1 or 2 = 1
    if data_count_cycle0 > 0:
        tb.log.error(f"✗ TIMING VIOLATION: wr_drain_data_avail went active combinatorially!")
        assert False, "wr_drain_data_avail should not be combinatorial with write"

    if data_count_cycle2 < 1:
        tb.log.error(f"✗ Data should be available after 2 cycles, got {data_count_cycle2}")
        assert False, "Data should appear after pipeline delay"

    tb.log.info(f"✓ Timing verified: wr_drain_data_avail has proper 1-2 cycle delay")


#==============================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
#==============================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_sram_controller_alloc(dut):
    """Unified SRAM controller allocation test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'basic': Basic allocation test (pre-allocate then write data)
    - 'full': Fill FIFO completely via allocation
    - 'multi_channel': Multi-channel allocation test (concurrent operation)
    - 'timing': Timing verification (wr_drain_data_avail delay)
    """
    test_type = os.environ.get('TEST_TYPE', 'basic')
    tb = SRAMControllerTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'basic':
        await run_basic_allocation_test(tb)

    elif test_type == 'full':
        await run_full_allocation_test(tb)

    elif test_type == 'multi_channel':
        await run_multi_channel_allocation_test(tb)

    elif test_type == 'timing':
        await run_timing_allocation_test(tb)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


#==============================================================================
# PARAMETER GENERATION
#==============================================================================

def generate_sram_alloc_params():
    """
    Generate test parameters for SRAM allocation tests

    Returns:
        List of tuples: (test_type, num_channels, fifo_depth, data_width)
    """
    # Fewer configs since allocation tests are longer
    base_params = [
        # (num_channels, fifo_depth, data_width)
        (4, 256, 64),     # Small config for quick tests
        (8, 512, 512),    # Medium config
    ]

    # Different test types have different parameter coverage
    params = []

    # Basic and full tests run on all base configs
    for test_type in ['basic', 'full', 'multi_channel']:
        for base in base_params:
            params.append((test_type,) + base)

    # Timing test only runs on small config (it's detailed)
    params.append(('timing', 4, 256, 64))

    return params


sram_alloc_params = generate_sram_alloc_params()


#==============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#==============================================================================

@pytest.mark.parametrize("test_type, num_channels, fifo_depth, data_width", sram_alloc_params)
def test_sram_controller_alloc(request, test_type, num_channels, fifo_depth, data_width, test_level):
    """Pytest wrapper for SRAM controller allocation tests - handles all test types."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "sram_controller"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/stream/rtl/filelists/fub/sram_controller.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    fd_str = TBBase.format_dec(fifo_depth, 4)
    dw_str = TBBase.format_dec(data_width, 4)

    test_name_plus_params = f"test_{dut_name}_alloc_{test_type}_nc{nc_str}_fd{fd_str}_dw{dw_str}"

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

    simulator = os.environ.get('SIM', 'verilator').lower()

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_test_sram_controller_alloc",  # ← Single cocotb test
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            simulator=simulator,
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
        print(f"✓ Allocation {test_type} test completed! Logs: {log_path}")
    except SystemExit as e:
        if e.code != 0:
            pytest.fail(f"Allocation {test_type} test failed with exit code {e.code}. Check log: {log_path}")
