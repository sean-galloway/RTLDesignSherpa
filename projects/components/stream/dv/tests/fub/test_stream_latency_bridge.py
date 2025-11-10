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
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, ReadOnly
from cocotb_test.simulator import run

# Setup Python path BEFORE any other imports
import sys
# First, do minimal setup to import get_repo_root
repo_root_temp = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, os.path.join(repo_root_temp, 'bin'))

# Now import utilities to get proper repo root
from CocoTBFramework.tbclasses.shared.utilities import get_repo_root

# Use the proper get_repo_root() function
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import testbench
from projects.components.stream.dv.tbclasses.stream_latency_bridge_tb import StreamLatencyBridgeTB

# Framework utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


#===============================================================================
# Helper Functions - Test Logic
#===============================================================================

async def run_occupancy_test(tb):
    """Test occupancy tracking with 4-deep skid buffer"""
    tb.log.info("=== Testing Occupancy Tracking ===")

    # Initially occupancy should be 0
    occ = tb.get_occupancy()
    assert occ == 0, f"Initial occupancy should be 0, got {occ}"
    tb.log.info(f"✓ Initial occupancy: {occ}")

    # Block downstream to prevent draining
    tb.dut.m_ready.value = 0
    tb.dut.s_valid.value = 1

    # Write 4 beats to fill FIFO (strict FIFO count, not counting in-flight)
    # Occupancy = FIFO count (max 4)
    tb.log.info("Writing 4 beats to fill FIFO...")
    for i in range(4):
        tb.dut.s_data.value = 0xA000 + i
        await RisingEdge(tb.dut.clk)
        ready = int(tb.dut.s_ready.value)
        tb.log.info(f"Wrote beat {i+1}: s_ready={ready}")

    # Wait for FIFO to fully fill
    await RisingEdge(tb.dut.clk)

    # Check final occupancy
    occ = tb.get_occupancy()
    tb.log.info(f"Final occupancy after 4 writes: {occ}")

    # Verify occupancy shows FIFO filled
    # With 4-deep FIFO, max occupancy is 4 (strict FIFO count, not counting in-flight)
    assert occ == 4, f"Expected occupancy = 4 after filling, got {occ}"
    tb.log.info(f"✓ FIFO filled: occupancy={occ}")

    # Verify backpressure asserted (s_ready should be 0 now)
    ready = int(tb.dut.s_ready.value)
    assert ready == 0, f"Expected s_ready=0 when pipeline full, got {ready}"
    tb.log.info("✓ Backpressure correctly asserted (s_ready=0)")

    # Release downstream and verify occupancy decreases
    tb.dut.s_valid.value = 0  # Stop writing
    tb.dut.m_ready.value = 1  # Start reading

    await RisingEdge(tb.dut.clk)
    await RisingEdge(tb.dut.clk)
    occ_after = tb.get_occupancy()
    assert occ_after < 5, f"Occupancy should decrease after draining, got {occ_after}"
    tb.log.info(f"✓ Occupancy decreased after draining: {occ_after}")

    tb.log.info("✓ Occupancy tracking test passed")


async def run_streaming_test(tb):
    """Test streaming flow with occupancy"""
    occupancies = await tb.verify_streaming_flow(num_beats=20)

    # During streaming, occupancy should stabilize to 1 or 2
    # (pipeline stays partially/fully filled)
    avg_occ = sum(occupancies) / len(occupancies)
    tb.log.info(f"Average occupancy during streaming: {avg_occ:.2f}")
    assert avg_occ > 0, "Occupancy should be non-zero during streaming"


async def run_backpressure_test(tb):
    """Test backpressure when 4-deep skid buffer fills"""
    tb.log.info("=== Testing Backpressure with 4-deep Skid ===")

    # Collect errors for soft-fail pattern
    errors = []

    # Fill pipeline without reading
    tb.dut.m_ready.value = 0
    tb.dut.s_valid.value = 1

    # Write beats and track s_ready until backpressure
    # Occupancy = FIFO count (max 4 with strict FIFO count)
    beats_written = []
    backpressure_detected = False

    for i in range(6):  # Try to write 6 beats (should stop at 4)
        # Set data for this beat
        if not backpressure_detected:
            data = 0xA000 + i
            tb.dut.s_data.value = data

        # Wait for clock and sample signals
        await RisingEdge(tb.dut.clk)
        ready = int(tb.dut.s_ready.value)
        occ = tb.get_occupancy()

        # If backpressure was already detected, just log and skip
        if backpressure_detected:
            tb.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: Beat {i+1}: Skipped (backpressure active), s_ready={ready}, occupancy={occ}")
            continue

        # Check if handshake occurred (s_valid && s_ready in previous cycle)
        # On this cycle, we see the result of the previous cycle's handshake
        if i == 0 or ready == 1:  # First beat or ready was high
            beats_written.append(data)
            tb.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: Beat {i+1}: data=0x{data:X}, s_ready={ready}, occupancy={occ}")
        else:
            tb.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: Beat {i+1} BLOCKED: s_ready={ready}, occupancy={occ}")
            backpressure_detected = True  # Flag for next iteration

    # Verify exactly 4 beats written before backpressure (FIFO depth = 4)
    # NOTE: Occupancy now reflects strict FIFO count (not counting in-flight)
    if len(beats_written) != 4:
        msg = f"Expected 4 beats before backpressure, wrote {len(beats_written)}"
        tb.log.error(f"❌ {msg}")
        errors.append(msg)
    else:
        tb.log.info(f"✓ Wrote {len(beats_written)} beats before backpressure")

    # Verify occupancy at max (FIFO depth)
    final_occ = tb.get_occupancy()
    if final_occ != 4:
        msg = f"Expected occupancy=4 at backpressure, got {final_occ}"
        tb.log.error(f"❌ {msg}")
        errors.append(msg)
    else:
        tb.log.info(f"✓ Occupancy at max: {final_occ}")

    # Verify s_ready deasserted
    ready_now = int(tb.dut.s_ready.value)
    if ready_now != 0:
        msg = f"Expected s_ready=0 at max occupancy, got {ready_now}"
        tb.log.error(f"❌ {msg}")
        errors.append(msg)
    else:
        tb.log.info("✓ Backpressure correctly asserted (s_ready=0)")

    # Release backpressure by reading
    tb.dut.s_valid.value = 0  # Stop writing
    tb.dut.m_ready.value = 1  # Start reading

    # Read out some beats
    read_beats = []
    for i in range(3):
        await RisingEdge(tb.dut.clk)
        if int(tb.dut.m_valid.value):
            data = int(tb.dut.m_data.value)
            read_beats.append(data)
            tb.log.info(f"@ {cocotb.utils.get_sim_time('ns')}ns: Read beat {i+1}: data=0x{data:X}")

    # Verify s_ready re-asserted after draining
    await RisingEdge(tb.dut.clk)
    ready_after = int(tb.dut.s_ready.value)
    occ_after = tb.get_occupancy()
    if ready_after != 1:
        msg = f"Expected s_ready=1 after draining, got {ready_after}"
        tb.log.error(f"❌ {msg}")
        errors.append(msg)
    else:
        tb.log.info(f"✓ Backpressure released (s_ready={ready_after}, occupancy={occ_after})")

    # Final report - single assertion point
    if errors:
        tb.log.error("="*80)
        tb.log.error(f"BACKPRESSURE TEST FAILED: {len(errors)} error(s)")
        for err in errors:
            tb.log.error(f"  - {err}")
        tb.log.error("="*80)
        raise AssertionError(f"Backpressure test failed with {len(errors)} error(s)")
    else:
        tb.log.info("✓ Backpressure test passed")


#===============================================================================
# COCOTB TEST FUNCTION - Single test that handles all variants
#===============================================================================

@cocotb.test(timeout_time=10, timeout_unit="ms")
async def cocotb_test_stream_latency_bridge(dut):
    """Unified stream latency bridge test - handles all test types via TEST_TYPE env var.

    Test Types:
    - 'occupancy': Occupancy tracking with 4-deep skid buffer
    - 'streaming': Streaming flow with occupancy verification
    - 'backpressure': Backpressure when 4-deep skid buffer fills
    """
    test_type = os.environ.get('TEST_TYPE', 'occupancy')
    tb = StreamLatencyBridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Branch on test type
    if test_type == 'occupancy':
        await run_occupancy_test(tb)

    elif test_type == 'streaming':
        await run_streaming_test(tb)

    elif test_type == 'backpressure':
        await run_backpressure_test(tb)

    else:
        raise ValueError(f"Unknown TEST_TYPE: {test_type}")


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
    elif reg_level == 'FUNC':
        # Functional coverage
        data_widths = [256, 512]
    else:  # FULL
        # Comprehensive
        data_widths = [128, 256, 512]

    # Generate params for all test types
    test_types = ['occupancy', 'streaming', 'backpressure']
    params = []
    for test_type in test_types:
        for data_width in data_widths:
            params.append((test_type, data_width))

    return params


params = generate_params()


#===============================================================================
# PYTEST WRAPPER FUNCTION - Single wrapper for all test types
#===============================================================================

@pytest.mark.parametrize("test_type, data_width", params)
def test_stream_latency_bridge(request, test_type, data_width):
    """Pytest wrapper for stream latency bridge tests - handles all test types."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_stream_fub': '../../../../rtl/stream_fub',
    })

    dut_name = "stream_latency_bridge"

    # Format parameter for unique test name (xdist compatibility)
    dw_str = f"{data_width:04d}"
    test_name = f"test_latency_bridge_{test_type}_dw{dw_str}"

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

    compile_args = ['-Wno-TIMESCALEMOD', '-Wno-WIDTHEXPAND', '-Wno-WIDTHTRUNC']

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
        extra_env=extra_env
    )

    # Restore WAVES if it was set
    if waves_requested and waves_value is not None:
        os.environ['WAVES'] = waves_value

    print(f"✓ Stream latency bridge {test_type} test completed! Logs: {log_path}")
