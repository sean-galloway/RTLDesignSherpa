# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler
# Purpose: RAPIDS Scheduler FUB Validation Test - Phase 1 (STREAM-based)
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler FUB Validation Test - Phase 1 (STREAM-based)

Test suite for the RAPIDS Phase 1 scheduler module with concurrent read/write architecture.

RAPIDS Phase 1 Features (tested here):
- Concurrent read/write in CH_XFER_DATA state
- Beat-based length (aligned addresses)
- Descriptor chaining via next_descriptor_ptr
- IRQ generation via MonBus
- Error handling (descriptor, read engine, write engine)
- Channel reset functionality

NOT in Phase 1 (NOT tested):
- Credit management (Phase 2 feature)
- Control engines ctrlrd/ctrlwr (Phase 2 feature)
- Alignment fixup (Phase 1 requires aligned addresses)

This test file imports the reusable SchedulerTB class from:
  projects/components/rapids/dv/tbclasses/scheduler_tb.py (PROJECT AREA - CORRECT!)

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import sys

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
from projects.components.rapids.dv.tbclasses.scheduler_tb import SchedulerTB


# ===========================================================================
# BASIC DESCRIPTOR FLOW TESTS
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_descriptor_flow(dut):
    """Test basic descriptor processing flow"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow(num_descriptors=5)
    tb.generate_test_report()
    assert result, "Basic descriptor flow test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_concurrent_transfer(dut):
    """Test concurrent read/write in CH_XFER_DATA state"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_concurrent_transfer()
    tb.generate_test_report()
    assert result, "Concurrent transfer test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_descriptor_chaining(dut):
    """Test descriptor chaining with next_descriptor_ptr"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_chaining(chain_length=3)
    tb.generate_test_report()
    assert result, "Descriptor chaining test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_irq_generation(dut):
    """Test IRQ event generation via MonBus"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_irq_generation()
    tb.generate_test_report()
    assert result, "IRQ generation test failed"


# ===========================================================================
# ERROR HANDLING TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_descriptor_error_injection(dut):
    """Test handling of descriptor errors"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_error_injection()
    tb.generate_test_report()
    assert result, "Descriptor error injection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_read_engine_error(dut):
    """Test handling of read engine errors"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_read_engine_error()
    tb.generate_test_report()
    assert result, "Read engine error test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_write_engine_error(dut):
    """Test handling of write engine errors"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_write_engine_error()
    tb.generate_test_report()
    assert result, "Write engine error test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_channel_reset(dut):
    """Test channel reset functionality"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_channel_reset()
    tb.generate_test_report()
    assert result, "Channel reset test failed"


# ===========================================================================
# STRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_back_to_back_descriptors(dut):
    """Test rapid back-to-back descriptor submission"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_back_to_back_descriptors(count=10)
    tb.generate_test_report()
    assert result, "Back-to-back descriptors test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_varying_transfer_sizes(dut):
    """Test transfers of varying sizes"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_varying_transfer_sizes()
    tb.generate_test_report()
    assert result, "Varying transfer sizes test failed"


# ===========================================================================
# FSM STATE TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_fsm_state_transitions(dut):
    """Test all FSM state transitions"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_fsm_state_transitions()
    tb.generate_test_report()
    assert result, "FSM state transitions test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests.

    Returns list of tuples: (channel_id, num_channels, data_width)
    """
    return [
        # Standard configuration
        (0, 8, 512),
    ]


scheduler_params = generate_scheduler_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Flow Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_basic_flow(request, channel_id, num_channels, data_width):
    """Pytest: Test basic descriptor flow"""
    _run_scheduler_test(request, "cocotb_test_basic_descriptor_flow",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_concurrent_transfer(request, channel_id, num_channels, data_width):
    """Pytest: Test concurrent read/write transfer"""
    _run_scheduler_test(request, "cocotb_test_concurrent_transfer",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_descriptor_chaining(request, channel_id, num_channels, data_width):
    """Pytest: Test descriptor chaining"""
    _run_scheduler_test(request, "cocotb_test_descriptor_chaining",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_irq_generation(request, channel_id, num_channels, data_width):
    """Pytest: Test IRQ generation via MonBus"""
    _run_scheduler_test(request, "cocotb_test_irq_generation",
                       channel_id, num_channels, data_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Error Handling
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_descriptor_error(request, channel_id, num_channels, data_width):
    """Pytest: Test descriptor error injection"""
    _run_scheduler_test(request, "cocotb_test_descriptor_error_injection",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_read_error(request, channel_id, num_channels, data_width):
    """Pytest: Test read engine error"""
    _run_scheduler_test(request, "cocotb_test_read_engine_error",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_write_error(request, channel_id, num_channels, data_width):
    """Pytest: Test write engine error"""
    _run_scheduler_test(request, "cocotb_test_write_engine_error",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_channel_reset(request, channel_id, num_channels, data_width):
    """Pytest: Test channel reset functionality"""
    _run_scheduler_test(request, "cocotb_test_channel_reset",
                       channel_id, num_channels, data_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Stress Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_back_to_back(request, channel_id, num_channels, data_width):
    """Pytest: Test back-to-back descriptors"""
    _run_scheduler_test(request, "cocotb_test_back_to_back_descriptors",
                       channel_id, num_channels, data_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_varying_sizes(request, channel_id, num_channels, data_width):
    """Pytest: Test varying transfer sizes"""
    _run_scheduler_test(request, "cocotb_test_varying_transfer_sizes",
                       channel_id, num_channels, data_width)


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - FSM State Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width", scheduler_params)
def test_fsm_transitions(request, channel_id, num_channels, data_width):
    """Pytest: Test FSM state transitions"""
    _run_scheduler_test(request, "cocotb_test_fsm_state_transitions",
                       channel_id, num_channels, data_width)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_scheduler_test(request, testcase_name, channel_id, num_channels, data_width):
    """Helper function to run scheduler tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        channel_id: Channel ID for this test
        num_channels: Total number of channels
        data_width: Data width in bits
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_fub_beats': '../../rtl/fub_beats'
    })

    dut_name = "scheduler_beats"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub_beats/scheduler_beats.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    dw_str = TBBase.format_dec(data_width, 4)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_cid{cid_str}_nc{nc_str}_dw{dw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters for Phase 1 scheduler
    chan_width = (num_channels - 1).bit_length() if num_channels > 1 else 1
    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'CHAN_WIDTH': chan_width,
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': data_width,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'CHANNEL_ID': str(channel_id),
        'NUM_CHANNELS': str(num_channels),
        'DATA_WIDTH': str(data_width),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD"]
    if coverage_enabled:
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase_name,
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=os.environ.get('ENABLE_WAVEDUMP', '0') == '1',
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"✗ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic flow test when executed directly
    print("Running basic descriptor flow test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_scheduler_test(request, "cocotb_test_basic_descriptor_flow",
                       channel_id=0, num_channels=8, data_width=512)
