# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: MockRequest
# Purpose: RAPIDS Scheduler FUB Validation Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Scheduler FUB Validation Test

Comprehensive test suite for the RAPIDS scheduler module with dozens of individual tests
attacking every possible weakness in the RTL.

Test Organization:
- Exponential credit encoding tests (16 test cases - one for each value 0-15)
- Credit management tests (increment, decrement, exhaustion)
- Descriptor flow tests (basic, RDA, EOS, program sequencing)
- Error handling tests (descriptor errors, data errors, timeout)
- Stress tests (back-to-back, backpressure, mixed types)

This test file imports the reusable SchedulerTB class from:
  projects/components/rapids/dv/tbclasses/scheduler_tb.py (PROJECT AREA - CORRECT!)

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import sys

# Add RAPIDS DV directory to path to import project-area testbench classes
# This makes the import work regardless of whether env_python is sourced
rapids_dv_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
if rapids_dv_path not in sys.path:
    sys.path.insert(0, rapids_dv_path)

import pytest
import cocotb
from cocotb_test.simulator import run

# Import TB class from PROJECT AREA (not framework!)
from tbclasses.scheduler_tb import SchedulerTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


# ===========================================================================
# EXPONENTIAL CREDIT ENCODING TESTS - All 16 values (0-15)
# ===========================================================================
# NOTE: These cocotb test functions are prefixed with "cocotb_" to prevent pytest
# from collecting them directly. They are only run via the pytest wrappers below.

@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_0(dut):
    """Test exponential encoding: cfg=0 → 1 credit (2^0)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(0, 1)
    assert result, "Exponential encoding test for value 0 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_1(dut):
    """Test exponential encoding: cfg=1 → 2 credits (2^1)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(1, 2)
    assert result, "Exponential encoding test for value 1 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_2(dut):
    """Test exponential encoding: cfg=2 → 4 credits (2^2)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(2, 4)
    assert result, "Exponential encoding test for value 2 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_3(dut):
    """Test exponential encoding: cfg=3 → 8 credits (2^3)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(3, 8)
    assert result, "Exponential encoding test for value 3 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_4(dut):
    """Test exponential encoding: cfg=4 → 16 credits (2^4)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(4, 16)
    assert result, "Exponential encoding test for value 4 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_5(dut):
    """Test exponential encoding: cfg=5 → 32 credits (2^5)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(5, 32)
    assert result, "Exponential encoding test for value 5 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_6(dut):
    """Test exponential encoding: cfg=6 → 64 credits (2^6)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(6, 64)
    assert result, "Exponential encoding test for value 6 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_7(dut):
    """Test exponential encoding: cfg=7 → 128 credits (2^7)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(7, 128)
    assert result, "Exponential encoding test for value 7 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_8(dut):
    """Test exponential encoding: cfg=8 → 256 credits (2^8)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(8, 256)
    assert result, "Exponential encoding test for value 8 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_9(dut):
    """Test exponential encoding: cfg=9 → 512 credits (2^9)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(9, 512)
    assert result, "Exponential encoding test for value 9 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_10(dut):
    """Test exponential encoding: cfg=10 → 1024 credits (2^10)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(10, 1024)
    assert result, "Exponential encoding test for value 10 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_11(dut):
    """Test exponential encoding: cfg=11 → 2048 credits (2^11)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(11, 2048)
    assert result, "Exponential encoding test for value 11 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_12(dut):
    """Test exponential encoding: cfg=12 → 4096 credits (2^12)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(12, 4096)
    assert result, "Exponential encoding test for value 12 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_13(dut):
    """Test exponential encoding: cfg=13 → 8192 credits (2^13)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(13, 8192)
    assert result, "Exponential encoding test for value 13 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_14(dut):
    """Test exponential encoding: cfg=14 → 16384 credits (2^14)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(14, 16384)
    assert result, "Exponential encoding test for value 14 failed"


@cocotb.test(timeout_time=50, timeout_unit="ms")
async def cocotb_test_exponential_encoding_value_15(dut):
    """Test exponential encoding: cfg=15 → 0 credits (DISABLED)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_single_encoding_value(15, 0)
    assert result, "Exponential encoding test for value 15 failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_exponential_encoding_all_values(dut):
    """Test all 16 exponential encoding values in one test"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_exponential_encoding_all_values()
    assert result, "Comprehensive exponential encoding test failed"


# ===========================================================================
# CREDIT MANAGEMENT TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_credit_decrement_on_acceptance(dut):
    """Test credit decrements on descriptor acceptance (not data completion)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_credit_decrement_on_acceptance()
    assert result, "Credit decrement timing test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_credit_increment(dut):
    """Test credit increment mechanism"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_credit_increment()
    assert result, "Credit increment test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_credit_exhaustion(dut):
    """Test behavior when credits are exhausted"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_credit_exhaustion()
    assert result, "Credit exhaustion test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_credit_disabled(dut):
    """Test operation with credit management disabled"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_credit_disabled()
    assert result, "Credit disabled test failed"


# ===========================================================================
# DESCRIPTOR FLOW TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_descriptor_flow(dut):
    """Test basic descriptor processing"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow()
    assert result, "Basic descriptor flow test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_rda_completion(dut):
    """Test RDA completion flow"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_rda_completion()
    assert result, "RDA completion test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_eos_handling(dut):
    """Test EOS (End of Stream) boundary handling"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_eos_handling()
    assert result, "EOS handling test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_ctrl_sequencing(dut):
    """Test control sequencing (ctrlrd, ctrlwr) - RENAMED from program"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_ctrl_sequencing()
    assert result, "Control sequencing test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_descriptor_chaining(dut):
    """Test multiple descriptors with next descriptor address"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_descriptor_chaining()
    assert result, "Descriptor chaining test failed"


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
    assert result, "Descriptor error injection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_data_engine_error(dut):
    """Test handling of data engine errors"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_data_engine_error()
    assert result, "Data engine error test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_program_engine_error(dut):
    """Test handling of control write engine errors"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_ctrlwr_engine_error()
    assert result, "Control write engine error test failed"


# NOTE: Timeout test removed from main suite - use standalone test_scheduler_timeout.py instead
# The timeout test requires bare-metal signal control that conflicts with GAXI infrastructure
# @cocotb.test(timeout_time=200, timeout_unit="ms")
# async def cocotb_test_timeout_detection(dut):
#     """Test timeout detection for stuck operations
#
#     NOTE: This test continuously forces data_ready=0 to create sustained
#     backpressure, allowing the timeout counter to increment properly.
#     """
#     tb = SchedulerTB(dut)
#     await tb.setup_clocks_and_reset()
#     await tb.initialize_test()
#     result = await tb.test_timeout_detection()
#     assert result, "Timeout detection test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_channel_reset_recovery(dut):
    """Test recovery from channel reset"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_channel_reset_recovery()
    assert result, "Channel reset recovery test failed"


# ===========================================================================
# STRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_back_to_back_descriptors(dut):
    """Test rapid back-to-back descriptor submission (20 descriptors)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_back_to_back_descriptors()
    assert result, "Back-to-back descriptors test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_random_backpressure(dut):
    """Test with random backpressure on data/program engines"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_random_backpressure()
    assert result, "Random backpressure test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_mixed_packet_types(dut):
    """Test mixed descriptor types (RDA, EOS, normal)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_mixed_packet_types()
    assert result, "Mixed packet types test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_maximum_credits_stress(dut):
    """Test with maximum credits (cfg=14 → 16384 credits)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_maximum_credits_stress()
    assert result, "Maximum credits stress test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_minimum_credits_stress(dut):
    """Test with minimum credits (cfg=0 → 1 credit)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_minimum_credits_stress()
    assert result, "Minimum credits stress test failed"


# ===========================================================================
# ALIGNMENT AND ADDRESS TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_aligned_addresses(dut):
    """Test with aligned addresses (no alignment calculation needed)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_aligned_addresses()
    assert result, "Aligned addresses test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_unaligned_addresses(dut):
    """Test with unaligned addresses (alignment calculation required)"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_unaligned_addresses()
    assert result, "Unaligned addresses test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_alignment_backpressure(dut):
    """Test alignment bus with backpressure"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_alignment_backpressure()
    assert result, "Alignment backpressure test failed"


# ===========================================================================
# MONITOR BUS TESTS
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monitor_packet_generation(dut):
    """Test monitor packet generation"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_monitor_packet_generation()
    assert result, "Monitor packet generation test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_monitor_backpressure(dut):
    """Test monitor bus backpressure handling"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_monitor_backpressure()
    assert result, "Monitor backpressure test failed"


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
    assert result, "FSM state transitions test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_idle_mode_operation(dut):
    """Test idle mode operation"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_idle_mode_operation()
    assert result, "Idle mode operation test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_channel_wait_operation(dut):
    """Test channel wait operation"""
    tb = SchedulerTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_channel_wait_operation()
    assert result, "Channel wait operation test failed"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_scheduler_test_params():
    """Generate test parameters for scheduler tests.

    Returns list of tuples: (channel_id, num_channels, data_width, credit_width)
    """
    return [
        # Standard configuration
        (0, 8, 512, 8),
    ]


scheduler_params = generate_scheduler_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - AMBA PATTERN
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_0(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 0"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_0",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_1(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 1"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_1",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_2(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 2"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_2",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_3(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 3"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_3",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_4(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 4"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_4",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_5(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 5"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_5",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_6(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 6"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_6",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_7(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 7"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_7",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_8(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 8"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_8",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_9(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 9"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_9",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_10(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 10"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_10",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_11(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 11"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_11",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_12(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 12"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_12",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_13(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 13"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_13",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_14(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 14"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_14",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_15(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test exponential encoding value 15"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_value_15",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_exponential_encoding_comprehensive(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test all 16 exponential encoding values"""
    _run_scheduler_test(request, "cocotb_test_exponential_encoding_all_values",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Credit Management
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_credit_decrement(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test credit decrement on descriptor acceptance"""
    _run_scheduler_test(request, "cocotb_test_credit_decrement_on_acceptance",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_credit_increment(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test credit increment"""
    _run_scheduler_test(request, "cocotb_test_credit_increment",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.credit
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_credit_exhaustion(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test credit exhaustion"""
    _run_scheduler_test(request, "cocotb_test_credit_exhaustion",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_credit_disabled(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test with credit disabled"""
    _run_scheduler_test(request, "cocotb_test_credit_disabled",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Descriptor Flow
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_basic_flow(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test basic descriptor flow"""
    _run_scheduler_test(request, "cocotb_test_basic_descriptor_flow",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_rda(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test RDA completion"""
    _run_scheduler_test(request, "cocotb_test_rda_completion",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_eos(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test EOS handling"""
    _run_scheduler_test(request, "cocotb_test_eos_handling",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_ctrl_seq(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test control sequencing (ctrlrd, ctrlwr) - RENAMED from program"""
    _run_scheduler_test(request, "cocotb_test_ctrl_sequencing",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_desc_chain(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test descriptor chaining"""
    _run_scheduler_test(request, "cocotb_test_descriptor_chaining",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Error Handling
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_desc_error(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test descriptor error injection"""
    _run_scheduler_test(request, "cocotb_test_descriptor_error_injection",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_data_error(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test data engine error"""
    _run_scheduler_test(request, "cocotb_test_data_engine_error",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.error
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_prog_error(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test program engine error"""
    _run_scheduler_test(request, "cocotb_test_program_engine_error",
                       channel_id, num_channels, data_width, credit_width)


# NOTE: Timeout test removed - use standalone test_scheduler_timeout.py instead
# @pytest.mark.fub
# @pytest.mark.scheduler
# @pytest.mark.error
# @pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
# def test_timeout(request, channel_id, num_channels, data_width, credit_width):
#     """Pytest: Test timeout detection"""
#     _run_scheduler_test(request, "cocotb_test_timeout_detection",
#                        channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_channel_reset(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test channel reset recovery"""
    _run_scheduler_test(request, "cocotb_test_channel_reset_recovery",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Stress Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_back_to_back(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test back-to-back descriptors"""
    _run_scheduler_test(request, "cocotb_test_back_to_back_descriptors",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_backpressure(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test random backpressure"""
    _run_scheduler_test(request, "cocotb_test_random_backpressure",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_mixed_types(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test mixed packet types"""
    _run_scheduler_test(request, "cocotb_test_mixed_packet_types",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_max_credits(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test maximum credits stress"""
    _run_scheduler_test(request, "cocotb_test_maximum_credits_stress",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.stress
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_min_credits(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test minimum credits stress"""
    _run_scheduler_test(request, "cocotb_test_minimum_credits_stress",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Alignment Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_aligned(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test aligned addresses"""
    _run_scheduler_test(request, "cocotb_test_aligned_addresses",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_unaligned(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test unaligned addresses"""
    _run_scheduler_test(request, "cocotb_test_unaligned_addresses",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_align_backpressure(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test alignment backpressure"""
    _run_scheduler_test(request, "cocotb_test_alignment_backpressure",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - Monitor Bus Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_monitor_gen(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test monitor packet generation"""
    _run_scheduler_test(request, "cocotb_test_monitor_packet_generation",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_monitor_backpressure(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test monitor backpressure"""
    _run_scheduler_test(request, "cocotb_test_monitor_backpressure",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# PYTEST TEST FUNCTIONS - FSM State Tests
# ===========================================================================

@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_fsm_transitions(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test FSM state transitions"""
    _run_scheduler_test(request, "cocotb_test_fsm_state_transitions",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_idle_mode(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test idle mode operation"""
    _run_scheduler_test(request, "cocotb_test_idle_mode_operation",
                       channel_id, num_channels, data_width, credit_width)


@pytest.mark.fub
@pytest.mark.scheduler
@pytest.mark.parametrize("channel_id, num_channels, data_width, credit_width", scheduler_params)
def test_channel_wait(request, channel_id, num_channels, data_width, credit_width):
    """Pytest: Test channel wait operation"""
    _run_scheduler_test(request, "cocotb_test_channel_wait_operation",
                       channel_id, num_channels, data_width, credit_width)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_scheduler_test(request, testcase_name, channel_id, num_channels, data_width, credit_width):
    """Helper function to run scheduler tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        channel_id: Channel ID for this test
        num_channels: Total number of channels
        data_width: Data width in bits
        credit_width: Credit counter width in bits
    """
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub'
    })

    dut_name = "scheduler"

    # Get Verilog sources from file list (replaces manual list)
    # Path is relative to repo_root (main rtldesignsherpa directory)
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub/scheduler.f'
    )

    # Format parameters for unique test name (AMBA pattern with TBBase.format_dec())
    cid_str = TBBase.format_dec(channel_id, 2)
    nc_str = TBBase.format_dec(num_channels, 2)
    dw_str = TBBase.format_dec(data_width, 4)
    cw_str = TBBase.format_dec(credit_width, 2)

    # Extract test name from cocotb function (remove "cocotb_test_" prefix)
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_cid{cid_str}_nc{nc_str}_dw{dw_str}_cw{cw_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    chan_width = (num_channels - 1).bit_length() if num_channels > 1 else 1
    rtl_parameters = {
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': num_channels,
        'CHAN_WIDTH': chan_width,
        'ADDR_WIDTH': 64,
        'DATA_WIDTH': data_width,
        'CREDIT_WIDTH': credit_width,
        'TIMEOUT_CYCLES': 1000,
        'EARLY_WARNING_THRESHOLD': 4,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345),
        'TEST_CHANNEL_ID': str(channel_id),
    }

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,  # From file list
            includes=includes,                 # From file list
            toplevel=dut_name,
            module=module,
            testcase=testcase_name,  # Run specific cocotb test function
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=os.environ.get('ENABLE_WAVEDUMP', '0') == '1',
            keep_files=True,
            compile_args=["-Wno-TIMESCALEMOD"],
        )
        print(f"✓ Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"❌ Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic flow test when executed directly
    import sys
    print("Running basic descriptor flow test...")

    # Simulate pytest parametrize with default values
    class MockRequest:
        pass

    request = MockRequest()
    _run_scheduler_test(request, "cocotb_test_basic_descriptor_flow",
                       channel_id=0, num_channels=8, data_width=512, credit_width=8)
