# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_counter_bin_load
# Purpose: Test runner for counter_bin_load module.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Test runner for counter_bin_load module.

This module provides pytest test functions for validating a binary counter
with FIFO-optimized wraparound and load capability.

Test Scenarios:
- Basic counting (increment from 0 to MAX-1)
- FIFO wraparound (MSB toggle, lower bits clear)
- Load operation (directly set counter value)
- Load priority over enable
- Hold state when disabled
"""

import os
import sys
import pytest
import cocotb
import random
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles

# Import run function for pytest
from cocotb_test.simulator import run

# Import path utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


##############################################################################
# CocoTB Test Functions
##############################################################################

@cocotb.test()
async def test_basic_counting(dut):
    """Test basic counting from 0 to MAX-1."""
    # Get parameters
    WIDTH = int(dut.WIDTH.value)
    MAX = int(dut.MAX.value)

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.enable.value = 0
    dut.load.value = 0
    dut.load_value.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 2)

    # Enable counting
    dut.enable.value = 1

    # Count and verify
    for expected in range(MAX):
        await RisingEdge(dut.clk)
        curr = int(dut.counter_bin_curr.value)
        assert curr == expected, f"Count mismatch: got {curr}, expected {expected}"

    dut._log.info("✅ Basic counting test PASSED")


@cocotb.test()
async def test_fifo_wraparound(dut):
    """Test FIFO-style wraparound (MSB toggle, lower bits clear)."""
    WIDTH = int(dut.WIDTH.value)
    MAX = int(dut.MAX.value)

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.enable.value = 0
    dut.load.value = 0
    dut.load_value.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 2)

    # Enable counting
    dut.enable.value = 1

    # Count to MAX-1
    for _ in range(MAX):
        await RisingEdge(dut.clk)

    # At this point, counter should be at MAX-1
    # Next cycle should wrap around
    curr_before_wrap = int(dut.counter_bin_curr.value)
    assert curr_before_wrap == (MAX - 1), f"Before wrap: got {curr_before_wrap}, expected {MAX-1}"

    # Trigger wraparound
    await RisingEdge(dut.clk)
    curr_after_wrap = int(dut.counter_bin_curr.value)

    # Extract MSB and lower bits
    msb_mask = 1 << (WIDTH - 1)
    lower_mask = msb_mask - 1

    msb = (curr_after_wrap & msb_mask) >> (WIDTH - 1)
    lower_bits = curr_after_wrap & lower_mask

    # After wraparound: MSB should toggle (0->1), lower bits should be 0
    assert msb == 1, f"MSB should be 1 after first wrap, got {msb}"
    assert lower_bits == 0, f"Lower bits should be 0 after wrap, got {lower_bits}"

    # Continue counting for second wraparound
    for _ in range(MAX):
        await RisingEdge(dut.clk)

    curr_second_wrap = int(dut.counter_bin_curr.value)
    msb_second = (curr_second_wrap & msb_mask) >> (WIDTH - 1)
    lower_bits_second = curr_second_wrap & lower_mask

    # After second wraparound: MSB should toggle back (1->0), lower bits 0
    assert msb_second == 0, f"MSB should be 0 after second wrap, got {msb_second}"
    assert lower_bits_second == 0, f"Lower bits should be 0 after second wrap, got {lower_bits_second}"

    dut._log.info("✅ FIFO wraparound test PASSED")


@cocotb.test()
async def test_load_operation(dut):
    """Test load operation to directly set counter value."""
    WIDTH = int(dut.WIDTH.value)
    MAX = int(dut.MAX.value)

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.enable.value = 0
    dut.load.value = 0
    dut.load_value.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 2)

    # Test load various values (within WIDTH range)
    test_values = [5, MAX-3, 0, MAX-1]

    for load_val in test_values:
        dut.load.value = 1
        dut.load_value.value = load_val
        await RisingEdge(dut.clk)
        dut.load.value = 0

        # Wait one more cycle for load to take effect
        await RisingEdge(dut.clk)

        curr = int(dut.counter_bin_curr.value)
        assert curr == load_val, f"Load failed: got {curr}, expected {load_val}"

    dut._log.info("✅ Load operation test PASSED")


@cocotb.test()
async def test_load_priority(dut):
    """Test that load takes priority over enable."""
    WIDTH = int(dut.WIDTH.value)
    MAX = int(dut.MAX.value)

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.enable.value = 0
    dut.load.value = 0
    dut.load_value.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 2)

    # Set counter to known value
    load_val1 = min(10, MAX-2)  # Ensure value fits in WIDTH
    dut.load.value = 1
    dut.load_value.value = load_val1
    await RisingEdge(dut.clk)
    dut.load.value = 0
    await RisingEdge(dut.clk)  # Wait for load to take effect

    # Assert both enable and load (load should win)
    load_val2 = min(MAX-1, 15)  # Ensure value fits in WIDTH
    dut.enable.value = 1
    dut.load.value = 1
    dut.load_value.value = load_val2
    await RisingEdge(dut.clk)
    dut.load.value = 0
    await RisingEdge(dut.clk)  # Wait for load to take effect

    curr = int(dut.counter_bin_curr.value)
    # Should be load_val2, not load_val1+1 (load takes priority over enable)
    assert curr == load_val2, f"Load priority failed: got {curr}, expected {load_val2} (not {load_val1+1})"

    dut._log.info("✅ Load priority test PASSED")


@cocotb.test()
async def test_hold_when_disabled(dut):
    """Test that counter holds value when enable=0."""
    WIDTH = int(dut.WIDTH.value)
    MAX = int(dut.MAX.value)

    # Start clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Reset
    dut.rst_n.value = 0
    dut.enable.value = 0
    dut.load.value = 0
    dut.load_value.value = 0
    await ClockCycles(dut.clk, 5)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 2)

    # Load a value
    dut.load.value = 1
    dut.load_value.value = 15
    await RisingEdge(dut.clk)
    dut.load.value = 0

    # Disable and wait several cycles
    dut.enable.value = 0
    for _ in range(10):
        await RisingEdge(dut.clk)
        curr = int(dut.counter_bin_curr.value)
        assert curr == 15, f"Counter changed while disabled: got {curr}, expected 15"

    dut._log.info("✅ Hold when disabled test PASSED")


##############################################################################
# Pytest Test Cases
##############################################################################

def generate_test_parameters():
    """
    Generate test parameter combinations.

    Returns:
        List of tuples: (width, max_value, test_id)
    """
    test_params = []

    # Various width and MAX combinations
    configs = [
        # (WIDTH, MAX, Description)
        (3,  4,   "min-fifo"),      # Minimal FIFO (2-bit address + MSB)
        (4,  8,   "small-fifo"),    # Small FIFO (8 entries)
        (5,  16,  "medium-fifo"),   # Medium FIFO (16 entries)
        (6,  32,  "large-fifo"),    # Large FIFO (32 entries)
        (4,  10,  "non-pow2"),      # Non-power-of-2 MAX
    ]

    for width, max_val, test_id in configs:
        test_params.append((width, max_val, test_id))

    return test_params


@pytest.mark.parametrize("width, max_value, test_id",
                         generate_test_parameters())
def test_counter_bin_load(request, width, max_value, test_id):
    """
    Pytest test runner for counter_bin_load with parameterization.

    Args:
        request: pytest request fixture
        width: Counter bit width
        max_value: Maximum count value (wraps at max_value-1)
        test_id: Test configuration identifier
    """

    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common'})

    # DUT information
    dut_name = "counter_bin_load"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_cmn'], f"{dut_name}.sv")
    ]
    toplevel = dut_name

    # Create human-readable test identifier
    test_name_plus_params = f"test_counter_bin_load_w{width}_max{max_value}_{test_id}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(width),
        'MAX': str(max_value)
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(random.randint(0, 100000)),
    }

    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    sim_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = ["+trace"]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running test: width={width}, max={max_value}, id={test_id}")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=[],
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✓ Test PASSED: width={width}, max={max_value}, id={test_id}")
    except Exception as e:
        print(f"✗ Test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms run: {cmd_filename}")
        raise


##############################################################################
# Smoke Test
##############################################################################

def test_counter_bin_load_smoke():
    """
    Quick smoke test with minimal configuration.

    This test bypasses pytest parameterization for rapid iteration.
    """
    import types
    fake_request = types.SimpleNamespace()

    test_counter_bin_load(
        request=fake_request,
        width=4,
        max_value=8,
        test_id="smoke"
    )


if __name__ == "__main__":
    """
    Allow running tests directly: python test_counter_bin_load.py
    """
    pytest.main([__file__, "-v", "-s"])
