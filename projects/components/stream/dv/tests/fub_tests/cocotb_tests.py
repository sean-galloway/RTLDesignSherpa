"""
CocoTB test functions for apbtodescr module

This module contains the actual cocotb test functions that are run by cocotb_test.
"""

import cocotb
from cocotb.triggers import Timer
import os
import sys

# Add project testbench classes to path
sys.path.append(os.path.join(os.path.dirname(__file__), '../../tbclasses'))

from apbtodescr_tb import APBToDescrTB


@cocotb.test()
async def test_basic_all_channels(dut):
    """Test basic write to all 8 channels"""
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Test all channels
    result = await tb.test_all_channels()
    assert result, "All channels test failed"

    tb.log.info("✓✓✓ All channels basic test PASSED ✓✓✓")


@cocotb.test()
async def test_backpressure_single(dut):
    """Test single channel with back-pressure"""
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Test channel 0 with 5 cycle stall
    result = await tb.test_backpressure(channel=0, stall_cycles=5)
    assert result, "Back-pressure test failed"

    tb.log.info("✓✓✓ Back-pressure test PASSED ✓✓✓")


@cocotb.test()
async def test_backpressure_multiple(dut):
    """Test multiple channels with varying back-pressure"""
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Test channels 0, 3, 7 with different stalls
    test_cases = [
        (0, 3),   # Channel 0, 3 cycle stall
        (3, 10),  # Channel 3, 10 cycle stall
        (7, 1),   # Channel 7, 1 cycle stall
    ]

    for channel, stall_cycles in test_cases:
        result = await tb.test_backpressure(channel, stall_cycles)
        assert result, f"Back-pressure test failed for channel {channel}"
        await tb.wait_clocks(tb.clk_name, 2)

    tb.log.info("✓✓✓ Multiple back-pressure test PASSED ✓✓✓")


@cocotb.test()
async def test_errors(dut):
    """Test error cases (out-of-range, read)"""
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    # Test out-of-range address
    result1 = await tb.test_out_of_range()
    assert result1, "Out-of-range test failed"

    await tb.wait_clocks(tb.clk_name, 5)

    # Test read request (not supported)
    result2 = await tb.test_read_error()
    assert result2, "Read error test failed"

    tb.log.info("✓✓✓ Error tests PASSED ✓✓✓")


@cocotb.test()
async def test_rapid_fire(dut):
    """Test rapid sequential writes to different channels"""
    tb = APBToDescrTB(dut)
    await tb.setup_clocks_and_reset()

    tb.log.info("Testing rapid-fire writes to multiple channels")

    # Write to channels 0, 1, 2, 3 in quick succession
    for ch in range(4):
        addr = ch * 4
        data = 0x3000_0000 + (ch * 0x1000)

        success, error, cycles, kickoff_hit = await tb.apb_write(addr, data)
        assert success, f"Rapid-fire write to channel {ch} failed"
        assert kickoff_hit, f"kickoff_hit not asserted for channel {ch}"

        # Minimal delay between writes
        await tb.wait_clocks(tb.clk_name, 1)

    tb.log.info("✓✓✓ Rapid-fire test PASSED ✓✓✓")
