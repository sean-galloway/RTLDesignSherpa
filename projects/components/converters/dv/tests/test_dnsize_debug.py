"""
Simple debug test for axi_data_dnsize
"""

import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer
from cocotb_test.simulator import run
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)


@cocotb.test()
async def test_debug_simple(dut):
    """Ultra-simple test with debug output"""

    # Start clock
    cocotb.start_soon(Clock(dut.aclk, 10, units='ns').start())

    # Initialize
    dut.wide_valid.value = 0
    dut.wide_data.value = 0
    dut.wide_sideband.value = 0
    dut.wide_last.value = 0
    dut.narrow_ready.value = 0

    # Reset
    dut.aresetn.value = 0
    await Timer(50, units='ns')
    dut.aresetn.value = 1
    await Timer(20, units='ns')

    dut._log.info("=== Starting test ===")

    # Send one wide beat (128 bits = 0x33_22_11_00)
    dut.wide_valid.value = 1
    dut.wide_data.value = 0x33333333_22222222_11111111_00000000  # Full 128-bit value
    await RisingEdge(dut.aclk)

    dut._log.info(f"After wide_valid=1: wide_ready={dut.wide_ready.value}")

    while dut.wide_ready.value == 0:
        await RisingEdge(dut.aclk)
        dut._log.info(f"Waiting for wide_ready...")

    dut.wide_valid.value = 0
    dut._log.info("Wide beat accepted")
    dut._log.info(f"RTL state: r_wide_buffered={dut.r_wide_buffered.value}, r_beat_ptr={dut.r_beat_ptr.value}")
    dut._log.info(f"RTL buffer: r_data_buffer=0x{int(dut.r_data_buffer.value):032x}")

    # Try to receive narrow beats
    for i in range(4):  # WIDTH_RATIO=4 (128/32)
        dut._log.info(f"=== Receiving narrow beat {i} ===")
        dut.narrow_ready.value = 1
        await RisingEdge(dut.aclk)

        timeout = 0
        while dut.narrow_valid.value == 0:
            await RisingEdge(dut.aclk)
            timeout += 1
            if timeout > 10:
                dut._log.error(f"TIMEOUT waiting for narrow_valid on beat {i}")
                assert False, f"Timeout on beat {i}"

        data = int(dut.narrow_data.value)
        last = bool(dut.narrow_last.value)
        dut._log.info(f"Beat {i}: data=0x{data:08x}, last={last}")
        dut._log.info(f"  RTL state: r_wide_buffered={dut.r_wide_buffered.value}, r_beat_ptr={dut.r_beat_ptr.value}")

        # Deassert ready immediately after handshake (no extra clock!)
        dut.narrow_ready.value = 0

    dut._log.info("=== Test complete ===")


def test_dnsize_debug():
    """Pytest wrapper"""
    rtl_dir = os.path.join(repo_root, "projects/components/converters/rtl")

    parameters = {
        "WIDE_WIDTH": 128,
        "NARROW_WIDTH": 32,
        "WIDE_SB_WIDTH": 0,
        "NARROW_SB_WIDTH": 0,
        "SB_BROADCAST": 1,
        "TRACK_BURSTS": 0,
        "BURST_LEN_WIDTH": 8
    }

    includes = [
        os.path.join(repo_root, "rtl/amba/includes"),
        os.path.join(repo_root, "rtl/common")
    ]

    run(
        python_search=[os.path.dirname(__file__)],
        verilog_sources=[os.path.join(rtl_dir, "axi_data_dnsize.sv")],
        toplevel="axi_data_dnsize",
        module="test_dnsize_debug",
        parameters=parameters,
        includes=includes,
        waves=False,
        gui=False
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
