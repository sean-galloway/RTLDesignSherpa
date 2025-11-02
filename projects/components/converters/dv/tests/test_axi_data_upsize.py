"""
Pytest test runner for axi_data_upsize module
Tests various width configurations and modes
"""

import pytest
import cocotb
from cocotb_test.simulator import run
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../..'))
sys.path.insert(0, repo_root)

# Import testbench class
from projects.components.converters.dv.tbclasses.axi_data_upsize_tb import AXIDataUpsizeTB


# Test parameter combinations
test_params = [
    # (narrow_width, wide_width, narrow_sb_width, wide_sb_width, sb_or_mode, description)
    (32, 128, 4, 16, 0, "32to128_wstrb_concat"),
    (64, 256, 8, 32, 0, "64to256_wstrb_concat"),
    (32, 64, 2, 2, 1, "32to64_rresp_or"),
    (64, 128, 2, 2, 1, "64to128_rresp_or"),
    (128, 512, 2, 2, 1, "128to512_rresp_or"),
    (32, 256, 0, 0, 0, "32to256_no_sideband"),
]


def get_test_name(params):
    """Generate test name from parameters"""
    narrow_w, wide_w, narrow_sb, wide_sb, sb_or, desc = params
    return desc


@pytest.mark.parametrize("params", test_params, ids=[get_test_name(p) for p in test_params])
def test_axi_data_upsize(request, params):
    """
    Test axi_data_upsize with various configurations
    """
    narrow_width, wide_width, narrow_sb_width, wide_sb_width, sb_or_mode, description = params

    # RTL module location
    rtl_dir = os.path.join(repo_root, "projects/components/converters/rtl")
    dut_module = "axi_data_upsize"

    # Generate unique test name
    test_name = f"test_axi_data_upsize_{description}"

    # Verilog parameters
    parameters = {
        "NARROW_WIDTH": narrow_width,
        "WIDE_WIDTH": wide_width,
        "NARROW_SB_WIDTH": narrow_sb_width,
        "WIDE_SB_WIDTH": wide_sb_width,
        "SB_OR_MODE": sb_or_mode
    }

    # Include paths
    includes = [
        os.path.join(repo_root, "rtl/amba/includes"),
        os.path.join(repo_root, "rtl/common")
    ]

    # Verilog sources
    verilog_sources = [
        os.path.join(rtl_dir, f"{dut_module}.sv")
    ]

    # Run simulation
    run(
        python_search=[os.path.dirname(__file__)],
        verilog_sources=verilog_sources,
        toplevel=dut_module,
        module="test_axi_data_upsize",  # This file contains @cocotb.test() functions
        parameters=parameters,
        includes=includes,
        waves=False,  # Disable waveforms to avoid FST issues with verilator
        gui=False
    )


# ==============================================================================
# CocoTB Tests (called by cocotb_test simulator)
# ==============================================================================

@cocotb.test()
async def test_basic_accumulation(dut):
    """Test basic narrow→wide accumulation"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_accumulation(num_transactions=20)


@cocotb.test()
async def test_early_last(dut):
    """Test early termination with narrow_last"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_early_last(num_transactions=15)


@cocotb.test()
async def test_backpressure(dut):
    """Test backpressure handling"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_backpressure(num_transactions=10)


@cocotb.test()
async def test_continuous_streaming(dut):
    """Test continuous streaming without gaps"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_continuous_streaming(num_wide_beats=30)


if __name__ == "__main__":
    # Run pytest when executed directly
    pytest.main([__file__, "-v", "-s"])
