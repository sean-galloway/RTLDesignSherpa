"""
Pytest test runner for axi_data_dnsize module
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
from projects.components.converters.dv.tbclasses.axi_data_dnsize_tb import AXIDataDnsizeTB


# Test parameter combinations
test_params = [
    # (wide_width, narrow_width, wide_sb, narrow_sb, sb_broadcast, track_bursts, dual_buffer, description)

    # SINGLE-BUFFER MODE (DUAL_BUFFER=0) - Original tests
    (128, 32, 16, 4, 0, 0, 0, "128to32_wstrb_slice_simple"),
    (256, 64, 32, 8, 0, 0, 0, "256to64_wstrb_slice_simple"),
    (128, 32, 2, 2, 1, 0, 0, "128to32_rresp_broadcast_simple"),
    (256, 64, 2, 2, 1, 0, 0, "256to64_rresp_broadcast_simple"),
    (128, 32, 2, 2, 1, 1, 0, "128to32_rresp_burst_track"),
    (256, 64, 2, 2, 1, 1, 0, "256to64_rresp_burst_track"),
    (512, 128, 2, 2, 1, 1, 0, "512to128_rresp_burst_track"),
    (128, 64, 0, 0, 1, 0, 0, "128to64_no_sideband_simple"),

    # DUAL-BUFFER MODE (DUAL_BUFFER=1) - High throughput tests
    (128, 32, 16, 4, 0, 0, 1, "128to32_wstrb_slice_simple_DUAL"),
    (256, 64, 32, 8, 0, 0, 1, "256to64_wstrb_slice_simple_DUAL"),
    (128, 32, 2, 2, 1, 0, 1, "128to32_rresp_broadcast_simple_DUAL"),
    (256, 64, 2, 2, 1, 0, 1, "256to64_rresp_broadcast_simple_DUAL"),
    (128, 32, 2, 2, 1, 1, 1, "128to32_rresp_burst_track_DUAL"),
    (256, 64, 2, 2, 1, 1, 1, "256to64_rresp_burst_track_DUAL"),
    (512, 128, 2, 2, 1, 1, 1, "512to128_rresp_burst_track_DUAL"),
    (128, 64, 0, 0, 1, 0, 1, "128to64_no_sideband_simple_DUAL"),
]


def get_test_name(params):
    """Generate test name from parameters"""
    wide_w, narrow_w, wide_sb, narrow_sb, sb_bc, track, dual_buf, desc = params
    return desc


@pytest.mark.parametrize("params", test_params, ids=[get_test_name(p) for p in test_params])
def test_axi_data_dnsize(request, params):
    """
    Test axi_data_dnsize with various configurations
    """
    wide_width, narrow_width, wide_sb_width, narrow_sb_width, sb_broadcast, track_bursts, dual_buffer, description = params

    # RTL module location
    rtl_dir = os.path.join(repo_root, "projects/components/converters/rtl")
    dut_module = "axi_data_dnsize"

    # Generate unique test name
    test_name = f"test_axi_data_dnsize_{description}"

    # Verilog parameters
    parameters = {
        "WIDE_WIDTH": wide_width,
        "NARROW_WIDTH": narrow_width,
        "WIDE_SB_WIDTH": wide_sb_width,
        "NARROW_SB_WIDTH": narrow_sb_width,
        "SB_BROADCAST": sb_broadcast,
        "TRACK_BURSTS": track_bursts,
        "BURST_LEN_WIDTH": 8,
        "DUAL_BUFFER": dual_buffer
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
        module="test_axi_data_dnsize",  # This file contains @cocotb.test() functions
        parameters=parameters,
        includes=includes,
        waves=False,  # Disable waveforms to avoid FST issues with verilator
        gui=False
    )


# ==============================================================================
# CocoTB Tests (called by cocotb_test simulator)
# ==============================================================================

@cocotb.test()
async def test_basic_splitting(dut):
    """Test basic wide→narrow splitting"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_splitting(num_transactions=20)


@cocotb.test()
async def test_last_propagation(dut):
    """Test that wide_last propagates to last narrow beat (simple mode)"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_last_propagation(num_transactions=10)


@cocotb.test()
async def test_burst_tracking(dut):
    """Test burst tracking mode for correct LAST generation"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_burst_tracking(num_bursts=15)


@cocotb.test()
async def test_backpressure(dut):
    """Test backpressure handling"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_backpressure(num_transactions=10)


@cocotb.test()
async def test_continuous_streaming(dut):
    """Test continuous streaming without gaps"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_continuous_streaming(num_wide_beats=30)


if __name__ == "__main__":
    # Run pytest when executed directly
    pytest.main([__file__, "-v", "-s"])
