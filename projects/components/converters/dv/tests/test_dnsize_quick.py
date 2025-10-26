"""
Quick verification test for axi_data_dnsize - reduced transaction counts
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


@cocotb.test()
async def test_basic_splitting(dut):
    """Test basic wide→narrow splitting with just 3 transactions"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_splitting(num_transactions=3)  # Reduced from 20


@pytest.mark.parametrize("params", [
    (128, 32, 16, 4, 0, 0, "128to32_wstrb"),
    (256, 64, 2, 2, 1, 0, "256to64_rresp"),
], ids=["128to32_wstrb", "256to64_rresp"])
def test_axi_data_dnsize_quick(request, params):
    """Quick test with 2 configurations only"""
    wide_width, narrow_width, wide_sb_width, narrow_sb_width, sb_broadcast, track_bursts, description = params

    rtl_dir = os.path.join(repo_root, "projects/components/converters/rtl")

    parameters = {
        "WIDE_WIDTH": wide_width,
        "NARROW_WIDTH": narrow_width,
        "WIDE_SB_WIDTH": wide_sb_width,
        "NARROW_SB_WIDTH": narrow_sb_width,
        "SB_BROADCAST": sb_broadcast,
        "TRACK_BURSTS": track_bursts,
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
        module="test_dnsize_quick",
        parameters=parameters,
        includes=includes,
        waves=False,
        gui=False
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
