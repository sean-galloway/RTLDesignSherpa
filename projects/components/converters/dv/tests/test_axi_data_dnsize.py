"""
Pytest test runner for axi_data_dnsize module
Tests various width configurations and modes
"""

import pytest
import cocotb
from cocotb_test.simulator import run
import os
import sys

# Import testbench class from project area
from projects.components.converters.dv.tbclasses.axi_data_dnsize_tb import AXIDataDnsizeTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


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

    # Get directory and module information using repository standard
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
    })

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



    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/axi_data_dnsize.f'
    )

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--trace-depth", "99",
    ]
    sim_args = [
        "--trace",  # VCD waveform format
        "--trace-structs",
        "--trace-depth", "99",
    ]

    plusargs = [
        "--trace",
    ]

    # Simulation build directory
    sim_build = os.path.join(tests_dir, 'local_sim_build', f'test_axi_data_dnsize_{description}')
    os.makedirs(sim_build, exist_ok=True)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    extra_env = {}
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    # Run simulation
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel=dut_module,
        module="test_axi_data_dnsize",  # This file contains @cocotb.test() functions
        parameters=parameters,
        includes=includes,
        sim_build=sim_build,
        extra_env=extra_env,
        waves=False,  # VCD controlled by compile_args, not cocotb-test
        gui=False,
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plusargs=plusargs,
    )


# ==============================================================================
# CocoTB Tests (called by cocotb_test simulator)
# Prefix with "cocotb_test_" to prevent pytest collection
# ==============================================================================

@cocotb.test()
async def cocotb_test_basic_splitting(dut):
    """Test basic wide→narrow splitting"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_splitting(num_transactions=20)


@cocotb.test()
async def cocotb_test_last_propagation(dut):
    """Test that wide_last propagates to last narrow beat (simple mode)"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_last_propagation(num_transactions=10)


@cocotb.test()
async def cocotb_test_burst_tracking(dut):
    """Test burst tracking mode for correct LAST generation"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_burst_tracking(num_bursts=15)


@cocotb.test()
async def cocotb_test_backpressure(dut):
    """Test backpressure handling"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_backpressure(num_transactions=10)


@cocotb.test()
async def cocotb_test_continuous_streaming(dut):
    """Test continuous streaming without gaps"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_continuous_streaming(num_wide_beats=30)


if __name__ == "__main__":
    # Run pytest when executed directly
    pytest.main([__file__, "-v", "-s"])
