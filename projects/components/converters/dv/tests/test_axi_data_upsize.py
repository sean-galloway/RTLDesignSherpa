"""
Pytest test runner for axi_data_upsize module
Tests various width configurations and modes
"""

import pytest
import cocotb
from cocotb_test.simulator import run
import os
import sys

# Import testbench class (PYTHONPATH configured in env_python)
from tbclasses.axi_data_upsize_tb import AXIDataUpsizeTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


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

    # Get directory and module information using repository standard
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
    })

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



    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/converters/rtl/filelists/axi_data_upsize.f'
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
    sim_build = os.path.join(tests_dir, 'local_sim_build', f'test_axi_data_upsize_{description}')
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
        module="test_axi_data_upsize",  # This file contains @cocotb.test() functions
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
async def cocotb_test_basic_accumulation(dut):
    """Test basic narrow→wide accumulation"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_basic_accumulation(num_transactions=20)


@cocotb.test()
async def cocotb_test_early_last(dut):
    """Test early termination with narrow_last"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_early_last(num_transactions=15)


@cocotb.test()
async def cocotb_test_backpressure(dut):
    """Test backpressure handling"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_backpressure(num_transactions=10)


@cocotb.test()
async def cocotb_test_continuous_streaming(dut):
    """Test continuous streaming without gaps"""
    tb = AXIDataUpsizeTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.test_continuous_streaming(num_wide_beats=30)


if __name__ == "__main__":
    # Run pytest when executed directly
    pytest.main([__file__, "-v", "-s"])
