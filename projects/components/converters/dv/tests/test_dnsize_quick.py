"""
Quick verification test for axi_data_dnsize - reduced transaction counts
"""

import pytest
import cocotb
from cocotb_test.simulator import run
import os
import sys

# Import testbench class (PYTHONPATH configured in env_python)
from tbclasses.axi_data_dnsize_tb import AXIDataDnsizeTB
from CocoTBFramework.tbclasses.shared.utilities import get_paths
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


@cocotb.test()
async def cocotb_test_basic_splitting(dut):
    """Test basic wide→narrow splitting with just 3 transactions - prefix to prevent pytest collection"""
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

    # Get directory and module information using repository standard
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
    })

    parameters = {
        "WIDE_WIDTH": wide_width,
        "NARROW_WIDTH": narrow_width,
        "WIDE_SB_WIDTH": wide_sb_width,
        "NARROW_SB_WIDTH": narrow_sb_width,
        "SB_BROADCAST": sb_broadcast,
        "TRACK_BURSTS": track_bursts,
        "BURST_LEN_WIDTH": 8
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
    sim_build = os.path.join(tests_dir, 'local_sim_build', f'test_dnsize_quick_{description}')
    os.makedirs(sim_build, exist_ok=True)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    extra_env = {}
    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.vcd')

    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel="axi_data_dnsize",
        module="test_dnsize_quick",
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


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
