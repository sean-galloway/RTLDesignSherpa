"""
Quick verification test for axi_data_dnsize - reduced transaction counts
"""

import pytest
import cocotb
from cocotb_test.simulator import run
import os
import sys

# Import testbench class from project area
from projects.components.converters.dv.tbclasses.axi_data_dnsize_tb import AXIDataDnsizeTB
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import reg_level_grid, level_env


# This file is the fast smoke path over the same DUT as test_axi_data_dnsize:
# two configurations instead of eight and a short transaction count. It still
# needs the level axis, because REG_LEVEL=FULL must not silently run the smoke
# depth. 'gate' is the count this file has always used.
_SPLIT_COUNT = {'gate': 3, 'func': 12, 'full': 48}


def _depth():
    """Transaction count for this process, from the wrapper's TEST_LEVEL."""
    return _SPLIT_COUNT.get(os.environ.get('TEST_LEVEL', 'gate').lower(), 3)


@cocotb.test()
async def cocotb_test_basic_splitting(dut):
    """Basic wide-to-narrow splitting. Prefixed so pytest does not collect it."""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    # The scenario returns a pass/fail bool; before the level conversion this
    # call discarded it, so the test could not fail on a data mismatch.
    assert await tb.test_basic_splitting(num_transactions=_depth()), \
        'scenario reported failure'


@pytest.mark.parametrize("params", [
    (128, 32, 16, 4, 0, 0, "128to32_wstrb"),
    (256, 64, 2, 2, 1, 0, "256to64_rresp"),
], ids=["128to32_wstrb", "256to64_rresp"])
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi_data_dnsize_quick(request, params, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
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


    # Simulation build directory
    sim_build = sim_build_path(tests_dir, f'test_dnsize_quick_{description}_{test_level}')
    os.makedirs(sim_build, exist_ok=True)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    extra_env = dict(level_env(test_level))
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
        waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
        gui=False,
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=['--trace'] if enable_waves else [],
    )


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
