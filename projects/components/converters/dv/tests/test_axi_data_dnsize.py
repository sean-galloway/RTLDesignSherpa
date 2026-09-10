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
from TBClasses.shared.utilities import get_paths, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import reg_level_grid, level_env


# Test parameter combinations
test_params = [
    # (wide_width, narrow_width, wide_sb, narrow_sb, sb_broadcast, track_bursts, description)

    (128, 32, 16, 4, 0, 0, "128to32_wstrb_slice_simple"),
    (256, 64, 32, 8, 0, 0, "256to64_wstrb_slice_simple"),
    (128, 32, 2, 2, 1, 0, "128to32_rresp_broadcast_simple"),
    (256, 64, 2, 2, 1, 0, "256to64_rresp_broadcast_simple"),
    (128, 32, 2, 2, 1, 1, "128to32_rresp_burst_track"),
    (256, 64, 2, 2, 1, 1, "256to64_rresp_burst_track"),
    (512, 128, 2, 2, 1, 1, "512to128_rresp_burst_track"),
    (128, 64, 0, 0, 1, 0, "128to64_no_sideband_simple"),

]


# REG_LEVEL selects the grid (how many cells); TEST_LEVEL sets the depth of
# each one. The counts step by roughly 4x so the three levels are not three
# names for one run. 'func' holds the counts this file ran at before the axis
# existed, so today's coverage is preserved and gate/full are added around it.
_DEPTH = {
    'gate': {'splitting': 5, 'throughput': 16, 'bursts': 2, 'burst_wide': 8,
             'last_prop': 3, 'burst_track': 4, 'backpressure': 3, 'streaming': 8},
    'func': {'splitting': 20, 'throughput': 64, 'bursts': 8, 'burst_wide': 8,
             'last_prop': 10, 'burst_track': 15, 'backpressure': 10, 'streaming': 30},
    'full': {'splitting': 80, 'throughput': 256, 'bursts': 32, 'burst_wide': 16,
             'last_prop': 40, 'burst_track': 60, 'backpressure': 40, 'streaming': 120},
}


def _depth():
    """Depth for this cocotb process, from the TEST_LEVEL the wrapper exported."""
    level = os.environ.get('TEST_LEVEL', 'gate').lower()
    return _DEPTH.get(level, _DEPTH['gate'])


def get_test_name(params):
    """Generate test name from parameters"""
    wide_w, narrow_w, wide_sb, narrow_sb, sb_bc, track, desc = params
    return desc


@pytest.mark.parametrize("test_level", reg_level_grid())
@pytest.mark.parametrize("params", test_params, ids=[get_test_name(p) for p in test_params])
def test_axi_data_dnsize(request, params, test_level):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """
    Test axi_data_dnsize with various configurations
    """
    wide_width, narrow_width, wide_sb_width, narrow_sb_width, sb_broadcast, track_bursts, description = params

    # Get directory and module information using repository standard
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_converters': 'projects/components/converters/rtl',
    })

    dut_module = "axi_data_dnsize"

    # Generate unique test name
    test_name = f"test_axi_data_dnsize_{description}_{test_level}"

    # Verilog parameters
    parameters = {
        "WIDE_WIDTH": wide_width,
        "NARROW_WIDTH": narrow_width,
        "WIDE_SB_WIDTH": wide_sb_width,
        "NARROW_SB_WIDTH": narrow_sb_width,
        "SB_BROADCAST": sb_broadcast,
        "TRACK_BURSTS": track_bursts,
        "BURST_LEN_WIDTH": 8,
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
    sim_build = sim_build_path(tests_dir, f'test_axi_data_dnsize_{description}_{test_level}')
    os.makedirs(sim_build, exist_ok=True)

    # Conditionally set COCOTB_TRACE_FILE for VCD generation
    extra_env = dict(level_env(test_level))
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
        waves=enable_waves,  # VCD controlled by compile_args, not cocotb-test
        gui=False,
        keep_files=True,
        compile_args=compile_args,
        sim_args=sim_args,
        plus_args=['--trace'] if enable_waves else [],
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
    assert await tb.test_basic_splitting(num_transactions=_depth()['splitting']), 'scenario reported failure'


@cocotb.test()
async def cocotb_test_throughput(dut):
    """Measure sustained throughput -- the book claims single buffer loses
    a cycle per wide beat, which the RTL's ready logic contradicts."""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    rate = await tb.measure_throughput(wide_beats=_depth()['throughput'], label="no-backpressure")
    # None means the mode is out of scope for this measurement, not a failure
    if rate is not None:
        assert rate > 0.5, f"throughput collapsed to {rate:.3f} beats/cycle"

    # TRACK_BURSTS pays per burst, not per beat -- measured separately
    burst_rate = await tb.measure_burst_throughput(bursts=_depth()['bursts'],
                                                   wide_per_burst=_depth()['burst_wide'],
                                                   label="framed-bursts")
    if burst_rate is not None:
        assert burst_rate > 0.5, f"burst throughput collapsed to {burst_rate:.3f}"


@cocotb.test()
async def cocotb_test_last_propagation(dut):
    """Test that wide_last propagates to last narrow beat (simple mode)"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.test_last_propagation(num_transactions=_depth()['last_prop']), 'scenario reported failure'


@cocotb.test()
async def cocotb_test_burst_tracking(dut):
    """Test burst tracking mode for correct LAST generation"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.test_burst_tracking(num_bursts=_depth()['burst_track']), 'scenario reported failure'
    # isolation: no wide_last, so only the burst counter can assert LAST
    assert await tb.test_burst_len_drives_last(wide_beats=4)


@cocotb.test()
async def cocotb_test_backpressure(dut):
    """Test backpressure handling"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.test_backpressure(num_transactions=_depth()['backpressure']), 'scenario reported failure'


@cocotb.test()
async def cocotb_test_continuous_streaming(dut):
    """Test continuous streaming without gaps"""
    tb = AXIDataDnsizeTB(dut)
    await tb.setup_clocks_and_reset()
    assert await tb.test_continuous_streaming(num_wide_beats=_depth()['streaming']), 'scenario reported failure'


if __name__ == "__main__":
    # Run pytest when executed directly
    pytest.main([__file__, "-v", "-s"])
