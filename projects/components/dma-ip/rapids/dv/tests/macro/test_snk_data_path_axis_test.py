# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_sink_data_path_axis_test
# Purpose: RAPIDS Sink Data Path AXIS Test Wrapper Validation
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
# Subsystem: rapids_macro
#
# Author: sean galloway
# Created: 2026-01-10

"""
RAPIDS Sink Data Path AXIS Test Wrapper Validation

Test suite for the sink_data_path_axis_test module which wraps:
- 8x Scheduler instances
- sink_data_path_axis (AXIS slave -> SRAM -> AXI write)

Data Flow:
  8x Descriptor Packets (GAXI) -> 8x Schedulers -> AXIS Slave -> Sink Data Path -> AXI Write

Features tested:
- Descriptor injection via GAXI masters (one per channel)
- Scheduler processing of descriptors
- AXIS packet reception
- AXI4 write operations to memory
- Multi-channel operation
- End-to-end data integrity

STRUCTURE FOLLOWS AMBA PATTERN:
  - CocoTB test functions at top (prefixed with cocotb_)
  - Parameter generation at bottom
  - Pytest wrappers at bottom with @pytest.mark.parametrize
"""

import os
import random
import sys

import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.utilities import get_paths, create_view_cmd, get_repo_root, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.test_levels import level_env, reg_level_grid
from projects.components.dma_ip.rapids.dv.tbclasses.rapids_levels import depth as _profile_depth

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)


# ===========================================================================
# COCOTB TEST FUNCTIONS
# ===========================================================================

@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_basic_descriptor_flow(dut):
    """Test basic descriptor flow through schedulers to sink data path"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_basic_descriptor_flow(num_descriptors=_profile_depth('dp_descriptors'))
    tb.log.info(f"Basic descriptor flow: {stats}")
    assert result, f"Basic descriptor flow test failed: {stats}"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_multi_channel_operation(dut):
    """Test multi-channel operation with concurrent descriptors"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_multi_channel_operation(num_channels=4, descriptors_per_channel=_profile_depth('dp_desc_per_ch'))
    tb.log.info(f"Multi-channel operation: {stats}")
    assert result, f"Multi-channel operation test failed: {stats}"


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_axis_reception(dut):
    """Test AXIS data reception and SRAM buffering"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_axis_reception(num_packets=_profile_depth('dp_packets'))
    tb.log.info(f"AXIS reception: {stats}")
    assert result, f"AXIS reception test failed: {stats}"


@cocotb.test(timeout_time=600, timeout_unit="ms")
async def cocotb_test_axi_write_operations(dut):
    """Test AXI4 write operations to memory"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_axi_write_operations(num_operations=_profile_depth('dp_ops'))
    tb.log.info(f"AXI write operations: {stats}")
    assert result, f"AXI write operations test failed: {stats}"


@cocotb.test(timeout_time=800, timeout_unit="ms")
async def cocotb_test_end_to_end(dut):
    """Test end-to-end data flow: Descriptor -> AXIS -> AXI Write"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_end_to_end_flow(num_transfers=_profile_depth('dp_transfers'))
    tb.log.info(f"End-to-end flow: {stats}")
    assert result, f"End-to-end flow test failed: {stats}"


@cocotb.test(timeout_time=1000, timeout_unit="ms")
async def cocotb_test_stress(dut):
    """Stress test with high throughput"""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    tb.set_timing_profile('stress')

    result, stats = await tb.stress_test(num_operations=_profile_depth('dp_stress_ops'))
    tb.log.info(f"Stress test: {stats}")
    # Allow 90% success rate for stress test
    assert stats['success_rate'] >= 0.9, f"Stress test failed: {stats}"


@cocotb.test(timeout_time=1000, timeout_unit="ms")
async def cocotb_test_byte_packets(dut):
    """rapids TASK-019: byte lengths, byte addresses, partial strobes, the
    packet-length contract."""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_byte_packets()
    tb.log.info(f"Byte packets: {stats}")
    assert result, f"Byte packets failed: {stats}"


@cocotb.test(timeout_time=1000, timeout_unit="ms")
async def cocotb_test_channel_reset(dut):
    """rapids TASK-019: per-channel reset recovers a channel after a length
    mismatch, a B error and an abandoned packet, without disturbing another."""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_channel_reset()
    tb.log.info(f"Channel reset: {stats}")
    assert result, f"Channel reset failed: {stats}"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_residue_full_burst(dut):
    """rapids BUG-009: a partial segment left by a short packet must not make a
    full-depth burst impossible."""
    from projects.components.dma_ip.rapids.dv.tbclasses.snk_data_path_axis_test_tb import SnkDataPathAxisTestTB

    tb = SnkDataPathAxisTestTB(dut, clk=dut.clk, rst_n=dut.rst_n)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()

    result, stats = await tb.test_residue_full_burst()
    tb.log.info(f"Residue then full-depth burst: {stats}")
    assert result, f"Residue then full-depth burst failed: {stats}"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_sink_axis_test_params():
    """Generate test parameters for sink_data_path_axis_test tests.

    Returns list of tuples: (num_channels, addr_width, data_width, axi_id_width, sram_depth)
    """
    configs = [
        # Default configuration
        (8, 64, 512, 8, 4096),
        # Smaller data width
        (8, 64, 256, 8, 4096),
        # Smaller SRAM
        (8, 64, 512, 8, 2048),
    ]
    # All configs at 'default' (preserve existing coverage), plus a BOUNDED
    # BFM delay-profile sweep on the primary config only (these macro tests are
    # slow). Each profile drives the AXI write slave (TIMING_PROFILE), the GAXI
    # descriptor masters (GAXI_TIMING_PROFILE), and the AXIS ingress master
    # (AXIS_PROFILE). Standard names hit AXI+GAXI+AXIS; gaxi_* hit GAXI.
    profiles = ['constrained', 'slow_producer', 'burst_pause', 'high_throughput',
                'gaxi_backpressure', 'gaxi_stress']
    params = [cfg + ('default',) for cfg in configs]
    params += [configs[0] + (p,) for p in profiles]
    return params


sink_axis_test_params = generate_sink_axis_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_basic_descriptor_flow(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Test basic descriptor flow"""
    _run_sink_axis_test(request, "cocotb_test_basic_descriptor_flow",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_multi_channel_operation(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Test multi-channel operation"""
    _run_sink_axis_test(request, "cocotb_test_multi_channel_operation",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axis_reception(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Test AXIS reception"""
    _run_sink_axis_test(request, "cocotb_test_axis_reception",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_axi_write_operations(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Test AXI write operations"""
    _run_sink_axis_test(request, "cocotb_test_axi_write_operations",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_end_to_end(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Test end-to-end flow"""
    _run_sink_axis_test(request, "cocotb_test_end_to_end",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile", sink_axis_test_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_stress(request, num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level):
    """Pytest: Stress test"""
    _run_sink_axis_test(request, "cocotb_test_stress",
                        num_channels, addr_width, data_width, axi_id_width, sram_depth, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_byte_packets(request, test_level):
    """Pytest: rapids TASK-019 -- byte-granular packets on the Genesys 2 shape,
    at every level."""
    _run_sink_axis_test(request, "cocotb_test_byte_packets",
                        8, 64, 256, 8, 1024, 'default', test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_channel_reset(request, test_level):
    """Pytest: rapids TASK-019 -- per-channel reset on the Genesys 2 shape."""
    _run_sink_axis_test(request, "cocotb_test_channel_reset",
                        8, 64, 256, 8, 1024, 'default', test_level=test_level)


@pytest.mark.macro
@pytest.mark.sink_data_path_axis_test
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_residue_full_burst(request, test_level):
    """Pytest: rapids BUG-009 -- a short packet, then bursts equal to the buffer
    depth, on the Genesys 2 shape (256-bit, 128-deep per channel: SRAM_DEPTH here
    is the total over 8 channels). One cell at every level: it is the
    regression for a board deadlock."""
    _run_sink_axis_test(request, "cocotb_test_residue_full_burst",
                        8, 64, 256, 8, 1024, 'default', test_level=test_level)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_sink_axis_test(request, testcase_name, num_channels, addr_width, data_width, axi_id_width, sram_depth,
                        timing_profile='default', test_level='gate'):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Helper function to run sink_data_path_axis_test tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        num_channels: Number of channels
        addr_width: Address width
        data_width: Data width
        axi_id_width: AXI ID width
        sram_depth: SRAM depth (total across all channels)
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro': '../../rtl/macro'
    })

    dut_name = "snk_data_path_axis_test"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis_test.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    id_str = TBBase.format_dec(axi_id_width, 2)
    sd_str = TBBase.format_dec(sram_depth, 4)

    # Extract test name from cocotb function
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_nc{nc_str}_aw{aw_str}_dw{dw_str}_id{id_str}_sd{sd_str}_{timing_profile}_{test_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': num_channels,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': axi_id_width,
        'SRAM_DEPTH': sram_depth,
    }

    extra_env = {
        'LOG_PATH': log_path,
        'TRACE_FILE': os.path.join(sim_build, 'dump.fst'),
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'COCOTB_LOG_LEVEL': 'INFO',
        **level_env(test_level),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_AXI_ID_WIDTH': str(axi_id_width),
        'TEST_NUM_CHANNELS': str(num_channels),
        'TEST_SRAM_DEPTH': str(sram_depth),
        'TEST_ALLOC_SIZE': os.environ.get('TEST_ALLOC_SIZE', '16'),
    }

    # BFM delay-profile sweep: drive the AXI write slave (TIMING_PROFILE) and the
    # GAXI descriptor masters (GAXI_TIMING_PROFILE). 'default' leaves the TB
    # defaults in place.
    if timing_profile != 'default':
        extra_env['TIMING_PROFILE'] = timing_profile
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT", "-Wno-CASEINCOMPLETE"]
    if coverage_enabled:
        compile_args.extend([
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase=testcase_name,
            parameters=rtl_parameters,
            simulator="verilator",
            sim_build=sim_build,
            extra_env=extra_env,
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            plus_args=['--trace'] if enable_waves else [],
        )
        print(f"Test completed! Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"  View command: {cmd_filename}")
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs: {log_path}")
        if os.path.exists(cmd_filename):
            print(f"View command: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Run basic test when executed directly
    print("Running basic sink_data_path_axis_test test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_sink_axis_test(request, "cocotb_test_basic_descriptor_flow",
                        num_channels=8, addr_width=64, data_width=512, axi_id_width=8, sram_depth=4096)
