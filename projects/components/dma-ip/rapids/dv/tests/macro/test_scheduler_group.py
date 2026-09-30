# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_scheduler_group
# Purpose: RAPIDS Beats Scheduler Group Macro Validation Test - Phase 1
#
# Documentation: projects/components/dma-ip/rapids/PRD.md
# Subsystem: rapids_macro
#
# Author: sean galloway
# Created: 2025-01-10

"""
RAPIDS Beats Scheduler Group Macro Validation Test - Phase 1

Test suite for the scheduler_group module which wraps:
- Descriptor Engine (fetches descriptors via AXI, provides to scheduler)
- Scheduler (processes descriptors, issues data path commands)
- MonBus Arbiter (aggregates monitor packets from 2 sources)

Features tested:
- APB descriptor kick-off interface
- Descriptor AXI read interface
- Scheduler data path interfaces (rd/wr)
- Completion strobe handling
- MonBus event aggregation

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

# Import REUSABLE testbench class from PROJECT AREA (NOT framework!)
from projects.components.dma_ip.rapids.dv.tbclasses.scheduler_group_tb import SchedulerGroupTB


# ===========================================================================
# BASIC FUNCTIONALITY TESTS
# ===========================================================================

@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_idle_state(dut):
    """Test that system starts in idle state after reset"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_idle_state()
    report_ok = tb.generate_test_report()
    assert result and report_ok, "Idle state test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_config_interface(dut):
    """Test configuration interface"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_config_interface()
    report_ok = tb.generate_test_report()
    assert result and report_ok, "Configuration interface test failed"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_basic_descriptor_flow(dut):
    """Test basic descriptor fetch and processing"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_basic_descriptor_flow(num_descriptors=_profile_depth('sg_descriptors'))
    report_ok = tb.generate_test_report()
    assert result and report_ok, "Basic descriptor flow test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_ctrl_write_doorbell(dut):
    """CTRL_WRITE descriptor -> real ctrlwr engine posts a doorbell"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_ctrl_write_doorbell()
    report_ok = tb.generate_test_report()
    assert result and report_ok, "Control write doorbell test failed"


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def cocotb_test_ctrl_read_gate(dut):
    """CTRL_READ descriptor -> real ctrlrd engine gates the chain until match"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_ctrl_read_gate()
    report_ok = tb.generate_test_report()
    assert result and report_ok, "Control read gate test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_monbus_events(dut):
    """Test monitor bus event generation"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_monbus_events(wait_cycles=50)
    report_ok = tb.generate_test_report()
    assert result and report_ok, "MonBus events test failed: no packet seen on the group's monitor bus"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_compl_enable_gate(dut):
    """SCHED_CONFIG.COMPL_EN gates the group's CORE Completion packets (rapids ISSUE-005)"""
    tb = SchedulerGroupTB(dut)
    await tb.setup_clocks_and_reset()
    await tb.initialize_test()
    result = await tb.test_compl_enable_gate(wait_cycles=50)
    report_ok = tb.generate_test_report()
    assert result, "COMPL_EN gate test failed: see the OFF/ON completion counts in the log"
    assert report_ok, "COMPL_EN gate test: the report recorded errors"


# ===========================================================================
# PARAMETER GENERATION - AMBA PATTERN
# ===========================================================================

def generate_scheduler_group_test_params():
    """Generate test parameters for scheduler_group tests.

    Returns list of tuples: (channel_id, addr_width, data_width, axi_id_width, timing_profile)

    timing_profile sweeps the APB descriptor-kick GAXI master valid_delay
    (descriptor-request injection rate). REG_LEVEL gates the sweep breadth.
    """
    base_configs = [
        (0, 64, 512, 8),   # Default configuration
        (3, 64, 512, 8),   # Alternative channel ID
        (0, 64, 256, 8),   # Smaller data width
    ]

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        sweep_profiles = []
    elif reg_level == 'FUNC':
        sweep_profiles = ['slow_producer', 'gaxi_realistic']
    else:  # FULL
        sweep_profiles = ['constrained', 'slow_producer', 'gaxi_stress', 'gaxi_realistic']

    params = [cfg + ('default',) for cfg in base_configs]
    for profile in sweep_profiles:
        params.append((0, 64, 512, 8, profile))
    return params


scheduler_group_params = generate_scheduler_group_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS - Basic Functionality
# ===========================================================================

@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_idle_state(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: Test idle state after reset"""
    _run_scheduler_group_test(request, "cocotb_test_idle_state",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_config_interface(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: Test configuration interface"""
    _run_scheduler_group_test(request, "cocotb_test_config_interface",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_basic_descriptor_flow(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: Test basic descriptor fetch and processing"""
    _run_scheduler_group_test(request, "cocotb_test_basic_descriptor_flow",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_ctrl_write_doorbell(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: CTRL_WRITE descriptor -> real ctrlwr engine posts a doorbell"""
    _run_scheduler_group_test(request, "cocotb_test_ctrl_write_doorbell",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_ctrl_read_gate(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: CTRL_READ descriptor -> real ctrlrd engine gates the chain until match"""
    _run_scheduler_group_test(request, "cocotb_test_ctrl_read_gate",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


@pytest.mark.macro
@pytest.mark.scheduler_group
@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_monbus_events(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: Test monitor bus events"""
    _run_scheduler_group_test(request, "cocotb_test_monbus_events",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)

@pytest.mark.parametrize("channel_id, addr_width, data_width, axi_id_width, timing_profile", scheduler_group_params)
@pytest.mark.parametrize("test_level", reg_level_grid())
def test_scheduler_group_compl_enable_gate(request, channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level):
    """Pytest: SCHED_CONFIG.COMPL_EN gates the CORE Completion packets (rapids ISSUE-005)"""
    _run_scheduler_group_test(request, "cocotb_test_compl_enable_gate",
                                     channel_id, addr_width, data_width, axi_id_width, timing_profile, test_level=test_level)


# ===========================================================================
# HELPER FUNCTION - AMBA PATTERN
# ===========================================================================

def _run_scheduler_group_test(request, testcase_name, channel_id, addr_width, data_width, axi_id_width, timing_profile='default', test_level='gate'):
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    """Helper function to run scheduler_group tests with AMBA pattern.

    Args:
        request: pytest request fixture
        testcase_name: Name of cocotb test function to run
        channel_id: Channel ID parameter
        addr_width: Address width
        data_width: Data width
        axi_id_width: AXI ID width
    """
    # Check if coverage collection is enabled via environment variable
    coverage_enabled = os.environ.get('COVERAGE', '0') == '1'

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_macro': '../../rtl/macro'
    })

    dut_name = "scheduler_group"

    # Get Verilog sources from file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/dma-ip/rapids/rtl/filelists/macro/scheduler_group.f'
    )

    # Format parameters for unique test name
    ch_str = TBBase.format_dec(channel_id, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    id_str = TBBase.format_dec(axi_id_width, 2)

    # Extract test name from cocotb function
    test_suffix = testcase_name.replace("cocotb_test_", "")
    test_name_plus_params = f"test_{dut_name}_{test_suffix}_ch{ch_str}_aw{aw_str}_dw{dw_str}_id{id_str}_{timing_profile}_{test_level}"

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
        'CHANNEL_ID': channel_id,
        'NUM_CHANNELS': 8,
        'ADDR_WIDTH': addr_width,
        'DATA_WIDTH': data_width,
        'AXI_ID_WIDTH': axi_id_width,
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
    }
    if timing_profile != 'default':
        extra_env['GAXI_TIMING_PROFILE'] = timing_profile

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    # Build compile args - add coverage if enabled
    compile_args = ["-Wno-TIMESCALEMOD", "-Wno-WIDTH", "-Wno-UNOPTFLAT"]
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
    print("Running basic scheduler_group test...")

    class MockRequest:
        pass

    request = MockRequest()
    _run_scheduler_group_test(request, "cocotb_test_idle_state",
                                    channel_id=0, addr_width=64, data_width=512, axi_id_width=8)
