# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ctrlwr_engine
# Purpose: RAPIDS Control Write Engine FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Control Write Engine FUB Test

Tests the control write engine functional unit block that manages post-descriptor
write operations:
- 4-state FSM (IDLE → ISSUE_ADDR → ISSUE_DATA → WAIT_RESP)
- Null address support (64'h0 skips operation)
- AXI write interface with channel-based ID routing
- Address validation (4-byte alignment)
- Error handling (address errors, AXI response errors)
- Back-to-back operation throughput

Architecture:
- Scheduler Interface: program_valid/ready, addr, data
- AXI4 Write Interface: AW, W, B channels (32-bit writes)
- Configuration: Channel reset support
- MonBus: Completion and error events

This test follows the standardized RAPIDS test pattern:
1. CocoTB test functions at top (prefix with cocotb_)
2. Parameter generation in middle
3. Pytest wrappers at bottom

See: ../../../docs/rapids_spec/ch02_blocks/01_03_ctrlwr_engine.md
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add framework paths
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "bin"))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", ".."))

from tbclasses.ctrlwr_engine_tb import (
    CtrlwrEngineTB,
    DelayProfile,
    TestScenario
)
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.filelist_utils import get_sources_from_filelist


# ===========================================================================
# COCOTB TEST FUNCTIONS - prefix with "cocotb_" to prevent pytest collection
# ===========================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_basic_write(dut):
    """Test basic program write operation."""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()

    # Get test profile from environment
    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_basic_write(profile)
    assert result, "Basic write test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_null_address(dut):
    """Test null address handling (skip operation)."""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_null_address(profile)
    assert result, "Null address test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_back_to_back(dut):
    """Test multiple back-to-back operations."""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    num_ops = int(os.environ.get('TEST_NUM_OPS', '5'))

    result = await tb.test_back_to_back(num_ops, profile)
    assert result, "Back-to-back test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_misaligned(dut):
    """Test address alignment error detection."""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_misaligned_address(profile)
    assert result, "Misaligned address test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_mixed(dut):
    """Test mixed scenarios (all test types)."""
    tb = CtrlwrEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    num_ops = int(os.environ.get('TEST_NUM_OPS', '5'))

    result = await tb.run_test_suite(TestScenario.MIXED, profile, num_ops)
    assert result, "Mixed scenario test failed"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_ctrlwr_engine_test_params():
    """
    Generate test parameters for control write engine tests.

    Returns list of tuples: (num_channels, addr_width, test_scenario, delay_profile, num_ops)
    """
    params = []

    # Standard configuration
    num_channels = 32
    addr_width = 64

    # Test configurations:
    # (scenario, profile, num_operations)
    test_configs = [
        # Basic scenarios - quick validation
        (TestScenario.BASIC_WRITE, DelayProfile.FIXED_DELAY, 1),
        (TestScenario.NULL_ADDRESS, DelayProfile.FIXED_DELAY, 1),
        (TestScenario.MISALIGNED, DelayProfile.FIXED_DELAY, 1),

        # Throughput scenarios - different timing profiles
        (TestScenario.BACK_TO_BACK, DelayProfile.MINIMAL_DELAY, 5),
        (TestScenario.BACK_TO_BACK, DelayProfile.FAST_CONSUMER, 5),
        (TestScenario.BACK_TO_BACK, DelayProfile.BACKPRESSURE, 5),

        # Comprehensive scenarios
        (TestScenario.MIXED, DelayProfile.FIXED_DELAY, 5),
    ]

    for scenario, profile, num_ops in test_configs:
        params.append((num_channels, addr_width, scenario, profile, num_ops))

    return params


ctrlwr_engine_params = generate_ctrlwr_engine_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("num_channels, addr_width, scenario, profile, num_ops",
                        ctrlwr_engine_params)
def test_ctrlwr_engine(request, num_channels, addr_width, scenario, profile, num_ops):
    """
    Control Write Engine FUB test runner.

    Tests all scenarios with various timing profiles.
    """

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "ctrlwr_engine"
    toplevel = dut_name

    # Get Verilog sources and includes from hierarchical file list
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='projects/components/rapids/rtl/filelists/fub/ctrlwr_engine.f'
    )

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    scenario_str = scenario.value
    profile_str = profile.value
    nop_str = TBBase.format_dec(num_ops, 2)

    test_name_plus_params = f"test_{dut_name}_nc{nc_str}_aw{aw_str}_{scenario_str}_{profile_str}_n{nop_str}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'CHANNEL_ID': '0',
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
        'AXI_ID_WIDTH': '8',
        'MON_AGENT_ID': '8\'h20',
        'MON_UNIT_ID': '4\'h1',
        'MON_CHANNEL_ID': '6\'h0'
    }

    # Determine cocotb test function based on scenario
    testcase_map = {
        TestScenario.BASIC_WRITE: "cocotb_test_basic_write",
        TestScenario.NULL_ADDRESS: "cocotb_test_null_address",
        TestScenario.BACK_TO_BACK: "cocotb_test_back_to_back",
        TestScenario.MISALIGNED: "cocotb_test_misaligned",
        TestScenario.MIXED: "cocotb_test_mixed",
    }
    testcase = testcase_map[scenario]

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_PROFILE': profile.value,
        'TEST_NUM_OPS': str(num_ops),
        'SEED': str(12345)
    }

    # Compilation arguments with VCD tracing enabled (not FST)
    compile_args = [
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR",
        "--trace",  # Enable VCD tracing (not --trace-fst)
        "--trace-depth", "99",  # Full trace depth
        "--trace-structs"  # Trace struct members
    ]

    sim_args = []

    plusargs = []

    # Create waveform viewing command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            testcase=testcase,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Manually enable VCD via --trace compile arg
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ Control Write Engine test completed!")
        print(f"  Scenario: {scenario.value}")
        print(f"  Profile:  {profile.value}")
        print(f"  Ops:      {num_ops}")
        print(f"  Logs:     {log_path}")
        print(f"  Waves:    {cmd_filename}")

    except Exception as e:
        print(f"❌ Control Write Engine test failed: {str(e)}")
        print(f"  Scenario: {scenario.value}")
        print(f"  Profile:  {profile.value}")
        print(f"  Logs:     {log_path}")
        print(f"  Waves:    {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Control Write Engine FUB Test")
    print("=" * 70)
    print("Run with:")
    print("  pytest val/rapids/fub_tests/ctrlwr_engine/test_ctrlwr_engine.py -v")
    print("")
    print("Test Scenarios:")
    print("  - Basic Write:    Single program write operation")
    print("  - Null Address:   Skip operation on 64'h0 address")
    print("  - Misaligned:     Address alignment error detection")
    print("  - Back-to-Back:   Multiple consecutive operations")
    print("  - Mixed:          All scenarios combined")
    print("")
    print("Delay Profiles:")
    for profile in DelayProfile:
        print(f"  - {profile.value}")
