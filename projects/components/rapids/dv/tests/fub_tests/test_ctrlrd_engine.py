# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ctrlrd_engine
# Purpose: RAPIDS Control Read Engine FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Control Read Engine FUB Test

Tests the control read engine functional unit block that manages pre-descriptor
read operations:
- 7-state FSM (IDLE → ISSUE_ADDR → WAIT_DATA → COMPARE → RETRY_WAIT → MATCH/ERROR)
- Read-and-compare with configurable mask
- Automatic retry mechanism (configurable 0-511 retries)
- 1µs delay between retries
- Null address support (64'h0 = immediate success)
- AXI4 read interface with channel-based ID routing
- Error handling (max retries, AXI response errors)

Architecture:
- Scheduler Interface: ctrlrd_valid/ready, addr, expected_data, mask, result
- AXI4 Read Interface: AR and R channels (32-bit reads)
- Configuration: Max retry count, channel reset
- MonBus: Completion, retry, and error events

This test follows the standardized RAPIDS test pattern:
1. CocoTB test functions at top (prefix with cocotb_)
2. Parameter generation in middle
3. Pytest wrappers at bottom

See: ../../../docs/rapids_spec/ch02_blocks/01_04_ctrlrd_engine.md
"""

import os
import sys
import pytest
import cocotb
from cocotb_test.simulator import run

# Add framework paths
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "bin"))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", ".."))

from tbclasses.ctrlrd_engine_tb import (
    CtrlrdEngineTB,
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
async def cocotb_test_basic_read_match(dut):
    """Test basic read-match operation (first read matches)."""
    tb = CtrlrdEngineTB(dut)
    await tb.setup_clocks_and_reset()

    # Get test profile from environment
    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_basic_read_match(profile)
    assert result, "Basic read-match test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_read_retry_match(dut):
    """Test read-retry-match operation (retry then match)."""
    tb = CtrlrdEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    max_retries = int(os.environ.get('TEST_MAX_RETRIES', '3'))

    result = await tb.test_read_retry_match(profile, max_retries)
    assert result, "Read-retry-match test failed"


@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_null_address(dut):
    """Test null address handling (immediate success)."""
    tb = CtrlrdEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_null_address(profile)
    assert result, "Null address test failed"


@cocotb.test(timeout_time=200, timeout_unit="ms")
async def cocotb_test_masked_comparison(dut):
    """Test masked comparison with various mask patterns."""
    tb = CtrlrdEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    result = await tb.test_masked_comparison(profile)
    assert result, "Masked comparison test failed"


@cocotb.test(timeout_time=300, timeout_unit="ms")
async def cocotb_test_mixed(dut):
    """Test mixed scenarios (all test types)."""
    tb = CtrlrdEngineTB(dut)
    await tb.setup_clocks_and_reset()

    profile_name = os.environ.get('TEST_PROFILE', 'fixed_delay')
    profile = DelayProfile(profile_name)

    num_ops = int(os.environ.get('TEST_NUM_OPS', '1'))

    result = await tb.run_test_suite(TestScenario.MIXED, profile, num_ops)
    assert result, "Mixed scenario test failed"


# ===========================================================================
# PARAMETER GENERATION
# ===========================================================================

def generate_ctrlrd_engine_test_params():
    """
    Generate test parameters for control read engine tests.

    Returns list of tuples: (num_channels, addr_width, test_scenario, delay_profile, max_retries)
    """
    params = []

    # Standard configuration
    num_channels = 32
    addr_width = 64

    # Test configurations:
    # (scenario, profile, max_retries)
    test_configs = [
        # Basic scenarios - quick validation
        (TestScenario.BASIC_READ_MATCH, DelayProfile.FIXED_DELAY, 3),
        (TestScenario.NULL_ADDRESS, DelayProfile.FIXED_DELAY, 3),
        (TestScenario.MASKED_COMPARISON, DelayProfile.FIXED_DELAY, 3),

        # Retry scenarios - different timing profiles
        (TestScenario.READ_RETRY_MATCH, DelayProfile.MINIMAL_DELAY, 3),
        (TestScenario.READ_RETRY_MATCH, DelayProfile.FAST_CONSUMER, 5),
        (TestScenario.READ_RETRY_MATCH, DelayProfile.BACKPRESSURE, 3),

        # Comprehensive scenarios
        (TestScenario.MIXED, DelayProfile.FIXED_DELAY, 3),
    ]

    for scenario, profile, max_retries in test_configs:
        params.append((num_channels, addr_width, scenario, profile, max_retries))

    return params


ctrlrd_engine_params = generate_ctrlrd_engine_test_params()


# ===========================================================================
# PYTEST WRAPPER FUNCTIONS
# ===========================================================================

@pytest.mark.parametrize("num_channels, addr_width, scenario, profile, max_retries",
                        ctrlrd_engine_params)
def test_ctrlrd_engine(request, num_channels, addr_width, scenario, profile, max_retries):
    """
    Control Read Engine FUB test runner.

    Tests all scenarios with various timing profiles.
    """

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': 'projects/components/rapids/rtl/rapids_fub',
        'rtl_rapids_includes': 'projects/components/rapids/rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "ctrlrd_engine"
    toplevel = dut_name

    # RTL source files
    verilog_sources = [
        # Package files must be compiled first
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes', 'rapids_pkg.sv'),
        # Main module
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'rapids_fub', f'{dut_name}.sv'),
        # Dependencies for AXI
        os.path.join(repo_root, 'rtl', 'amba', 'gaxi', 'gaxi_skid_buffer.sv'),
    ]

    # Include directories
    includes = [
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes'),
        os.path.join(repo_root, 'rtl', 'amba', 'includes'),
        os.path.join(repo_root, 'rtl', 'common', 'includes')
    ]

    # Format parameters for unique test name
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    scenario_str = scenario.value
    profile_str = profile.value
    mr_str = TBBase.format_dec(max_retries, 2)

    test_name_plus_params = f"test_{dut_name}_nc{nc_str}_aw{aw_str}_{scenario_str}_{profile_str}_mr{mr_str}"

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
        TestScenario.BASIC_READ_MATCH: "cocotb_test_basic_read_match",
        TestScenario.READ_RETRY_MATCH: "cocotb_test_read_retry_match",
        TestScenario.NULL_ADDRESS: "cocotb_test_null_address",
        TestScenario.MASKED_COMPARISON: "cocotb_test_masked_comparison",
        TestScenario.MIXED: "cocotb_test_mixed",
    }
    testcase = testcase_map[scenario]

    # Environment variables
    extra_env = {
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_PROFILE': profile.value,
        'TEST_MAX_RETRIES': str(max_retries),
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

        print(f"✓ Control Read Engine test completed!")
        print(f"  Scenario:     {scenario.value}")
        print(f"  Profile:      {profile.value}")
        print(f"  Max Retries:  {max_retries}")
        print(f"  Logs:         {log_path}")
        print(f"  Waves:        {cmd_filename}")

    except Exception as e:
        print(f"❌ Control Read Engine test failed: {str(e)}")
        print(f"  Scenario:     {scenario.value}")
        print(f"  Profile:      {profile.value}")
        print(f"  Logs:         {log_path}")
        print(f"  Waves:        {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Control Read Engine FUB Test")
    print("=" * 70)
    print("Run with:")
    print("  pytest projects/components/rapids/dv/tests/fub_tests/ctrlrd_engine/test_ctrlrd_engine.py -v")
    print("")
    print("Test Scenarios:")
    print("  - Basic Read-Match:   First read matches expected data")
    print("  - Read-Retry-Match:   Retry mechanism with eventual match")
    print("  - Null Address:       Skip operation on 64'h0 address")
    print("  - Masked Comparison:  Various mask patterns")
    print("  - Mixed:              All scenarios combined")
    print("")
    print("Delay Profiles:")
    for profile in DelayProfile:
        print(f"  - {profile.value}")
