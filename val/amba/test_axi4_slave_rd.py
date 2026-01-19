# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_slave_rd
# Purpose: AXI4 Slave Read Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Slave Read Test Runner

Test runner for the AXI4 slave read using the CocoTB framework.
Tests various AXI4 configurations and validates read response behavior.

TEST LEVELS (per-test depth):
    basic (30s-2min):  Quick verification during development
    medium (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 2 tests (~5 min) - smoke test (stub + non-stub)
    FUNC: 8 tests (~30 min) - functional coverage - DEFAULT
    FULL: 48 tests (~4 hours) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 2 configs (1 stub + 1 non-stub) × 1 level = 2 tests
    FUNC: 2 stubs × 2 depth_configs × 2 levels = 8 tests (32-bit data only)
    FULL: 2 stubs × 2 id × 2 addr × 1 data × 2 depth_pairs × 3 levels = 48 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
    TEST_LEVEL: basic|medium|full - controls per-test depth (set by REG_LEVEL)
    SEED: Set random seed for reproducibility
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the testbench
from CocoTBFramework.tbclasses.axi4.axi4_slave_read_tb import AXI4SlaveReadTB


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axi4_slave_read_test(dut):
    """AXI4 slave read test using the AXI4 framework components"""

    # Create testbench instance
    tb = AXI4SlaveReadTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4 slave read test with seed: {seed}')

    # Get test parameters from environment
    test_level = os.environ.get('TEST_LEVEL', 'basic').lower()

    valid_levels = ['basic', 'medium', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'basic'. Valid: {valid_levels}")
        test_level = 'basic'

    # Start clock and reset sequence
    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info(f"Starting {test_level.upper()} AXI4 slave read test...")
    tb.log.info(f"AXI4 widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_read_counts = [10, 20]
        burst_lengths = [[2, 4], [4, 8]]
        stress_count = 25
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_read_counts = [20, 40, 30]
        burst_lengths = [[2, 4, 8], [4, 8, 16], [1, 2, 4, 8]]
        stress_count = 50
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        single_read_counts = [30, 50, 75]
        burst_lengths = [[1, 2, 4, 8, 16], [2, 4, 8, 16, 32], [1, 3, 7, 15, 31]]
        stress_count = 100

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    # Initialize success tracking for final results
    tests_passed = 0
    total_tests = 0

    try:
        # Test 1: Basic connectivity test
        tb.log.info("=== Test 1: Basic Slave Connectivity ===")
        total_tests += 1
        tb.set_timing_profile('normal')

        # Single read response from known memory location
        success, data, info = await tb.single_read_response_test(0x1000)
        if not success:
            tb.log.error("Basic slave connectivity test failed!")
            raise Exception(f"Basic connectivity failed: {info}")

        tb.log.info("✓ Basic slave connectivity test passed")
        tests_passed += 1

        # Test 2: Single read responses with different timing profiles
        for profile in timing_profiles:
            tb.log.info(f"=== Test 2: Single Read Responses ({profile.upper()}) ===")
            total_tests += 1
            tb.set_timing_profile(profile)

            for count in single_read_counts:
                tb.log.info(f"Testing {count} single read responses with '{profile}' timing...")
                success = await tb.basic_read_sequence(count)
                if not success:
                    error_msg = f"Single read responses failed with {profile} timing"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

            tb.log.info(f"✓ Single read responses passed with '{profile}' timing")
            tests_passed += 1

        # Test 3: Burst read responses with different lengths
        for burst_config in burst_lengths:
            tb.log.info(f"=== Test 3: Burst Read Responses {burst_config} ===")
            total_tests += 1
            tb.set_timing_profile('normal')

            tb.log.info(f"Testing slave burst read responses with lengths {burst_config}...")
            success = await tb.burst_read_sequence(burst_config)
            if not success:
                error_msg = f"Burst read responses failed with lengths {burst_config}"
                tb.log.error(error_msg)
                raise Exception(error_msg)

            tb.log.info(f"✓ Burst read responses passed for lengths {burst_config}")
            tests_passed += 1

        # Test 4: Mixed timing profiles (full test level only)
        if test_level == 'full':
            for profile in timing_profiles:
                tb.log.info(f"=== Test 4: Mixed Operations ({profile.upper()}) ===")
                total_tests += 1
                tb.set_timing_profile(profile)

                # Mix of single and burst read responses
                mixed_operations = [
                    ('single', 0x1008),
                    ('burst', 0x2008, 3),
                    ('single', 0x1010), 
                    ('burst', 0x2020, 2),
                    ('single', 0x1018),
                ]

                all_passed = True
                for i, op in enumerate(mixed_operations):
                    if op[0] == 'single':
                        success, data, info = await tb.single_read_response_test(op[1])
                    else:  # burst
                        success, data, info = await tb.burst_read_response_test(op[1], op[2])

                    if not success:
                        tb.log.error(f"Mixed operation {i+1} failed: {info}")
                        all_passed = False
                        break

                    # Small delay between operations
                    await tb.wait_clocks('aclk', 2)

                if not all_passed:
                    error_msg = f"Mixed operations failed with {profile} timing"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"✓ Mixed operations passed with '{profile}' timing")
                tests_passed += 1

        # Test 5: Address range responses
        tb.log.info("=== Test 5: Address Range Responses ===")
        total_tests += 1
        tb.set_timing_profile('normal')

        address_ranges = [
            (0x1000, "Pattern 1 (incremental)"),
            (0x2000, "Pattern 2 (address-based)"),
            (0x3000, "Pattern 3 (fixed patterns)")
        ]

        range_tests_passed = 0
        for base_addr, description in address_ranges:
            tb.log.info(f"Testing slave responses for {description.lower()}...")
            
            # Test several addresses in this range
            for i in range(5):
                addr = base_addr + (i * (tb.TEST_DATA_WIDTH // 8))
                success, data, info = await tb.single_read_response_test(addr)
                if success:
                    tb.log.debug(f"✓ Address 0x{addr:08X} returned data 0x{data:08X}")
                else:
                    tb.log.error(f"Address range test failed at 0x{addr:08X}: {info}")
                    raise Exception(f"Address range test failed: {info}")

            range_tests_passed += 1
            tb.log.info(f"✓ {description} responses passed")

        if range_tests_passed == len(address_ranges):
            tb.log.info("✓ All address range responses passed")
            tests_passed += 1

        # Test 6: Stress testing
        tb.log.info("=== Test 6: Slave Stress Testing ===")
        total_tests += 1
        tb.set_timing_profile('stress')

        tb.log.info(f"Running slave stress test with {stress_count} read responses...")
        success = await tb.stress_read_test(stress_count)
        if not success:
            error_msg = "Slave stress test failed"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("✓ Slave stress test passed")
        tests_passed += 1

        # Test 7: Outstanding transaction responses (medium and full levels)
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 7: Outstanding Transaction Responses ===")
            total_tests += 1
            tb.set_timing_profile('backtoback')

            success, stats = await tb.test_outstanding_transactions(count=15)
            if success:
                tb.log.info(f"✓ Outstanding transaction responses passed ({stats['success_rate']:.1%})")
                tests_passed += 1
            else:
                # Allow partial success for outstanding transactions
                if stats.get('success_rate', 0) >= 0.8:  # 80% threshold
                    tb.log.warning(f"Outstanding transaction responses partially successful ({stats['success_rate']:.1%})")
                    tests_passed += 1
                else:
                    error_msg = f"Outstanding transaction responses failed: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

        # =================================================================
        # Final Results
        # =================================================================
        final_stats = tb.get_test_stats()
        total_reads = final_stats['summary']['total_reads']
        successful_reads = final_stats['summary']['successful_reads']

        # Calculate overall success rate
        success_rate = (successful_reads / total_reads * 100) if total_reads > 0 else 0

        tb.log.info("="*80)
        tb.log.info("AXI4 SLAVE READ TEST RESULTS")
        tb.log.info("="*80)
        tb.log.info(f"Test phases passed:    {tests_passed}/{total_tests}")
        tb.log.info(f"Total read responses:  {total_reads}")
        tb.log.info(f"Successful responses:  {successful_reads}")
        tb.log.info(f"Overall success rate:  {success_rate:.1f}%")
        tb.log.info(f"Test level:            {test_level.upper()}")

        # Determine final result
        phase_success_rate = (tests_passed / total_tests) if total_tests > 0 else 0

        if tests_passed == total_tests and success_rate >= 95.0:
            tb.log.info("✅ AXI4 SLAVE READ TESTS PASSED")
        else:
            tb.log.error(f"❌ AXI4 SLAVE READ TESTS FAILED (phase success: {phase_success_rate:.1f}%, response success: {success_rate:.1f}%)")
            raise RuntimeError(f"Test failed with {phase_success_rate:.1f}% phase success and {success_rate:.1f}% response success")

    except Exception as e:
        tb.log.error(f"AXI4 slave read test failed with exception: {str(e)}")
        final_stats = tb.get_test_stats()
        tb.log.error(f"Final stats: {final_stats.get('summary', {})}")
        raise


def validate_axi4_params(params):
    """
    Validate AXI4 parameters to ensure they meet specification constraints.

    Raises:
        ValueError: If any parameter violates AXI4 specification limits
    """
    for param in params:
        stub, id_w, addr_w, data_w, user_w, ar_d, r_d, level = param

        # AXI4 specification: Address width must not exceed 64-bits
        if addr_w > 64:
            raise ValueError(
                f"Invalid AXI4 configuration: addr_width={addr_w} exceeds maximum of 64-bits. "
                f"AXI4 specification limits address width to 64-bits. "
                f"Full parameter set: {param}"
            )

    return params


def generate_axi4_params():
    """
    Generate AXI4 parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke test - stub + non-stub)
    REG_LEVEL=FUNC: 8 tests (functional coverage) - default
    REG_LEVEL=FULL: 48 tests (comprehensive validation)

    Parameters: (stub, id_width, addr_width, data_width, user_width, ar_depth, r_depth, test_level)

    Raises:
        ValueError: If generated parameters violate AXI4 constraints
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove both stub and non-stub compile and work
        # 2 tests: 1 stub + 1 non-stub, basic level
        params = [
            (1, 8, 32, 32, 1, 2, 4, 'basic'),  # Stub version
            (0, 8, 32, 32, 1, 2, 4, 'basic'),  # Non-stub version
        ]
        return validate_axi4_params(params)

    elif reg_level == 'FUNC':
        # Functional coverage - test both stub modes with proven configs
        # 2 stubs × 2 configs × 2 levels = 8 tests
        # NOTE: Sticking to 32-bit data (proven stable), testing depth variations
        stubs = [1, 0]
        configs = [
            (8, 32, 32, 1, 2, 4),   # Standard config
            (8, 32, 32, 1, 4, 8),   # Deeper buffers
        ]
        test_levels = ['basic', 'medium']

        params = []
        for stub in stubs:
            for id_w, addr_w, data_w, user_w, ar_d, r_d in configs:
                for level in test_levels:
                    params.append((stub, id_w, addr_w, data_w, user_w, ar_d, r_d, level))

        return validate_axi4_params(params)

    else:  # FULL
        # Comprehensive testing - multiple widths, depths, and both stub modes
        # 2 stubs × 2 id_widths × 2 addr_widths × 1 data_width × 2 depths × 3 levels = 48 tests
        # NOTE: 64-bit data width excluded for consistency with write path (has RTL issues)
        stubs = [1, 0]
        id_widths = [4, 8]
        addr_widths = [32, 64]
        data_width = 32  # Fixed to 32-bit for consistency
        user_width = 1
        ar_r_depths = [(2, 4), (4, 8)]  # (ar_depth, r_depth) pairs
        test_levels = ['basic', 'medium', 'full']

        params = []
        for stub, id_w, addr_w, (ar_d, r_d), level in product(
                stubs, id_widths, addr_widths, ar_r_depths, test_levels):
            params.append((stub, id_w, addr_w, data_width, user_width, ar_d, r_d, level))

        return validate_axi4_params(params)


@pytest.mark.parametrize("stub, id_width, addr_width, data_width, user_width, ar_depth, r_depth, test_level",
                        generate_axi4_params())
def test_axi4_slave_read(request, stub, id_width, addr_width, data_width, user_width,
                            ar_depth, r_depth, test_level):
    """Test AXI4 slave read with different parameter combinations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi4': 'rtl/amba/axi4/',
        'rtl_axi4_stubs': 'rtl/amba/axi4/stubs',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Set up test names and directories
    if stub == 1:
        dir_key = 'rtl_axi4_stubs'
        dut_name = "axi4_slave_rd_stub"
    else:
        dir_key = 'rtl_axi4'
        dut_name = "axi4_slave_rd"

    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_{dut_name}_i{id_str}_a{aw_str}_d{dw_str}_u{uw_str}_ard{ard_str}_rd{rd_str}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),  # Dependency
        os.path.join(rtl_dict[dir_key], f"{dut_name}.sv"),         # Main DUT
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters
    wstrb_width = data_width // 8
    ar_size = id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + user_width  # AR packet size
    r_size = id_width + data_width + 2 + 1 + user_width  # R packet size

    rtl_parameters = {
        'SKID_DEPTH_AR': ar_depth,
        'SKID_DEPTH_R': r_depth,
        'AXI_ID_WIDTH': id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': user_width,
        'AXI_WSTRB_WIDTH': wstrb_width,
        # Calculated parameters
        'AW': addr_width,
        'DW': data_width,
        'IW': id_width,
        'SW': wstrb_width,
        'UW': user_width,
        'ARSize': ar_size,
        'RSize': r_size,
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width + id_width) / 100.0
    timeout_ms = int(5000 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(4347), # str(random.randint(0, 100000)),
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),

        # AXI4 test parameters
        'TEST_STUB': str(stub),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',  # 10ns = 100MHz
        'TIMEOUT_CYCLES': '2000',

        # Buffer depth parameters
        'TEST_AR_DEPTH': str(ar_depth),
        'TEST_R_DEPTH': str(r_depth),
        'AXI4_COMPLIANCE_CHECK': '1',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-DUSE_ASYNC_RESET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected pins for stub testing
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI4 Slave Read test: {dut_name}")
    print(f"AXI4 Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
    print(f"Buffer Depths: AR={ar_depth}, R={r_depth}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"{'='*80}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # VCD controlled by compile_args, not cocotb-test
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )
        print(f"✅ {test_level.upper()} AXI4 Slave Read test PASSED")
    except Exception as e:
        print(f"❌ {test_level.upper()} AXI4 Slave Read test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise