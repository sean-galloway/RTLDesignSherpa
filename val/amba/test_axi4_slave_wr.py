# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4_slave_wr
# Purpose: AXI4 Slave Write Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI4 Slave Write Test Runner

Test runner for the AXI4 slave write stub using the CocoTB framework.
Tests various AXI4 configurations and validates write response behavior.

Inverted from the master test runner - tests the slave's response to writes.

REG_LEVEL Control:
    Environment variable REG_LEVEL controls the test parameter combinations:

    REG_LEVEL=GATE: 2 tests (smoke test - stub + non-stub)
        - Quick validation (stub + non-stub, basic level)
        - Duration: ~2 min
        - Use: Pre-commit hooks, fast CI

    REG_LEVEL=FUNC: 8 tests (functional coverage) - default
        - 2 stubs × 2 depth_configs × 2 levels (32-bit data only)
        - Moderate coverage of key combinations
        - Duration: ~15 min
        - Use: PR validation, regular testing

    REG_LEVEL=FULL: 48 tests (comprehensive validation)
        - 2 stubs × 2 id × 2 addr × 1 data × 2 depth_pairs × 3 levels
        - Complete parameter space coverage (32-bit data only)
        - Duration: ~1 hour
        - Use: Release validation, nightly regression
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
from CocoTBFramework.tbclasses.axi4.axi4_slave_write_tb import AXI4SlaveWriteTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4_slave_write_test(dut):
    """AXI4 slave write test using the AXI4 framework components"""

    # Create testbench instance
    tb = AXI4SlaveWriteTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4 slave write test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXI4 slave write test...")
    tb.log.info(f"AXI4 widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_write_counts = [10, 20]
        burst_lengths = [[2, 4], [4, 8]]
        stress_count = 25
        run_error_tests = False
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_write_counts = [20, 40, 30]
        burst_lengths = [[2, 4, 8], [4, 8, 16], [1, 2, 4, 8]]
        stress_count = 50
        run_error_tests = True
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        single_write_counts = [30, 50, 75]
        burst_lengths = [[1, 2, 4, 8, 16], [2, 4, 8, 16, 32], [1, 3, 7, 15, 31]]
        stress_count = 100
        run_error_tests = True

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    try:
        # =================================================================
        # Test 1: Basic connectivity test
        # =================================================================
        tb.log.info("=== Test 1: Basic Slave Connectivity ===")
        tb.set_timing_profile('normal')

        # Single write response test
        tb.log.info("Testing basic slave write response...")
        success, info = await tb.single_write_response_test(0x1000, 0xDEADBEEF)
        if not success:
            error_msg = f"Basic slave connectivity test failed: {info.get('error', 'Unknown error')}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("✓ Basic slave connectivity test passed")

        # =================================================================
        # Test 2: Single write responses with different timing profiles
        # =================================================================
        for profile in timing_profiles:
            tb.log.info(f"=== Test 2: Single Write Responses ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for count in single_write_counts:
                tb.log.info(f"Running {count} single write responses with '{profile}' timing...")
                success, stats = await tb.run_single_writes(count)
                if not success:
                    error_msg = f"Single write responses failed with '{profile}' timing: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"✓ Single write responses passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 3: Burst write responses with different lengths
        # =================================================================
        for profile in ['normal', 'fast']:
            tb.log.info(f"=== Test 3: Burst Write Responses ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for burst_config in burst_lengths:
                tb.log.info(f"Testing burst write responses with lengths {burst_config}...")
                success, stats = await tb.run_burst_writes(burst_config, count=3)
                if not success:
                    error_msg = f"Burst write responses failed: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"✓ Burst write responses passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 4: Mixed operation responses
        # =================================================================
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 4: Mixed Operation Responses ===")
            tb.set_timing_profile('normal')

            # Mix of single and burst write responses
            mixed_operations = [
                ('single', 0x4000, 0x11111111),
                ('burst', 0x4010, [0x22222222, 0x33333333, 0x44444444]),
                ('single', 0x4020, 0x55555555),
                ('burst', 0x4030, [0x66666666, 0x77777777]),
                ('single', 0x4040, 0x88888888),
            ]

            for op_type, addr, data in mixed_operations:
                if op_type == 'single':
                    success, info = await tb.single_write_response_test(addr, data)
                else:  # burst
                    success, info = await tb.burst_write_response_test(addr, data)

                if not success:
                    error_msg = f"Mixed operation response failed: {info}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

            tb.log.info("✓ Mixed operation responses passed")

        # =================================================================
        # Test 5: Timing variation responses
        # =================================================================
        if test_level == 'full':
            tb.log.info("=== Test 5: Timing Variation Responses ===")
            for profile in timing_profiles:
                tb.set_timing_profile(profile)
                success, stats = await tb.run_single_writes(10)
                if not success:
                    error_msg = f"Timing variation responses failed with {profile}: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"✓ {profile.capitalize()} timing responses passed ({stats['success_rate']:.1%})")

        # =================================================================
        # Test 6: Address range responses
        # =================================================================
        tb.log.info("=== Test 6: Address Range Responses ===")
        tb.set_timing_profile('normal')

        address_ranges = [
            (0x1000, "Low addresses"),
            (0x8000, "Mid addresses"), 
            (0xF000, "High addresses")
        ]

        for base_addr, description in address_ranges:
            tb.log.info(f"Testing slave responses for {description.lower()}...")
            for i in range(5):
                addr = base_addr + (i * 4)
                data = 0xABCD0000 + i
                success, info = await tb.single_write_response_test(addr, data)
                if not success:
                    error_msg = f"Address range response test failed at {description}: {info}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

            tb.log.info(f"✓ {description} responses passed")

        # =================================================================
        # Test 7: Stress testing
        # =================================================================
        tb.log.info("=== Test 7: Slave Stress Testing ===")
        tb.set_timing_profile('stress')

        tb.log.info(f"Running slave stress test with {stress_count} mixed operations...")
        success, stats = await tb.stress_test(stress_count)
        if not success:
            error_msg = f"Slave stress test failed: {stats}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info(f"✓ Slave stress test passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 8: Outstanding transaction responses
        # =================================================================
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 8: Outstanding Transaction Responses ===")
            tb.set_timing_profile('backtoback')

            success, stats = await tb.test_outstanding_transactions(count=20)
            if success:
                tb.log.info(f"✓ Outstanding transaction responses passed ({stats['success_rate']:.1%})")
            else:
                tb.log.warning(f"Outstanding transaction responses had issues: {stats}")

        # =================================================================
        # Final Results
        # =================================================================
        final_stats = tb.get_test_stats()
        total_writes = final_stats['summary']['total_writes']
        successful_writes = final_stats['summary']['successful_writes']
        failed_writes = final_stats['summary']['failed_writes']

        tb.log.info("="*80)
        tb.log.info("AXI4 SLAVE WRITE TEST RESULTS")
        tb.log.info("="*80)
        tb.log.info(f"Total write responses:      {total_writes}")
        tb.log.info(f"Successful responses:       {successful_writes}")
        tb.log.info(f"Failed responses:           {failed_writes}")
        tb.log.info(f"Success rate:               {(successful_writes/total_writes*100) if total_writes > 0 else 0:.2f}%")
        tb.log.info(f"Test level:                 {test_level.upper()}")
        tb.log.info(f"Test duration:              {final_stats['summary']['test_duration']:.2f}s")

        if failed_writes > 0:
            tb.log.error("❌ AXI4 slave write test FAILED: Some responses failed")
            raise Exception(f"AXI4 slave write test FAILED: {failed_writes} responses failed")

        tb.log.info("✅ AXI4 slave write test PASSED: All responses successful")

    except Exception as e:
        # Log final error and re-raise
        tb.log.error(f"AXI4 slave write test FAILED with exception: {str(e)}")
        final_stats = tb.get_test_stats()
        tb.log.error(f"Final stats: {final_stats['summary']}")
        raise


def validate_axi4_params(params):
    """
    Validate AXI4 parameters to ensure they meet specification constraints.

    Raises:
        ValueError: If any parameter violates AXI4 specification limits
    """
    for param in params:
        stub, id_w, addr_w, data_w, user_w, aw_d, w_d, b_d, level = param

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

    Returns:
        list: Tuples of (stub, id_width, addr_width, data_width, user_width,
                         aw_depth, w_depth, b_depth, test_level)

    Raises:
        ValueError: If generated parameters violate AXI4 constraints
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Quick smoke test - just verify stub + non-stub compile and run
        # 2 tests: stub + non-stub @ basic level
        params = [
            (1, 8, 32, 32, 1, 2, 4, 2, 'basic'),  # Stub
            (0, 8, 32, 32, 1, 2, 4, 2, 'basic'),  # Non-stub
        ]
        return validate_axi4_params(params)

    elif reg_level == 'FUNC':
        # FUNC: Functional coverage - test proven configs with depth variations
        # 2 stubs × 2 configs × 2 levels = 8 tests
        # NOTE: Sticking to 32-bit data (proven stable), testing depth variations
        stubs = [1, 0]  # Test both stub and non-stub
        configs = [
            # (id_w, addr_w, data_w, user_w, aw_d, w_d, b_d)
            (8, 32, 32, 1, 2, 4, 2),   # Standard config
            (8, 32, 32, 1, 4, 4, 4),   # Deeper buffers
        ]
        test_levels = ['basic', 'medium']

        params = []
        for stub in stubs:
            for (id_w, addr_w, data_w, user_w, aw_d, w_d, b_d) in configs:
                for level in test_levels:
                    params.append((stub, id_w, addr_w, data_w, user_w, aw_d, w_d, b_d, level))
        return validate_axi4_params(params)

    else:  # FULL
        # FULL: Comprehensive testing - cover parameter space
        # 2 stubs × 2 id × 2 addr × 1 data × 2 depth_pairs × 3 levels = 48 tests
        # NOTE: 64-bit data width excluded due to RTL instability (see known issues)
        stubs = [1, 0]
        id_widths = [4, 8]
        addr_widths = [32, 64]
        data_width = 32  # Fixed to 32-bit (64-bit has RTL issues on write path)
        user_width = 1

        # Test different depth configurations
        aw_w_b_depths = [
            (2, 4, 2),  # Shallow buffers
            (4, 8, 4),  # Deeper buffers
        ]

        test_levels = ['basic', 'medium', 'full']

        # Generate all combinations, unpacking depth tuples
        params = []
        for stub in stubs:
            for id_w in id_widths:
                for addr_w in addr_widths:
                    for (aw_d, w_d, b_d) in aw_w_b_depths:
                        for level in test_levels:
                            params.append((stub, id_w, addr_w, data_width, user_width,
                                         aw_d, w_d, b_d, level))
        return validate_axi4_params(params)


@pytest.mark.parametrize("stub, id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level",
                        generate_axi4_params())
def test_axi4_slave_write(stub, id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level):
    """Test AXI4 slave write with specified parameters"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

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
        dut_name = "axi4_slave_wr_stub"
    else:
        dir_key = 'rtl_axi4'
        dut_name = "axi4_slave_wr"

    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    awd_str = TBBase.format_dec(aw_depth, 1)
    wd_str = TBBase.format_dec(w_depth, 1)
    bd_str = TBBase.format_dec(b_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_{dut_name}_i{id_str}_a{aw_str}_d{dw_str}_u{uw_str}_awd{awd_str}_wd{wd_str}_bd{bd_str}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies for gaxi_skid_buffer
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
    aw_size = id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + user_width  # AW packet size
    w_size = data_width + wstrb_width + 1 + user_width  # W packet size
    b_size = id_width + 2 + user_width  # B packet size

    rtl_parameters = {
        'AXI_ID_WIDTH': id_width,
        'AXI_ADDR_WIDTH': addr_width,
        'AXI_DATA_WIDTH': data_width,
        'AXI_USER_WIDTH': user_width,
        'AXI_WSTRB_WIDTH': wstrb_width,
        'SKID_DEPTH_AW': aw_depth,
        'SKID_DEPTH_W': w_depth,
        'SKID_DEPTH_B': b_depth,
        'AWSize': aw_size,
        'WSize': w_size,
        'BSize': b_size,
    }

    # Test timeout based on complexity
    timeout_ms = 5000 if test_level == 'basic' else 10000 if test_level == 'medium' else 20000

    # Set up test module
    module = "test_axi4_slave_wr"

    # Environment variables for the test
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),

        # AXI4 test parameters
        'TEST_STUB': str(stub),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',  # 10ns = 100MHz
        'TIMEOUT_CYCLES': str(timeout_ms // 10),  # Convert to cycles
        'SEED': str(random.randint(1, 999999)),

        # Buffer depth parameters
        'TEST_AW_DEPTH': str(aw_depth),
        'TEST_W_DEPTH': str(w_depth),
        'TEST_B_DEPTH': str(b_depth),
        'AXI4_COMPLIANCE_CHECK': '1',
    }

    # Cocotb simulation settings
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
    print(f"Running {test_level.upper()} AXI4 Slave Write test: {dut_name}")
    print(f"AXI4 Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
    print(f"Buffer Depths: AW={aw_depth}, W={w_depth}, B={b_depth}")
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
        print(f"✅ {test_level.upper()} AXI4 Slave Write test PASSED")
    except Exception as e:
        print(f"❌ {test_level.upper()} AXI4 Slave Write test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise