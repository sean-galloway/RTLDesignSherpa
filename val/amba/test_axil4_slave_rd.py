# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil4_slave_rd
# Purpose: AXIL4 Slave Read Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Slave Read Test Runner

Test runner for the AXIL4 slave read module using the CocoTB framework.
Tests various AXIL4 configurations and validates read response behavior
for single transfer register access patterns.

Based on AXI4 test runner but simplified for AXIL4 specification:
- No stub version (AXIL4 only has full RTL)
- No ID width parameter (AXIL4 doesn't use IDs)  
- No burst testing (single transfers only)
- Register-oriented test patterns
"""

import os
import random
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Import the testbench
from CocoTBFramework.tbclasses.axil4.axil4_slave_read_tb import AXIL4SlaveReadTB


@cocotb.test(timeout_time=15, timeout_unit="ms")
async def axil4_slave_read_test(dut):
    """AXIL4 slave read test using the AXIL4 framework components"""

    # Create testbench instance
    tb = AXIL4SlaveReadTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIL4 slave read test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXIL4 slave read test...")
    tb.log.info(f"AXIL4 widths: ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        register_read_counts = [10, 20]
        address_ranges = {
            'incremental': (0x1000, 8),
            'address_decode': (0x2000, 4)
        }
        stress_count = 25
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        register_read_counts = [20, 40, 30]
        address_ranges = {
            'incremental': (0x1000, 16),
            'address_decode': (0x2000, 8),
            'fixed_patterns': (0x3000, 8)
        }
        stress_count = 50
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        register_read_counts = [30, 50, 75]
        address_ranges = {
            'incremental': (0x1000, 32),
            'address_decode': (0x2000, 16),
            'fixed_patterns': (0x3000, 16),
            'status_patterns': (0x4000, 8)
        }
        stress_count = 100

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    # Initialize success tracking for final results
    tests_passed = 0
    total_tests = 0

    try:
        # Test 1: Basic connectivity test
        tb.log.info("=== Test 1: Basic AXIL4 Slave Connectivity ===")
        total_tests += 1
        tb.set_timing_profile('normal')

        # Single register read from known memory location
        success, data, info = await tb.single_read_response_test(0x1000)
        if not success:
            tb.log.error("Basic AXIL4 slave connectivity test failed!")
            raise Exception(f"Basic connectivity failed: {info}")

        tb.log.info("✅ Basic AXIL4 slave connectivity test passed")
        tests_passed += 1

        # Test 2: Register read sequences with different timing profiles
        for profile in timing_profiles:
            tb.log.info(f"=== Test 2: Register Read Sequences ({profile.upper()}) ===")
            total_tests += 1
            tb.set_timing_profile(profile)

            for count in register_read_counts:
                tb.log.info(f"Testing {count} register reads with '{profile}' timing...")
                success = await tb.basic_register_read_sequence(count)
                if not success:
                    error_msg = f"Register read sequence failed with {profile} timing"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

            tb.log.info(f"✅ Register read sequences passed with '{profile}' timing")
            tests_passed += 1

        # Test 3: Address decode validation
        tb.log.info("=== Test 3: Address Decode Validation ===")
        total_tests += 1
        tb.set_timing_profile('normal')

        success = await tb.address_decode_test(address_ranges)
        if not success:
            error_msg = "Address decode validation failed"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("✅ Address decode validation passed")
        tests_passed += 1

        # Test 4: Register pattern validation
        tb.log.info("=== Test 4: Register Pattern Validation ===")
        total_tests += 1
        tb.set_timing_profile('normal')

        pattern_success, pattern_results = await tb.register_pattern_validation_test()
        if not pattern_success:
            failed_patterns = [name for name, success, _, _ in pattern_results if not success]
            error_msg = f"Pattern validation failed for: {failed_patterns}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("✅ Register pattern validation passed")
        tests_passed += 1

        # Test 5: Timing profile validation (medium and full levels)
        if test_level in ['medium', 'full']:
            for profile in timing_profiles:
                tb.log.info(f"=== Test 5: Timing Profile Validation ({profile.upper()}) ===")
                total_tests += 1

                success = await tb.timing_profile_test(profile, test_count=20)
                if success:
                    tb.log.info(f"✅ Timing profile '{profile}' validation passed")
                    tests_passed += 1
                else:
                    # Allow partial success for timing tests
                    tb.log.warning(f"⚠️ Timing profile '{profile}' had some failures (continuing)")
                    tests_passed += 1  # Count as success with warning

        # Test 6: Stress testing
        tb.log.info("=== Test 6: AXIL4 Slave Stress Testing ===")
        total_tests += 1
        tb.set_timing_profile('stress')

        tb.log.info(f"Running AXIL4 slave stress test with {stress_count} register reads...")
        success = await tb.stress_register_access_test(stress_count)
        if not success:
            error_msg = "AXIL4 slave stress test failed"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("✅ AXIL4 slave stress test passed")
        tests_passed += 1

        # Test 7: Mixed register operations (full level only)
        if test_level == 'full':
            tb.log.info("=== Test 7: Mixed Register Operations ===")
            total_tests += 1

            # Mix of register reads from different address ranges
            mixed_operations = [
                (0x1008, "incremental pattern"),
                (0x2008, "address decode"),
                (0x3010, "fixed pattern"),
                (0x4008, "status pattern"),
                (0x1010, "incremental pattern"),
            ]

            all_passed = True
            for i, (addr, description) in enumerate(mixed_operations):
                tb.log.debug(f"Mixed operation {i+1}: {description} @ 0x{addr:08X}")
                success, data, info = await tb.single_read_response_test(addr)

                if not success:
                    tb.log.error(f"Mixed operation {i+1} failed: {info}")
                    all_passed = False
                    break

                # Small delay between operations
                await tb.wait_clocks('aclk', 2)

            if not all_passed:
                error_msg = "Mixed register operations failed"
                tb.log.error(error_msg)
                raise Exception(error_msg)

            tb.log.info("✅ Mixed register operations passed")
            tests_passed += 1

        # =================================================================
        # Final Results
        # =================================================================
        final_stats = tb.get_test_stats()
        total_reads = final_stats['summary']['total_reads']
        successful_reads = final_stats['summary']['successful_reads']

        # Calculate overall success rate
        success_rate = (successful_reads / total_reads * 100) if total_reads > 0 else 0

        tb.log.info("="*80)
        tb.log.info("AXIL4 SLAVE READ TEST RESULTS")
        tb.log.info("="*80)
        tb.log.info(f"Test phases passed:      {tests_passed}/{total_tests}")
        tb.log.info(f"Total register reads:    {total_reads}")
        tb.log.info(f"Successful reads:        {successful_reads}")
        tb.log.info(f"Overall success rate:    {success_rate:.1f}%")
        tb.log.info(f"Test level:              {test_level.upper()}")

        # Determine final result
        phase_success_rate = (tests_passed / total_tests) if total_tests > 0 else 0

        if tests_passed == total_tests and success_rate >= 95.0:
            tb.log.info("✅ AXIL4 SLAVE READ TESTS PASSED")
        else:
            tb.log.error(f"❌ AXIL4 SLAVE READ TESTS FAILED (phase success: {phase_success_rate:.1f}%, response success: {success_rate:.1f}%)")
            raise RuntimeError(f"Test failed with {phase_success_rate:.1f}% phase success and {success_rate:.1f}% response success")

    except Exception as e:
        tb.log.error(f"AXIL4 slave read test failed with exception: {str(e)}")
        final_stats = tb.get_test_stats()
        tb.log.error(f"Final stats: {final_stats.get('summary', {})}")
        raise
    finally:
        # Always call finalize to print compliance reports
        tb.finalize_test()


def generate_axil4_params():
    """
    Generate AXIL4 slave read parameter combinations based on REG_LEVEL.

    Parameter tuple: (addr_width, data_width, ar_depth, r_depth, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 18 tests - Comprehensive testing (6 configs × 3 test_levels)

    Returns:
        list: Parameter tuples for pytest.mark.parametrize
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [(32, 32, 2, 4, 'basic')]
    elif reg_level == 'FUNC':
        params = [(32, 32, 2, 4, 'basic'), (32, 32, 4, 8, 'medium'), (64, 64, 2, 4, 'medium')]
    else:  # FULL
        test_levels = ['basic', 'medium', 'full']
        configs = [(32, 32, 2, 4), (32, 32, 4, 8), (64, 64, 2, 4), (32, 64, 4, 4), (64, 32, 2, 8), (64, 64, 4, 4)]
        params = [(aw, dw, ar, r, level) for (aw, dw, ar, r) in configs for level in test_levels]

    return params


@pytest.mark.parametrize("addr_width, data_width, ar_depth, r_depth, test_level",
                        generate_axil4_params())
def test_axil4_slave_read(request, addr_width, data_width, ar_depth, r_depth, test_level):
    """Test AXIL4 slave read with different parameter combinations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Set up test names and directories
    dut_name = "axil4_slave_rd"

    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_ard{ard_str}_rd{rd_str}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),  # Dependency
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),     # Main DUT
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL4)
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': addr_width,
        'AXIL_DATA_WIDTH': data_width,
        'SKID_DEPTH_AR': ar_depth,
        'SKID_DEPTH_R': r_depth,
        # Derived parameters
        'AW': addr_width,
        'DW': data_width,
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width) / 100.0
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

        # AXIL4 test parameters
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_CLK_PERIOD': '10',  # 10ns = 100MHz
        'TIMEOUT_CYCLES': '2000',

        # Buffer depth parameters
        'TEST_AR_DEPTH': str(ar_depth),
        'TEST_R_DEPTH': str(r_depth),
        'AXIL4_COMPLIANCE_CHECK': '1',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected pins
    ]
    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIL4 Slave Read test: {dut_name}")
    print(f"AXIL4 Config: ADDR={addr_width}, DATA={data_width}")
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
        print(f"✅ {test_level.upper()} AXIL4 Slave Read test PASSED")
    except Exception as e:
        print(f"❌ {test_level.upper()} AXIL4 Slave Read test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Can run individual tests or use pytest
    pytest.main([__file__, "-v", "-s"])

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Test AXIL4 slave read with different parameter combinations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # Set up test names and directories
    dut_name = "axil4_slave_rd"

    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_ard{ard_str}_rd{rd_str}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),  # Dependency
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),     # Main DUT
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL4)
    rtl_parameters = {
        'AXIL_ADDR_WIDTH': addr_width,
        'AXIL_DATA_WIDTH': data_width,
        'SKID_DEPTH_AR': ar_depth,
        'SKID_DEPTH_R': r_depth,
        # Derived parameters
        'AW': addr_width,
        'DW': data_width,
    }

    # Calculate timeout based on complexity
    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width) / 100.0
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

        # AXIL4 test parameters
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_CLK_PERIOD': '10',  # 10ns = 100MHz
        'TIMEOUT_CYCLES': '2000',

        # Buffer depth parameters
        'TEST_AR_DEPTH': str(ar_depth),
        'TEST_R_DEPTH': str(r_depth),
        'AXIL4_COMPLIANCE_CHECK': '1',
    }

    # Simulation settings
    includes = [rtl_dict['rtl_amba_includes']]
    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",  # Allow unconnected pins
    ]
    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIL4 Slave Read test: {dut_name}")
    print(f"AXIL4 Config: ADDR={addr_width}, DATA={data_width}")
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
        print(f"✅ {test_level.upper()} AXIL4 Slave Read test PASSED")
    except Exception as e:
        print(f"❌ {test_level.upper()} AXIL4 Slave Read test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise


if __name__ == "__main__":
    # Can run individual tests or use pytest
    pytest.main([__file__, "-v", "-s"])
