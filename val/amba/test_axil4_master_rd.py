# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil4_master_rd
# Purpose: AXIL4 Read Master Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Read Master Test Runner

Test runner for the AXIL4 read master using the CocoTB framework.
Tests various AXIL4 configurations and validates read transactions.

Based on the AXI4 master read test runner pattern but simplified for AXIL4 register access.
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
from CocoTBFramework.tbclasses.axil4.axil4_master_read_tb import AXIL4MasterReadTB


@cocotb.test(timeout_time=10, timeout_unit="ms")
async def axil4_read_master_test(dut):
    """AXIL4 read master test using the AXIL4 framework components"""

    # Create testbench instance
    tb = AXIL4MasterReadTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIL4 read master test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXIL4 read master test...")
    tb.log.info(f"AXIL4 widths: ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_read_counts = [10, 20]
        stress_count = 25
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_read_counts = [20, 40, 30]
        stress_count = 50
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        single_read_counts = [30, 50, 75]
        stress_count = 100

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    # Test 1: Basic connectivity test
    tb.log.info("=== Scenario AXIL-MR-01: Single read ===")
    tb.log.info("=== Test 1: Basic Connectivity ===")
    tb.set_timing_profile('normal')

    # Single register read from known memory location
    success, data, info = await tb.register_read_test(0x1000)
    if not success:
        tb.log.error("Basic connectivity test failed!")
        raise RuntimeError("Basic connectivity failed")

    tb.log.info(f"Basic connectivity test passed: data=0x{data:08X}")

    # Test 2: Register read sequences with different timing profiles
    tb.log.info("=== Scenario AXIL-MR-02: Back-to-back reads ===")
    tb.log.info("=== Test 2: Register Read Sequences ===")

    for i, (profile, count) in enumerate(zip(timing_profiles, single_read_counts)):
        tb.log.info(f"[{i+1}/{len(timing_profiles)}] Register reads with '{profile}' timing ({count} reads)")
        tb.set_timing_profile(profile)

        result = await tb.basic_read_sequence(count)
        if not result:
            tb.log.error(f"Register read sequence failed with '{profile}' timing")
            # Don't fail immediately - continue testing other profiles
        else:
            tb.log.info(f"Register read sequence passed with '{profile}' timing")

    # Test 3: Interface method compatibility test
    tb.log.info("=== Test 3: Interface Method Compatibility ===")

    for i, profile in enumerate(timing_profiles[:3]):  # Test first 3 profiles
        tb.log.info(f"[{i+1}/3] Interface methods with '{profile}' timing")
        tb.set_timing_profile(profile)

        result = await tb.register_access_sequence(15)
        if not result:
            tb.log.error(f"Interface method test failed with '{profile}' timing")
        else:
            tb.log.info(f"Interface method test passed with '{profile}' timing")

    # Test 4: Address pattern validation
    tb.log.info("=== Scenario AXIL-MR-11: Address sweep ===")
    tb.log.info("=== Test 4: Address Pattern Validation ===")

    # Test reads from different memory regions
    test_addresses = [
        (0x1000, "Incremental pattern"),
        (0x2000, "Address-based pattern"),
        (0x3000, "Fixed patterns")
    ]

    for addr, description in test_addresses:
        tb.log.info(f"Testing {description} at 0x{addr:08X}")
        success, data, info = await tb.register_read_test(addr)
        if success:
            tb.log.info(f"{description}: data=0x{data:08X}")
        else:
            tb.log.warning(f"{description} failed")

    # Test 5: Address alignment validation (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Test 5: Address Alignment Validation ===")
        
        alignment_result = await tb.address_alignment_test()
        if alignment_result:
            tb.log.info("Address alignment test passed")
        else:
            tb.log.warning("Address alignment test had issues")

    # Test 6: Stress testing (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Scenario AXIL-MR-06: Slow AR accept ===")
        tb.log.info("=== Scenario AXIL-MR-07: Slow R valid ===")
        tb.log.info("=== Scenario AXIL-MR-09: Backpressure ===")
        tb.log.info("=== Test 6: Stress Testing ===")

        result = await tb.stress_read_test(stress_count)
        if result:
            tb.log.info(f"Stress test passed ({stress_count} reads)")
        else:
            tb.log.warning(f"Stress test had issues ({stress_count} reads)")

    # Test 7: Protection field testing (full level)
    if test_level == 'full':
        tb.log.info("=== Scenario AXIL-MR-10: Various ARPROT ===")
        tb.log.info("=== Test 7: Protection Field Testing ===")

        # Test different PROT field values
        prot_values = [0x0, 0x1, 0x2, 0x3]  # Different protection types
        for prot in prot_values:
            success, data, info = await tb.register_read_test(0x1000, prot=prot)
            if success:
                tb.log.info(f"PROT={prot}: SUCCESS, data=0x{data:08X}")
            else:
                tb.log.warning(f"PROT={prot}: FAILED")

    # Test 8: Back-to-back read testing (full level)
    if test_level == 'full':
        tb.log.info("=== Test 8: Back-to-Back Read Testing ===")

        tb.set_timing_profile('backtoback')
        b2b_success = 0
        b2b_total = 20

        for i in range(b2b_total):
            addr = 0x3000 + (i * (tb.TEST_DATA_WIDTH // 8))
            success, _, _ = await tb.register_read_test(addr)
            if success:
                b2b_success += 1

        tb.log.info(f"Back-to-back reads result: {b2b_success}/{b2b_total} successful")

    # Final statistics and cleanup
    tb.log.info("=== Test Results Summary ===")
    stats = tb.get_test_stats()

    tb.log.info("Test Statistics:")
    tb.log.info(f"  Total reads: {stats['summary']['total_reads']}")
    tb.log.info(f"  Successful reads: {stats['summary']['successful_reads']}")
    tb.log.info(f"  Success rate: {stats['summary']['success_rate']}")
    tb.log.info(f"  Register reads: {stats['details']['register_reads']}")
    tb.log.info(f"  Data mismatches: {stats['details']['data_mismatches']}")
    tb.log.info(f"  Response errors: {stats['details']['response_errors']}")
    tb.log.info(f"  Timeout errors: {stats['details']['timeout_errors']}")

    # Determine overall test result
    success_rate = float(stats['summary']['success_rate'].rstrip('%'))
    if success_rate >= 95.0:
        tb.log.info(f"ALL {test_level.upper()} AXIL4 READ MASTER TESTS PASSED!")
    else:
        tb.log.error(f"AXIL4 READ MASTER TESTS FAILED (success rate: {success_rate:.1f}%)")
        raise RuntimeError(f"Test failed with {success_rate:.1f}% success rate")


def generate_axil4_params():
    """
    Generate AXIL4 parameter combinations based on REG_LEVEL.

    Parameter tuple: (addr_width, data_width, ar_depth, r_depth, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 18 tests - Comprehensive testing (2 addr × 3 depth combos × 3 test_levels)

    Returns:
        list: Parameter tuples for pytest.mark.parametrize
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [(32, 32, 4, 4, 'basic')]
    elif reg_level == 'FUNC':
        params = [(32, 32, 4, 4, 'basic'), (32, 32, 4, 8, 'medium'), (64, 64, 4, 4, 'medium')]
    else:  # FULL
        test_levels = ['basic', 'medium', 'full']
        configs = [(32, 32, 4, 4), (32, 32, 4, 8), (64, 64, 4, 4), (32, 64, 2, 4), (64, 32, 8, 4), (64, 64, 8, 8)]
        params = [(aw, dw, ar, r, level) for (aw, dw, ar, r) in configs for level in test_levels]

    return params


@pytest.mark.parametrize("addr_width, data_width, ar_depth, r_depth, test_level",
                        generate_axil4_params())
def test_axil4_read_master(request, addr_width, data_width, ar_depth, r_depth, test_level):
    """Test AXIL4 read master with different parameter combinations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # AXIL4 module details (no stub versions)
    dut_name = "axil4_master_rd"
    
    # Create descriptive test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_ard{ard_str}_rd{rd_str}_{test_level}_{reg_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies for gaxi_skid_buffer
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL4)
    ar_size = addr_width + 3  # ARADDR + ARPROT
    r_size = data_width + 2   # RDATA + RRESP

    rtl_parameters = {
        'SKID_DEPTH_AR': str(ar_depth),
        'SKID_DEPTH_R': str(r_depth),
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        # Calculated parameters
        'AW': str(addr_width),
        'DW': str(data_width),
        'ARSize': str(ar_size),
        'RSize': str(r_size),
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
        'SEED': str(random.randint(0, 100000)),
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIL4 Read Master test: {dut_name}")
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
        print(f"✓ {test_level.upper()} AXIL4 Read Master test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIL4 Read Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Test AXIL4 read master with different parameter combinations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # AXIL4 module details (no stub versions)
    dut_name = "axil4_master_rd"
    
    # Create descriptive test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    ard_str = TBBase.format_dec(ar_depth, 1)
    rd_str = TBBase.format_dec(r_depth, 1)

    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_ard{ard_str}_rd{rd_str}_{test_level}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # Verilog sources - include dependencies for gaxi_skid_buffer
    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_axil4'], f"{dut_name}.sv"),
    ]

    # Check that files exist
    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    # RTL parameters (simplified for AXIL4)
    ar_size = addr_width + 3  # ARADDR + ARPROT
    r_size = data_width + 2   # RDATA + RRESP

    rtl_parameters = {
        'SKID_DEPTH_AR': str(ar_depth),
        'SKID_DEPTH_R': str(r_depth),
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        # Calculated parameters
        'AW': str(addr_width),
        'DW': str(data_width),
        'ARSize': str(ar_size),
        'RSize': str(r_size),
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
        'SEED': str(random.randint(0, 100000)),
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

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    # Create command file for viewing results
    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXIL4 Read Master test: {dut_name}")
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
        print(f"✓ {test_level.upper()} AXIL4 Read Master test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIL4 Read Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
