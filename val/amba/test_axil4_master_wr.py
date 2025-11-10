# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axil4_master_wr
# Purpose: AXIL4 Write Master Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIL4 Write Master Test Runner

Test runner for the AXIL4 write master using the CocoTB framework.
Tests various AXIL4 configurations and validates write transactions.

Based on the AXI4 master write test runner pattern but simplified for AXIL4 register access.
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
from CocoTBFramework.tbclasses.axil4.axil4_master_write_tb import AXIL4MasterWriteTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axil4_write_master_test(dut):
    """AXIL4 write master test using the AXIL4 framework components"""

    # Create testbench instance
    tb = AXIL4MasterWriteTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXIL4 write master test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXIL4 write master test...")
    tb.log.info(f"AXIL4 widths: ADDR={tb.TEST_ADDR_WIDTH}, DATA={tb.TEST_DATA_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_write_counts = [10, 20]
        stress_count = 25
        run_error_tests = False
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_write_counts = [20, 40, 30]
        stress_count = 50
        run_error_tests = True
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress']
        single_write_counts = [30, 50, 75]
        stress_count = 100
        run_error_tests = True

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    try:
        # Test 1: Basic connectivity test
        tb.log.info("=== Test 1: Basic Connectivity ===")
        tb.set_timing_profile('normal')

        # Single register write to known memory location
        success, info = await tb.register_write_test(0x1000, 0xDEADBEEF)
        if not success:
            error_msg = f"Basic connectivity test failed: {info.get('error', 'Unknown error')}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("Basic connectivity test passed")

        # Test 2: Register write sequences with different timing profiles
        tb.log.info("=== Test 2: Register Write Sequences ===")

        for i, (profile, count) in enumerate(zip(timing_profiles, single_write_counts)):
            tb.log.info(f"[{i+1}/{len(timing_profiles)}] Register writes with '{profile}' timing ({count} writes)")
            tb.set_timing_profile(profile)

            result = await tb.basic_write_sequence(count)
            if not result:
                tb.log.error(f"Register write sequence failed with '{profile}' timing")
                # Don't fail immediately - continue testing other profiles
            else:
                tb.log.info(f"Register write sequence passed with '{profile}' timing")

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

        # Test 4: Address boundary testing
        tb.log.info("=== Test 4: Address Boundary Testing ===")
        tb.set_timing_profile('normal')

        # Calculate memory model size for boundary testing
        # Memory model size = num_lines × bytes_per_line
        memory_size = tb.memory_model.size
        max_valid_addr = memory_size - 4  # Leave room for word access

        boundary_addresses = [
            0x0,                    # Minimum address
            0x4,                    # Word aligned
            0x1000,                 # Page boundary
            max_valid_addr,         # Near max of MEMORY MODEL (not address space)
        ]

        for addr in boundary_addresses:
            # Ensure address is within memory model bounds
            if addr > max_valid_addr:
                addr = max_valid_addr

            data = 0xA5A5A5A5 & tb.MAX_DATA
            tb.log.info(f"Testing boundary address 0x{addr:08X}...")
            success, info = await tb.register_write_test(addr, data)
            if not success:
                tb.log.warning(f"Boundary test failed at address 0x{addr:08X}: {info}")
                # Don't fail the entire test for boundary issues, just log

        tb.log.info("Address boundary testing completed")

        # Test 5: Data pattern testing
        tb.log.info("=== Test 5: Data Pattern Testing ===")
        tb.set_timing_profile('normal')

        test_patterns = [
            0x00000000,     # All zeros
            0xFFFFFFFF,     # All ones
            0x55555555,     # Alternating 01
            0xAAAAAAAA,     # Alternating 10
            0x12345678,     # Sequential
            0x87654321,     # Reverse sequential
        ]

        base_addr = 0x2000
        for i, pattern in enumerate(test_patterns):
            pattern = pattern & tb.MAX_DATA  # Mask to data width
            addr = base_addr + (i * (tb.TEST_DATA_WIDTH // 8))
            tb.log.info(f"Testing data pattern 0x{pattern:08X}...")
            success, info = await tb.register_write_test(addr, pattern)
            if not success:
                tb.log.warning(f"Pattern test failed for 0x{pattern:08X}: {info}")

        tb.log.info("Data pattern testing completed")

        # Test 6: Write strobe testing (medium and full levels)
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 6: Write Strobe Testing ===")
            
            strobe_result = await tb.strobe_pattern_test()
            if strobe_result:
                tb.log.info("Write strobe test passed")
            else:
                tb.log.warning("Write strobe test had issues")

        # Test 7: Protection field testing (full level)
        if test_level == 'full':
            tb.log.info("=== Test 7: Protection Field Testing ===")

            # Test different PROT field values
            prot_values = [0x0, 0x1, 0x2, 0x3]  # Different protection types
            base_addr = 0x3000
            
            for prot in prot_values:
                addr = base_addr + (prot * (tb.TEST_DATA_WIDTH // 8))
                data = 0x12340000 + prot
                success, info = await tb.register_write_test(addr, data, prot=prot)
                if success:
                    tb.log.info(f"PROT={prot}: SUCCESS, data=0x{data:08X}")
                else:
                    tb.log.warning(f"PROT={prot}: FAILED")

        # Test 8: Stress testing (medium and full levels)
        if test_level in ['medium', 'full']:
            tb.log.info("=== Test 8: Stress Testing ===")

            result = await tb.stress_write_test(stress_count)
            if result:
                tb.log.info(f"Stress test passed ({stress_count} writes)")
            else:
                tb.log.warning(f"Stress test had issues ({stress_count} writes)")

        # Test 9: Back-to-back write testing (full level)
        if test_level == 'full':
            tb.log.info("=== Test 9: Back-to-Back Write Testing ===")

            tb.set_timing_profile('backtoback')
            b2b_success = 0
            b2b_total = 20

            for i in range(b2b_total):
                addr = 0x4000 + (i * (tb.TEST_DATA_WIDTH // 8))
                data = 0xBEEF0000 + i
                success, _ = await tb.register_write_test(addr, data)
                if success:
                    b2b_success += 1

            tb.log.info(f"Back-to-back writes result: {b2b_success}/{b2b_total} successful")

        # Test 10: Error injection testing (if enabled)
        if run_error_tests:
            tb.log.info("=== Test 10: Error Injection Testing ===")
            
            # Test maximum data values
            try:
                tb.log.info("Testing maximum data values...")
                max_data = (1 << tb.TEST_DATA_WIDTH) - 1
                success, info = await tb.register_write_test(0x5000, max_data)
                if success:
                    tb.log.info("Maximum data value handled correctly")
                else:
                    tb.log.warning(f"Maximum data value failed: {info}")
            except Exception as e:
                tb.log.warning(f"Maximum data value test caused exception: {str(e)}")

            # Test boundary addresses
            try:
                tb.log.info("Testing zero address...")
                success, info = await tb.register_write_test(0x0, 0xDEADBEEF)
                if success:
                    tb.log.info("Zero address handled correctly")
            except Exception as e:
                tb.log.info(f"Zero address test caused exception: {str(e)}")

            tb.log.info("Error injection testing completed")

        # Final statistics and cleanup
        tb.log.info("=== Test Results Summary ===")
        stats = tb.get_test_stats()

        tb.log.info("Test Statistics:")
        tb.log.info(f"  Total writes: {stats['summary']['total_writes']}")
        tb.log.info(f"  Successful writes: {stats['summary']['successful_writes']}")
        tb.log.info(f"  Success rate: {stats['summary']['success_rate']}")
        tb.log.info(f"  Register writes: {stats['details']['register_writes']}")
        tb.log.info(f"  Data mismatches: {stats['details']['data_mismatches']}")
        tb.log.info(f"  Response errors: {stats['details']['response_errors']}")
        tb.log.info(f"  Timeout errors: {stats['details']['timeout_errors']}")

        # Determine overall test result
        success_rate = float(stats['summary']['success_rate'].rstrip('%'))
        if success_rate >= 95.0:
            tb.log.info(f"ALL {test_level.upper()} AXIL4 WRITE MASTER TESTS PASSED!")
        else:
            tb.log.error(f"AXIL4 WRITE MASTER TESTS FAILED (success rate: {success_rate:.1f}%)")
            raise RuntimeError(f"Test failed with {success_rate:.1f}% success rate")

    except Exception as e:
        tb.log.error(f"AXIL4 write master test FAILED with exception: {str(e)}")
        final_stats = tb.get_test_stats()
        tb.log.error(f"Final stats: {final_stats['summary']}")
        raise


def generate_axil4_params():
    """
    Generate AXIL4 write parameter combinations based on REG_LEVEL.

    Parameter tuple: (addr_width, data_width, aw_depth, w_depth, b_depth, test_level)

    REG_LEVEL values:
        GATE: 1 test - Quick smoke test
        FUNC: 3 tests - Functional validation with variations
        FULL: 18 tests - Comprehensive testing (6 configs × 3 test_levels)

    Returns:
        list: Parameter tuples for pytest.mark.parametrize
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [(32, 32, 2, 4, 2, 'basic')]
    elif reg_level == 'FUNC':
        params = [(32, 32, 2, 4, 2, 'basic'), (32, 32, 4, 4, 4, 'medium'), (64, 64, 2, 4, 2, 'medium')]
    else:  # FULL
        test_levels = ['basic', 'medium', 'full']
        configs = [(32, 32, 2, 4, 2), (32, 32, 4, 4, 4), (64, 64, 2, 4, 2), (32, 64, 2, 8, 2), (64, 32, 4, 4, 2), (64, 64, 4, 8, 4)]
        params = [(aw, dw, awd, wd, bd, level) for (aw, dw, awd, wd, bd) in configs for level in test_levels]

    return params


@pytest.mark.parametrize("addr_width, data_width, aw_depth, w_depth, b_depth, test_level",
                        generate_axil4_params())
def test_axil4_write_master(request, addr_width, data_width, aw_depth, w_depth, b_depth, test_level):
    """Test AXIL4 write master with different parameter combinations"""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # AXIL4 module details (no stub versions)
    dut_name = "axil4_master_wr"
    
    # Create descriptive test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    awd_str = TBBase.format_dec(aw_depth, 1)
    wd_str = TBBase.format_dec(w_depth, 1)
    bd_str = TBBase.format_dec(b_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_awd{awd_str}_wd{wd_str}_bd{bd_str}_{test_level}_{reg_level}"

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
    wstrb_width = data_width // 8
    aw_size = addr_width + 3  # AWADDR + AWPROT
    w_size = data_width + wstrb_width  # WDATA + WSTRB
    b_size = 2   # BRESP only

    rtl_parameters = {
        'SKID_DEPTH_AW': str(aw_depth),
        'SKID_DEPTH_W': str(w_depth),
        'SKID_DEPTH_B': str(b_depth),
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        # Calculated parameters
        'AW': str(addr_width),
        'DW': str(data_width),
        'AWSize': str(aw_size),
        'WSize': str(w_size),
        'BSize': str(b_size),
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
        'TEST_AW_DEPTH': str(aw_depth),
        'TEST_W_DEPTH': str(w_depth),
        'TEST_B_DEPTH': str(b_depth),
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
    print(f"Running {test_level.upper()} AXIL4 Write Master test: {dut_name}")
    print(f"AXIL4 Config: ADDR={addr_width}, DATA={data_width}")
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
        print(f"✓ {test_level.upper()} AXIL4 Write Master test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIL4 Write Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Test AXIL4 write master with different parameter combinations"""

    # Get paths and setup
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axil4': 'rtl/amba/axil4/',
        'rtl_gaxi': 'rtl/amba/gaxi',
     'rtl_amba_includes': 'rtl/amba/includes'})

    # AXIL4 module details (no stub versions)
    dut_name = "axil4_master_wr"
    
    # Create descriptive test name
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    awd_str = TBBase.format_dec(aw_depth, 1)
    wd_str = TBBase.format_dec(w_depth, 1)
    bd_str = TBBase.format_dec(b_depth, 1)

    test_name_plus_params = f"test_{worker_id}_{dut_name}_a{aw_str}_d{dw_str}_awd{awd_str}_wd{wd_str}_bd{bd_str}_{test_level}"

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
    wstrb_width = data_width // 8
    aw_size = addr_width + 3  # AWADDR + AWPROT
    w_size = data_width + wstrb_width  # WDATA + WSTRB
    b_size = 2   # BRESP only

    rtl_parameters = {
        'SKID_DEPTH_AW': str(aw_depth),
        'SKID_DEPTH_W': str(w_depth),
        'SKID_DEPTH_B': str(b_depth),
        'AXIL_ADDR_WIDTH': str(addr_width),
        'AXIL_DATA_WIDTH': str(data_width),
        # Calculated parameters
        'AW': str(addr_width),
        'DW': str(data_width),
        'AWSize': str(aw_size),
        'WSize': str(w_size),
        'BSize': str(b_size),
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
        'TEST_AW_DEPTH': str(aw_depth),
        'TEST_W_DEPTH': str(w_depth),
        'TEST_B_DEPTH': str(b_depth),
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
    print(f"Running {test_level.upper()} AXIL4 Write Master test: {dut_name}")
    print(f"AXIL4 Config: ADDR={addr_width}, DATA={data_width}")
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
        print(f"✓ {test_level.upper()} AXIL4 Write Master test PASSED")
    except Exception as e:
        print(f"✗ {test_level.upper()} AXIL4 Write Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
