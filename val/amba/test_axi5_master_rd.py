# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi5_master_rd
# Purpose: AXI5 Read Master Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-12-16

"""
AXI5 Read Master Test Runner

Test runner for the AXI5 read master using the CocoTB framework.
Tests various AXI5 configurations and validates read transactions with
AXI5-specific features like NSAID, TRACE, MPAM, MECID, TAGOP, etc.

TEST LEVELS (per-test depth):
    basic (30s-2min):  Quick verification during development
    medium (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 2 tests (~5 min) - smoke test (stub + non-stub, one config each)
    FUNC: 8 tests (~30 min) - functional coverage - DEFAULT
    FULL: 48 tests (~4 hours) - comprehensive validation

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
from CocoTBFramework.tbclasses.axi5.axi5_master_read_tb import AXI5MasterReadTB


@cocotb.test(timeout_time=30, timeout_unit="sec")
async def axi5_read_master_test(dut):
    """AXI5 read master test using the AXI5 framework components"""

    # Create testbench instance
    tb = AXI5MasterReadTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    # Use the seed for reproducibility
    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI5 read master test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXI5 read master test...")
    tb.log.info(f"AXI5 widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, "
               f"DATA={tb.TEST_DATA_WIDTH}, NSAID={tb.TEST_NSAID_WIDTH}")

    # Define test configurations based on test level
    if test_level == 'basic':
        timing_profiles = ['normal', 'fast']
        single_read_counts = [10, 20]
        burst_lengths = [[2, 4], [4, 8]]
        axi5_feature_count = 10
        stress_count = 25
    elif test_level == 'medium':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_read_counts = [20, 40, 30]
        burst_lengths = [[2, 4, 8], [4, 8, 16], [1, 2, 4, 8]]
        axi5_feature_count = 25
        stress_count = 50
    else:  # test_level == 'full'
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback', 'stress', 'mte', 'secure']
        single_read_counts = [30, 50, 75]
        burst_lengths = [[1, 2, 4, 8, 16], [2, 4, 8, 16, 32], [1, 3, 7, 15, 31]]
        axi5_feature_count = 50
        stress_count = 100

    tb.log.info(f"Testing with timing profiles: {timing_profiles}")

    # Test 1: Basic connectivity test
    tb.log.info("=== Test 1: Basic Connectivity ===")
    tb.set_timing_profile('normal')

    success, data, info = await tb.single_read_test(0x1000)
    if not success:
        tb.log.error("Basic connectivity test failed!")
        raise RuntimeError("Basic connectivity failed")

    tb.log.info(f"Basic connectivity test passed: data=0x{data:08X}")

    # Test 2: Single read sequences with different timing profiles
    tb.log.info("=== Test 2: Single Read Sequences ===")

    for i, (profile, count) in enumerate(zip(timing_profiles, single_read_counts)):
        tb.log.info(f"[{i+1}/{len(timing_profiles)}] Single reads with '{profile}' timing ({count} reads)")
        tb.set_timing_profile(profile)

        result = await tb.basic_read_sequence(count)
        if not result:
            tb.log.error(f"Single read sequence failed with '{profile}' timing")
        else:
            tb.log.info(f"Single read sequence passed with '{profile}' timing")

    # Test 3: Burst read sequences
    tb.log.info("=== Test 3: Burst Read Sequences ===")

    for i, (profile, lengths) in enumerate(zip(timing_profiles, burst_lengths)):
        tb.log.info(f"[{i+1}/{len(timing_profiles)}] Burst reads with '{profile}' timing: {lengths}")
        tb.set_timing_profile(profile)

        result = await tb.burst_read_sequence(lengths)
        if not result:
            tb.log.error(f"Burst read sequence failed with '{profile}' timing")
        else:
            tb.log.info(f"Burst read sequence passed with '{profile}' timing")

    # Test 4: AXI5 Feature Tests
    tb.log.info("=== Test 4: AXI5 Feature Tests ===")
    tb.set_timing_profile('normal')

    result = await tb.axi5_feature_test_sequence(axi5_feature_count)
    if result:
        tb.log.info(f"AXI5 feature tests passed ({axi5_feature_count} tests)")
    else:
        tb.log.warning(f"AXI5 feature tests had issues ({axi5_feature_count} tests)")

    # Test 5: Mixed read patterns (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Test 5: Mixed Read Patterns ===")

        tb.set_timing_profile('normal')
        mixed_success = 0
        mixed_total = 10

        for i in range(mixed_total):
            if i % 2 == 0:
                # Single read with AXI5 features
                addr = 0x1000 + (i * 4)
                nsaid = random.randint(0, 15)
                success, _, _ = await tb.single_read_test(addr, nsaid=nsaid, trace=1)
            else:
                # Short burst read
                addr = 0x2000 + (i * 16)
                success, _, _ = await tb.burst_read_test(addr, 4)

            if success:
                mixed_success += 1

            await tb.wait_clocks('aclk', 3)

        tb.log.info(f"Mixed patterns result: {mixed_success}/{mixed_total} successful")

    # Test 6: Stress testing (medium and full levels)
    if test_level in ['medium', 'full']:
        tb.log.info("=== Test 6: Stress Testing ===")

        result = await tb.stress_read_test(stress_count)
        if result:
            tb.log.info(f"Stress test passed ({stress_count} reads)")
        else:
            tb.log.warning(f"Stress test had issues ({stress_count} reads)")

    # Test 7: Security and MTE features (full level)
    if test_level == 'full':
        tb.log.info("=== Test 7: Security and MTE Features ===")

        tb.set_timing_profile('secure')
        security_count = 20

        for i in range(security_count):
            addr = 0x1000 + (i * 4)
            success, _, _ = await tb.single_read_test(
                addr,
                nsaid=random.randint(0, 15),
                mpam=random.randint(0, 2047),
                mecid=random.randint(0, 65535),
                tagop=random.randint(0, 3)
            )
            if not success:
                tb.log.warning(f"Security feature test {i} failed")

        tb.log.info(f"Security and MTE tests completed")

    # Final statistics and cleanup
    tb.log.info("=== Test Results Summary ===")
    stats = tb.get_test_stats()

    tb.log.info("Test Statistics:")
    tb.log.info(f"  Total reads: {stats['summary']['total_reads']}")
    tb.log.info(f"  Successful reads: {stats['summary']['successful_reads']}")
    tb.log.info(f"  Success rate: {stats['summary']['success_rate']}")
    tb.log.info(f"  Single reads: {stats['details']['single_reads']}")
    tb.log.info(f"  Burst reads: {stats['details']['burst_reads']}")
    tb.log.info(f"  AXI5 feature tests: {stats['axi5_features']['total_axi5_tests']}")
    tb.log.info(f"  NSAID tests: {stats['axi5_features']['nsaid_tests']}")
    tb.log.info(f"  TRACE tests: {stats['axi5_features']['trace_tests']}")
    tb.log.info(f"  MPAM tests: {stats['axi5_features']['mpam_tests']}")
    tb.log.info(f"  MECID tests: {stats['axi5_features']['mecid_tests']}")
    tb.log.info(f"  TAGOP tests: {stats['axi5_features']['tagop_tests']}")
    tb.log.info(f"  Data mismatches: {stats['details']['data_mismatches']}")
    tb.log.info(f"  Response errors: {stats['details']['response_errors']}")
    tb.log.info(f"  Timeout errors: {stats['details']['timeout_errors']}")

    # Determine overall test result
    success_rate = float(stats['summary']['success_rate'].rstrip('%'))
    if success_rate >= 95.0:
        tb.log.info(f"ALL {test_level.upper()} AXI5 READ MASTER TESTS PASSED!")
    else:
        tb.log.error(f"AXI5 READ MASTER TESTS FAILED (success rate: {success_rate:.1f}%)")
        raise RuntimeError(f"Test failed with {success_rate:.1f}% success rate")


def validate_axi5_params(params):
    """
    Validate AXI5 parameters to ensure they meet specification constraints.
    """
    for param in params:
        stub, id_w, addr_w, data_w, user_w, ar_d, r_d, level = param

        if addr_w > 64:
            raise ValueError(
                f"Invalid AXI5 configuration: addr_width={addr_w} exceeds maximum of 64-bits. "
                f"Full parameter set: {param}"
            )

    return params


def generate_axi5_params():
    """
    Generate AXI5 parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (smoke test - stub + non-stub)
    REG_LEVEL=FUNC: 8 tests (functional coverage) - default
    REG_LEVEL=FULL: 48 tests (comprehensive validation)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [
            (1, 8, 32, 32, 1, 2, 4, 'basic'),  # Stub version
            (0, 8, 32, 32, 1, 2, 4, 'basic'),  # Non-stub version
        ]
        return validate_axi5_params(params)

    elif reg_level == 'FUNC':
        stubs = [1, 0]
        configs = [
            (8, 32, 32, 1, 2, 4),
            (8, 32, 32, 1, 4, 8),
        ]
        test_levels = ['basic', 'medium']

        params = []
        for stub in stubs:
            for id_w, addr_w, data_w, user_w, ar_d, r_d in configs:
                for level in test_levels:
                    params.append((stub, id_w, addr_w, data_w, user_w, ar_d, r_d, level))

        return validate_axi5_params(params)

    else:  # FULL
        stubs = [1, 0]
        id_widths = [4, 8]
        addr_widths = [32, 64]
        data_width = 32
        user_width = 1
        ar_r_depths = [(2, 4), (4, 8)]
        test_levels = ['basic', 'medium', 'full']

        params = []
        for stub, id_w, addr_w, (ar_d, r_d), level in product(
                stubs, id_widths, addr_widths, ar_r_depths, test_levels):
            params.append((stub, id_w, addr_w, data_width, user_width, ar_d, r_d, level))

        return validate_axi5_params(params)


@pytest.mark.parametrize("stub, id_width, addr_width, data_width, user_width, ar_depth, r_depth, test_level",
                        generate_axi5_params())
def test_axi5_read_master(request, stub, id_width, addr_width, data_width, user_width,
                            ar_depth, r_depth, test_level):
    """Test AXI5 read master with different parameter combinations"""

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_axi5': 'rtl/amba/axi5/',
        'rtl_axi5_stubs': 'rtl/amba/axi5/stubs',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    if stub == 1:
        dir_key = 'rtl_axi5_stubs'
        dut_name = "axi5_master_rd_stub"
    else:
        dir_key = 'rtl_axi5'
        dut_name = "axi5_master_rd"

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

    verilog_sources = [
        os.path.join(rtl_dict['rtl_gaxi'], "gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict[dir_key], f"{dut_name}.sv"),
    ]

    for src in verilog_sources:
        if not os.path.exists(src):
            raise FileNotFoundError(f"RTL source not found: {src}")

    wstrb_width = data_width // 8

    # AXI5 specific parameters
    nsaid_width = 4
    mpam_width = 11
    mecid_width = 16
    tag_width = 4
    tagop_width = 2
    chunknum_width = 4
    num_tags = max(1, data_width // 128)
    chunk_strb_width = num_tags

    # Calculate packet sizes for AXI5
    ar_size = (id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + user_width +
               nsaid_width + 1 + mpam_width + mecid_width + 1 + 1 + tagop_width)
    r_size = (id_width + data_width + 2 + 1 + user_width + 1 + 1 + 1 + chunknum_width +
              chunk_strb_width + (tag_width * num_tags) + 1)

    rtl_parameters = {
        'SKID_DEPTH_AR': str(ar_depth),
        'SKID_DEPTH_R': str(r_depth),
        'AXI_ID_WIDTH': str(id_width),
        'AXI_ADDR_WIDTH': str(addr_width),
        'AXI_DATA_WIDTH': str(data_width),
        'AXI_USER_WIDTH': str(user_width),
        'AXI_WSTRB_WIDTH': str(wstrb_width),
        'AXI_NSAID_WIDTH': str(nsaid_width),
        'AXI_MPAM_WIDTH': str(mpam_width),
        'AXI_MECID_WIDTH': str(mecid_width),
        'AXI_TAG_WIDTH': str(tag_width),
        'AXI_TAGOP_WIDTH': str(tagop_width),
        'AXI_CHUNKNUM_WIDTH': str(chunknum_width),
        'AW': str(addr_width),
        'DW': str(data_width),
        'IW': str(id_width),
        'SW': str(wstrb_width),
        'UW': str(user_width),
        'ARSize': str(ar_size),
        'RSize': str(r_size),
    }

    timeout_multipliers = {'basic': 1, 'medium': 2, 'full': 4}
    complexity_factor = (data_width + addr_width + id_width) / 100.0
    timeout_ms = int(7500 * timeout_multipliers.get(test_level, 1) * max(1.0, complexity_factor))

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
        'TEST_STUB': str(stub),
        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',
        'TIMEOUT_CYCLES': '2000',
        'TEST_AR_DEPTH': str(ar_depth),
        'TEST_R_DEPTH': str(r_depth),
        'TEST_NSAID_WIDTH': str(nsaid_width),
        'TEST_MPAM_WIDTH': str(mpam_width),
        'TEST_MECID_WIDTH': str(mecid_width),
        'TEST_TAG_WIDTH': str(tag_width),
        'TEST_TAGOP_WIDTH': str(tagop_width),
        'TEST_CHUNKNUM_WIDTH': str(chunknum_width),
        'AXI5_COMPLIANCE_CHECK': '1',
    }

    includes = [rtl_dict['rtl_amba_includes']]
    compile_args = [
        "--trace",
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-DUSE_ASYNC_RESET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
        "-Wno-PINMISSING",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    sim_args = ["--trace", "--trace-depth", "99"]
    plusargs = ["--trace"]

    cmd_filename = create_view_cmd(os.path.dirname(log_path), log_path, sim_build,
                                    module, test_name_plus_params)

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI5 Read Master test: {dut_name}")
    print(f"AXI5 Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
    print(f"AXI5 Features: NSAID={nsaid_width}, MPAM={mpam_width}, MECID={mecid_width}")
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
            waves=False,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
            simulator="verilator",
        )
        print(f"{test_level.upper()} AXI5 Read Master test PASSED")
    except Exception as e:
        print(f"{test_level.upper()} AXI5 Read Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
