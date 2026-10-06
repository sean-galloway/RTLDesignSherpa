# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4ace_master_wr
# Purpose: AXI4-ACE Write Master Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-05

"""
AXI4-ACE Write Master Test Runner

Test runner for the AXI4-ACE write master using the CocoTB framework.
Tests various AXI4-ACE configurations and validates write transactions,
AWSNOOP passthrough, and the auto-pulsed m_axi_wack acknowledge.

TEST LEVELS (per-test depth):
    basic (30s-2min):  Quick verification during development
    medium (2-5 min):  Integration testing for CI/branches
    full (5-15 min):   Comprehensive validation for regression

REG_LEVEL Control (parameter combinations):
    GATE: 1 test  - smoke test (one config at gate level)
    FUNC: 4 tests - two depth configs at gate/func levels
    FULL: 24 tests - id {4,8} x addr {32,64} x depths x levels

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
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path

from TBClasses.ace.ace_master_write_tb import AXI4ACEMasterWriteTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4ace_write_master_test(dut):
    """AXI4-ACE write master test using the framework's ACE components."""

    tb = AXI4ACEMasterWriteTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4-ACE write master test with seed: {seed}')

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()

    valid_levels = ['gate', 'func', 'full']
    if test_level not in valid_levels:
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'. Valid: {valid_levels}")
        test_level = 'gate'

    await tb.start_clock('aclk', tb.TEST_CLK_PERIOD, 'ns')
    await tb.assert_reset()
    await tb.wait_clocks('aclk', 10)
    await tb.deassert_reset()
    await tb.wait_clocks('aclk', 10)

    tb.log.info(f"Starting {test_level.upper()} AXI4-ACE write master test...")
    tb.log.info(
        f"AXI4-ACE widths: ID={tb.TEST_ID_WIDTH}, ADDR={tb.TEST_ADDR_WIDTH}, "
        f"DATA={tb.TEST_DATA_WIDTH}, USER={tb.TEST_USER_WIDTH}"
    )

    if test_level == 'gate':
        timing_profiles = ['normal', 'fast']
        single_write_counts = [10, 20]
        burst_lengths = [[2, 4], [4, 8]]
        stress_count = 25
        run_error_tests = False
    elif test_level == 'func':
        timing_profiles = ['normal', 'fast', 'slow', 'backtoback']
        single_write_counts = [20, 40, 30]
        burst_lengths = [[2, 4, 8], [4, 8, 16], [1, 2, 4, 8]]
        stress_count = 50
        run_error_tests = True
    else:  # full
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
        tb.log.info("=== Test 1: Basic Connectivity ===")
        tb.set_timing_profile('normal')

        tb.log.info("Testing basic write connectivity...")
        success, info = await tb.single_write_test(0x1000, 0xDEADBEEF)
        if not success:
            error_msg = f"Basic connectivity test failed: {info.get('error', 'Unknown error')}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("Basic connectivity test passed")

        # =================================================================
        # Test 2: WACK pulse check (ACE master only)
        # =================================================================
        tb.log.info("=== Test 2: WACK Pulse Check ===")
        await tb.wack_check(0x7000, 0xBEEFCAFE)

        # =================================================================
        # Test 3: AWSNOOP matrix
        # =================================================================
        tb.log.info("=== Test 3: AWSNOOP Matrix ===")
        await tb.awsnoop_matrix_test()

        # =================================================================
        # Test 4: Single writes with different timing profiles
        # =================================================================
        for profile in timing_profiles:
            tb.log.info(f"=== Test 4: Single Writes ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for count in single_write_counts:
                tb.log.info(f"Running {count} single writes with {profile} timing...")
                success, stats = await tb.run_single_writes(count)
                if not success:
                    error_msg = f"Single write test failed with {profile} timing: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"{count} single writes passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 5: Burst writes with different timing profiles
        # =================================================================
        for profile in timing_profiles:
            tb.log.info(f"=== Test 5: Burst Writes ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for burst_lens in burst_lengths:
                tb.log.info(f"Testing burst writes with lengths {burst_lens} and {profile} timing...")
                success, stats = await tb.run_burst_writes(burst_lens, count=10)
                if not success:
                    error_msg = f"Burst write test failed with {profile} timing: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"Burst writes passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 6: Address boundary testing
        # =================================================================
        tb.log.info("=== Test 6: Address Boundary Testing ===")
        tb.set_timing_profile('normal')

        memory_size = tb.memory_model.size
        max_valid_addr = memory_size - 4

        boundary_addresses = [
            0x0,
            0x4,
            0x1000,
            max_valid_addr,
        ]

        for addr in boundary_addresses:
            if addr > max_valid_addr:
                addr = max_valid_addr
            data = 0xA5A5A5A5
            tb.log.info(f"Testing boundary address 0x{addr:08X}...")
            success, info = await tb.single_write_test(addr, data)
            if not success:
                tb.log.warning(f"Boundary test failed at address 0x{addr:08X}: {info}")

        tb.log.info("Address boundary testing completed")

        # =================================================================
        # Test 7: Data pattern testing
        # =================================================================
        tb.log.info("=== Test 7: Data Pattern Testing ===")
        tb.set_timing_profile('normal')

        test_patterns = [
            0x00000000,
            0xFFFFFFFF,
            0x55555555,
            0xAAAAAAAA,
            0x12345678,
            0x87654321,
        ]

        base_addr = 0x2000
        for i, pattern in enumerate(test_patterns):
            pattern = pattern & tb.MAX_DATA
            addr = base_addr + (i * 4)
            tb.log.info(f"Testing data pattern 0x{pattern:08X}...")
            success, info = await tb.single_write_test(addr, pattern)
            if not success:
                tb.log.warning(f"Pattern test failed for 0x{pattern:08X}: {info}")

        tb.log.info("Data pattern testing completed")

        # =================================================================
        # Test 8: ID field testing
        # =================================================================
        if tb.TEST_ID_WIDTH > 1:
            tb.log.info("=== Test 8: Transaction ID Testing ===")
            tb.set_timing_profile('normal')

            test_ids = [0, 1, tb.MAX_ID // 2, tb.MAX_ID]
            base_addr = 0x3000

            for test_id in test_ids:
                addr = base_addr + (test_id * 4)
                data = 0x12340000 + test_id
                tb.log.info(f"Testing transaction ID {test_id}...")
                success, info = await tb.single_write_test(addr, data, transaction_id=test_id)
                if not success:
                    tb.log.warning(f"ID test failed for ID {test_id}: {info}")

            tb.log.info("Transaction ID testing completed")

        # =================================================================
        # Test 9: Error injection testing
        # =================================================================
        if run_error_tests:
            tb.log.info("=== Test 9: Error Injection Testing ===")
            await tb.run_error_injection_tests()
            tb.log.info("Error injection testing completed")

        # =================================================================
        # Test 10: Stress testing
        # =================================================================
        tb.log.info("=== Test 10: Stress Testing ===")
        tb.set_timing_profile('stress')

        tb.log.info(f"Running stress test with {stress_count} mixed operations...")
        success, stats = await tb.stress_test(stress_count)
        if not success:
            error_msg = f"Stress test failed: {stats}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info(f"Stress test passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 11: Outstanding transaction testing
        # =================================================================
        if test_level in ['func', 'full']:
            tb.log.info("=== Test 11: Outstanding Transaction Testing ===")
            tb.set_timing_profile('backtoback')

            success, stats = await tb.test_outstanding_transactions(count=20)
            if success:
                tb.log.info(f"Outstanding transaction test passed ({stats['success_rate']:.1%})")
            else:
                tb.log.warning(f"Outstanding transaction test had issues: {stats}")

        # =================================================================
        # Test 12: busy output check
        # =================================================================
        tb.log.info("=== Test 12: busy Output Check ===")
        await tb.check_busy()

        # =================================================================
        # Final Results
        # =================================================================
        tb.finalize_test()
        final_stats = tb.get_test_stats()
        total_writes = final_stats['summary']['total_writes']
        successful_writes = final_stats['summary']['successful_writes']
        failed_writes = final_stats['summary']['failed_writes']

        tb.log.info("=" * 80)
        tb.log.info("AXI4-ACE WRITE MASTER TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Total writes:      {total_writes}")
        tb.log.info(f"Successful writes: {successful_writes}")
        tb.log.info(f"Failed writes:     {failed_writes}")
        tb.log.info(
            f"Success rate:      {(successful_writes/total_writes*100) if total_writes > 0 else 0:.2f}%"
        )
        tb.log.info(f"Test level:        {test_level.upper()}")
        tb.log.info(f"Test duration:     {final_stats['summary']['test_duration']:.2f}s")

        if failed_writes > 0:
            tb.log.error("AXI4-ACE write master test FAILED: Some writes failed")
            raise Exception(f"AXI4-ACE write master test FAILED: {failed_writes} writes failed")

        tb.log.info("AXI4-ACE write master test PASSED: All writes successful")

    except Exception as e:
        tb.log.error(f"AXI4-ACE write master test FAILED with exception: {str(e)}")
        final_stats = tb.get_test_stats()
        tb.log.error(f"Final stats: {final_stats['summary']}")
        raise


def validate_axi4ace_params(params):
    """Validate AXI4-ACE parameters to ensure they meet specification constraints."""
    for param in params:
        id_w, addr_w, data_w, user_w, aw_d, w_d, b_d, level = param

        if addr_w > 64:
            raise ValueError(
                f"Invalid AXI4-ACE configuration: addr_width={addr_w} exceeds maximum of 64-bits. "
                f"Full parameter set: {param}"
            )

    return params


def generate_axi4ace_params():
    """
    Generate AXI4-ACE parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test
    REG_LEVEL=FUNC: 4 tests
    REG_LEVEL=FULL: 24 tests

    Parameters: (id_width, addr_width, data_width, user_width,
                 aw_depth, w_depth, b_depth, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        params = [
            (8, 32, 32, 1, 2, 4, 2, 'gate'),
        ]
        return validate_axi4ace_params(params)

    elif reg_level == 'FUNC':
        configs = [
            (8, 32, 32, 1, 2, 4, 2),
            (8, 32, 32, 1, 4, 8, 4),
        ]
        test_levels = ['gate', 'func']

        params = []
        for id_w, addr_w, data_w, user_w, aw_d, w_d, b_d in configs:
            for level in test_levels:
                params.append((id_w, addr_w, data_w, user_w, aw_d, w_d, b_d, level))
        return validate_axi4ace_params(params)

    else:  # FULL
        id_widths = [4, 8]
        addr_widths = [32, 64]
        data_width = 32
        user_width = 1
        depth_sets = [
            (2, 4, 2),
            (4, 8, 4),
        ]
        test_levels = ['gate', 'func', 'full']

        params = []
        for id_w, addr_w, (aw_d, w_d, b_d), level in product(
                id_widths, addr_widths, depth_sets, test_levels):
            params.append((id_w, addr_w, data_width, user_width, aw_d, w_d, b_d, level))
        return validate_axi4ace_params(params)


@pytest.mark.parametrize(
    "id_width, addr_width, data_width, user_width, aw_depth, w_depth, b_depth, test_level",
    generate_axi4ace_params()
)
def test_axi4ace_write_master(id_width, addr_width, data_width, user_width,
                              aw_depth, w_depth, b_depth, test_level):
    """Test AXI4-ACE write master with specified parameters."""

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_ace': 'rtl/amba/ace',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi4ace_master_wr"

    id_str = TBBase.format_dec(id_width, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    uw_str = TBBase.format_dec(user_width, 1)
    awd_str = TBBase.format_dec(aw_depth, 1)
    wd_str = TBBase.format_dec(w_depth, 1)
    bd_str = TBBase.format_dec(b_depth, 1)

    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = (
        f"test_{worker_id}_{dut_name}_i{id_str}_a{aw_str}_d{dw_str}_u{uw_str}_"
        f"awd{awd_str}_wd{wd_str}_bd{bd_str}_{test_level}_{reg_level}"
    )

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path=f'rtl/amba/filelists/{dut_name}.f'
    )

    wstrb_width = data_width // 8
    aw_size = id_width + addr_width + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + user_width + 3
    w_size = data_width + wstrb_width + 1 + user_width
    b_size = id_width + 2 + user_width

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

    timeout_ms = 5000 if test_level == 'gate' else 10000 if test_level == 'func' else 20000

    module = "test_axi4ace_master_wr"

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'TEST_LEVEL': test_level,
        'COCOTB_TEST_TIMEOUT': str(timeout_ms),

        'TEST_ID_WIDTH': str(id_width),
        'TEST_ADDR_WIDTH': str(addr_width),
        'TEST_DATA_WIDTH': str(data_width),
        'TEST_USER_WIDTH': str(user_width),
        'TEST_CLK_PERIOD': '10',
        'TIMEOUT_CYCLES': str(timeout_ms // 10),
        'SEED': os.environ.get('SEED', str(random.randint(1, 999999))),

        'TEST_AW_DEPTH': str(aw_depth),
        'TEST_W_DEPTH': str(w_depth),
        'TEST_B_DEPTH': str(b_depth),
        'AXI4_COMPLIANCE_CHECK': '1',
    }

    compile_args = [
        "--trace",
        "--trace-depth", "99",
        "-Wall", "-Wno-SYNCASYNCNET", "-DUSE_ASYNC_RESET",
        "-Wno-UNUSED",
        "-Wno-DECLFILENAME",
    ]

    sim_args = ["--trace", "--trace-depth", "99"]
    plus_args = ["--trace"]

    cmd_filename = create_view_cmd(
        os.path.dirname(log_path), log_path, sim_build, module, test_name_plus_params
    )

    print(f"\n{'='*80}")
    print(f"Running {test_level.upper()} AXI4-ACE Write Master test: {dut_name}")
    print(f"AXI4-ACE Config: ID={id_width}, ADDR={addr_width}, DATA={data_width}, USER={user_width}")
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
            waves=enable_waves,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plus_args=plus_args,
        )
        print(f"{test_level.upper()} AXI4-ACE Write Master test PASSED")
    except Exception as e:
        print(f"{test_level.upper()} AXI4-ACE Write Master test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
