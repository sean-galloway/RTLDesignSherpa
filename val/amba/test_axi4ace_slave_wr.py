# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_axi4ace_slave_wr
# Purpose: AXI4-ACE Write Slave Test Runner
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-05

"""
AXI4-ACE Write Slave Test Runner

Test runner for the AXI4-ACE write slave using the CocoTB framework.
Tests various AXI4-ACE configurations and validates write response behavior
and AWSNOOP passthrough. The DUT has no WACK pin.

REG_LEVEL Control:
    GATE: 1 test  - smoke test (one config at gate level)
    FUNC: 4 tests - two depth configs at gate/func levels
    FULL: 24 tests - id {4,8} x addr {32,64} x depths x levels
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

from TBClasses.ace.ace_slave_write_tb import AXI4ACESlaveWriteTB


@cocotb.test(timeout_time=30, timeout_unit="ms")
async def axi4ace_slave_write_test(dut):
    """AXI4-ACE slave write test using the framework's ACE components."""

    tb = AXI4ACESlaveWriteTB(dut, aclk=dut.aclk, aresetn=dut.aresetn)

    seed = int(os.environ.get('SEED', '0'))
    random.seed(seed)
    tb.log.info(f'AXI4-ACE slave write test with seed: {seed}')

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

    tb.log.info(f"Starting {test_level.upper()} AXI4-ACE slave write test...")
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
        # Test 1: Basic slave connectivity test
        # =================================================================
        tb.log.info("=== Test 1: Basic Slave Connectivity ===")
        tb.set_timing_profile('normal')

        tb.log.info("Testing basic slave write response...")
        success, info = await tb.single_write_response_test(0x1000, 0xDEADBEEF)
        if not success:
            error_msg = f"Basic slave connectivity test failed: {info.get('error', 'Unknown error')}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info("Basic slave connectivity test passed")

        # =================================================================
        # Test 2: AWSNOOP matrix
        # =================================================================
        tb.log.info("=== Test 2: AWSNOOP Matrix ===")
        await tb.awsnoop_matrix_test()

        # =================================================================
        # Test 3: Single write responses with different timing profiles
        # =================================================================
        for profile in timing_profiles:
            tb.log.info(f"=== Test 3: Single Write Responses ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for count in single_write_counts:
                tb.log.info(f"Running {count} single write responses with '{profile}' timing...")
                success, stats = await tb.run_single_writes(count)
                if not success:
                    error_msg = f"Single write responses failed with '{profile}' timing: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"Single write responses passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 4: Burst write responses with different lengths
        # =================================================================
        for profile in ['normal', 'fast']:
            tb.log.info(f"=== Test 4: Burst Write Responses ({profile.upper()}) ===")
            tb.set_timing_profile(profile)

            for burst_config in burst_lengths:
                tb.log.info(f"Testing burst write responses with lengths {burst_config}...")
                success, stats = await tb.run_burst_writes(burst_config, count=3)
                if not success:
                    error_msg = f"Burst write responses failed: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"Burst write responses passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 5: Mixed operation responses
        # =================================================================
        if test_level in ['func', 'full']:
            tb.log.info("=== Test 5: Mixed Operation Responses ===")
            tb.set_timing_profile('normal')

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
                else:
                    success, info = await tb.burst_write_response_test(addr, data)

                if not success:
                    error_msg = f"Mixed operation response failed: {info}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

            tb.log.info("Mixed operation responses passed")

        # =================================================================
        # Test 6: Timing variation responses
        # =================================================================
        if test_level == 'full':
            tb.log.info("=== Test 6: Timing Variation Responses ===")
            for profile in timing_profiles:
                tb.set_timing_profile(profile)
                success, stats = await tb.run_single_writes(10)
                if not success:
                    error_msg = f"Timing variation responses failed with {profile}: {stats}"
                    tb.log.error(error_msg)
                    raise Exception(error_msg)

                tb.log.info(f"{profile.capitalize()} timing responses passed ({stats['success_rate']:.1%})")

        # =================================================================
        # Test 7: Address range responses
        # =================================================================
        tb.log.info("=== Test 7: Address Range Responses ===")
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

            tb.log.info(f"{description} responses passed")

        # =================================================================
        # Test 8: Stress testing
        # =================================================================
        tb.log.info("=== Test 8: Slave Stress Testing ===")
        tb.set_timing_profile('stress')

        tb.log.info(f"Running slave stress test with {stress_count} mixed operations...")
        success, stats = await tb.stress_test(stress_count)
        if not success:
            error_msg = f"Slave stress test failed: {stats}"
            tb.log.error(error_msg)
            raise Exception(error_msg)

        tb.log.info(f"Slave stress test passed ({stats['success_rate']:.1%} success rate)")

        # =================================================================
        # Test 9: Outstanding transaction responses
        # =================================================================
        if test_level in ['func', 'full']:
            tb.log.info("=== Test 9: Outstanding Transaction Responses ===")
            tb.set_timing_profile('backtoback')

            success, stats = await tb.test_outstanding_transactions(count=20)
            if success:
                tb.log.info(f"Outstanding transaction responses passed ({stats['success_rate']:.1%})")
            else:
                tb.log.warning(f"Outstanding transaction responses had issues: {stats}")

        # =================================================================
        # Test 10: busy output check
        # =================================================================
        tb.log.info("=== Test 10: busy Output Check ===")
        await tb.check_busy()

        # =================================================================
        # Final Results
        # =================================================================
        final_stats = tb.get_test_stats()
        total_writes = final_stats['summary']['total_writes']
        successful_writes = final_stats['summary']['successful_writes']
        failed_writes = final_stats['summary']['failed_writes']

        tb.log.info("=" * 80)
        tb.log.info("AXI4-ACE SLAVE WRITE TEST RESULTS")
        tb.log.info("=" * 80)
        tb.log.info(f"Total write responses:      {total_writes}")
        tb.log.info(f"Successful responses:       {successful_writes}")
        tb.log.info(f"Failed responses:           {failed_writes}")
        tb.log.info(
            f"Success rate:               {(successful_writes/total_writes*100) if total_writes > 0 else 0:.2f}%"
        )
        tb.log.info(f"Test level:                 {test_level.upper()}")
        tb.log.info(f"Test duration:              {final_stats['summary']['test_duration']:.2f}s")

        if failed_writes > 0:
            tb.log.error("AXI4-ACE slave write test FAILED: Some responses failed")
            raise Exception(f"AXI4-ACE slave write test FAILED: {failed_writes} responses failed")

        tb.log.info("AXI4-ACE slave write test PASSED: All responses successful")

    except Exception as e:
        tb.log.error(f"AXI4-ACE slave write test FAILED with exception: {str(e)}")
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
def test_axi4ace_slave_write(id_width, addr_width, data_width, user_width,
                             aw_depth, w_depth, b_depth, test_level):
    """Test AXI4-ACE write slave with specified parameters."""

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_ace': 'rtl/amba/ace',
        'rtl_gaxi': 'rtl/amba/gaxi',
        'rtl_amba_includes': 'rtl/amba/includes'
    })

    dut_name = "axi4ace_slave_wr"

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

    module = "test_axi4ace_slave_wr"

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
    print(f"Running {test_level.upper()} AXI4-ACE Slave Write test: {dut_name}")
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
        print(f"{test_level.upper()} AXI4-ACE Slave Write test PASSED")
    except Exception as e:
        print(f"{test_level.upper()} AXI4-ACE Slave Write test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
