# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_token_bucket
# Purpose: Token-bucket request shaper test - rate, burst, never-overspend
#
# Documentation: docs/markdown/rtl-common/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-10

"""
Token-Bucket Request Shaper Test

The properties under test: completed grants never exceed refilled tokens
(the invariant, asserted per completion), sustained rate tracks the refill
rate under saturation, burst allowance is exactly the cap, cap-0 clients
are unshaped (fail-open), and a runtime rate cut drains-then-blocks with
no update FSM.

GATE:  sustained rate + bypass
FUNC:  + burst allowance, rate-0 drain
FULL:  same scenarios at longer durations
"""

import os
import random
import cocotb
from cocotb_test.simulator import run
import pytest

from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args
from TBClasses.common.arbiter_token_bucket_tb import TokenBucketTB


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def arbiter_token_bucket_test(dut):
    """Rate/burst/overspend verification for the request shaper."""
    tb = TokenBucketTB(dut)

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    cycles = {'gate': 800, 'func': 2000, 'full': 5000}[test_level]

    tb.log.info(f"Token bucket test level={test_level.upper()} "
                f"clients={tb.CLIENTS} max_tokens={tb.MAX_TOKENS} "
                f"ack={tb.WAIT_GNT_ACK} seed={tb.SEED}")

    await tb.setup_clocks_and_reset()

    await tb.scenario_sustained_rate(cycles)
    await tb.scenario_bypass(cycles // 2)

    if test_level in ('func', 'full'):
        await tb.scenario_burst_allowance()
        await tb.scenario_rate_zero_drain()

    tb.log.info("Token bucket test complete - all scenarios passed")


def generate_test_params():
    """
    (clients, max_tokens, rate_width, wait_ack) grid by REG_LEVEL.

    GATE: 2 tests (4 clients, both ack modes)
    FUNC: 4 tests (+8 clients) - default
    FULL: 6 tests (+16 clients, small buckets)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_configs = [
        ( 4, 64, 4, 0),
        ( 4, 64, 4, 1),
        ( 8, 32, 3, 0),
        ( 8, 32, 3, 1),
        (16,  8, 2, 0),
        (16,  8, 2, 1),
    ]

    if reg_level == 'GATE':
        return all_configs[0:2]
    elif reg_level == 'FUNC':
        return all_configs[0:4]
    return all_configs


@pytest.mark.parametrize("clients, max_tokens, rate_width, wait_ack",
                         generate_test_params())
def test_arbiter_token_bucket(request, clients, max_tokens, rate_width,
                              wait_ack):
    """Pytest wrapper for the token-bucket request shaper."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "arbiter_token_bucket"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_token_bucket.f')

    c_str = TBBase.format_dec(clients, 2)
    t_str = TBBase.format_dec(max_tokens, 2)
    r_str = TBBase.format_dec(rate_width, 1)
    w_str = TBBase.format_dec(wait_ack, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = \
        f"test_{dut_name}_c{c_str}_t{t_str}_r{r_str}_w{w_str}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    parameters = {
        'CLIENTS': clients,
        'MAX_TOKENS': max_tokens,
        'RATE_WIDTH': rate_width,
        'WAIT_GNT_ACK': wait_ack,
    }

    extra_env = {
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', reg_level.lower()),
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_CLIENTS': str(clients),
        'TEST_MAX_TOKENS': str(max_tokens),
        'TEST_RATE_WIDTH': str(rate_width),
        'TEST_WAIT_GNT_ACK': str(wait_ack),
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]
    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []
    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module,
                                   test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,
            waves=enable_waves,
        )
    except Exception as e:
        print(f"Token bucket test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
