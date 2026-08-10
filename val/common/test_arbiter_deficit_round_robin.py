# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_deficit_round_robin
# Purpose: Deficit round-robin arbiter test - cost-proportional shares
#
# Documentation: docs/markdown/rtl-common/index.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-08-09

"""
Deficit Round-Robin Arbiter Test

The property under test: long-run COST-UNITS served per client follow the
quantum ratio, whatever the per-request costs are. Scenarios per level:

GATE:  equal-cost shares + zero-quantum disable
FUNC:  + mixed random costs (the DRR-defining case), cost > quantum
         (multi-round accumulation), anti-hoarding
FULL:  + dynamic quantum change (atomic update FSM)

Every scenario also runs the TB's cycle mirror of the deficit discipline:
a grant to a client whose deficit did not cover its cost fails the test.
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
from TBClasses.common.arbiter_deficit_round_robin_tb import DeficitRoundRobinTB


@cocotb.test(timeout_time=2, timeout_unit="ms")
async def arbiter_deficit_round_robin_test(dut):
    """Cost-proportional share + deficit-discipline verification."""
    tb = DeficitRoundRobinTB(dut)

    test_level = os.environ.get('TEST_LEVEL', 'gate').lower()
    if test_level not in ('gate', 'func', 'full'):
        tb.log.warning(f"Invalid TEST_LEVEL '{test_level}', using 'gate'")
        test_level = 'gate'

    completions = {'gate': 300, 'func': 600, 'full': 1000}[test_level]

    tb.log.info(f"DRR test level={test_level.upper()} clients={tb.CLIENTS} "
                f"max_quantum={tb.MAX_QUANTUM} cost_width={tb.COST_WIDTH} "
                f"ack={tb.WAIT_GNT_ACK} seed={tb.SEED}")

    await tb.setup_clocks_and_reset()

    await tb.scenario_equal_cost(completions)
    await tb.scenario_disable(completions)

    if test_level in ('func', 'full'):
        await tb.scenario_mixed_costs(completions)
        await tb.scenario_cost_gt_quantum(completions)
        await tb.scenario_anti_hoarding(completions)

    if test_level == 'full':
        await tb.scenario_quantum_change(completions)

    tb.log.info("DRR test complete - all scenarios passed")


def generate_test_params():
    """
    (clients, max_quantum, cost_width, wait_ack) grid by REG_LEVEL.

    GATE: 2 tests (4 clients, both ack modes)
    FUNC: 6 tests (4/6/8 clients, both ack modes) - default
    FULL: 10 tests (up to 16 clients, wider costs)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    all_configs = [
        ( 4, 16, 4, 0),
        ( 4, 16, 4, 1),
        ( 6, 16, 4, 0),
        ( 6, 16, 4, 1),
        ( 8, 16, 5, 0),
        ( 8, 16, 5, 1),
        (16, 32, 6, 0),
        (16, 32, 6, 1),
        ( 4,  8, 8, 0),   # costs far above quantum: accumulation stress
        ( 4,  8, 8, 1),
    ]

    if reg_level == 'GATE':
        return all_configs[0:2]
    elif reg_level == 'FUNC':
        return all_configs[0:6]
    return all_configs


@pytest.mark.parametrize("clients, max_quantum, cost_width, wait_ack",
                         generate_test_params())
def test_arbiter_deficit_round_robin(request, clients, max_quantum,
                                     cost_width, wait_ack):
    """Pytest wrapper for the deficit round-robin arbiter."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes'})

    dut_name = "arbiter_deficit_round_robin"
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/arbiter_deficit_round_robin.f')

    c_str = TBBase.format_dec(clients, 2)
    q_str = TBBase.format_dec(max_quantum, 2)
    cw_str = TBBase.format_dec(cost_width, 1)
    w_str = TBBase.format_dec(wait_ack, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = \
        f"test_{dut_name}_c{c_str}_q{q_str}_cw{cw_str}_w{w_str}_{reg_level}"

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
        'MAX_QUANTUM': max_quantum,
        'COST_WIDTH': cost_width,
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
        'TEST_MAX_QUANTUM': str(max_quantum),
        'TEST_COST_WIDTH': str(cost_width),
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
        print(f"DRR test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
