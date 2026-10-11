# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_arbiter_matrix_weighted
# Purpose: Test runner for the weighted matrix arbiter.
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-11

"""
Test runner for arbiter_matrix_weighted.

Validates weighted matrix arbitration across a parameterization sweep.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

from TBClasses.common.arbiter_matrix_weighted_tb import ArbiterMatrixWeightedTB
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=20, timeout_unit="ms")
async def cocotb_arbiter_matrix_weighted_test(dut):
    """Run the weighted matrix arbiter testbench."""
    tb = ArbiterMatrixWeightedTB(dut)
    await tb.setup_clocks_and_reset()
    passed = await tb.run_all_tests()
    assert passed, "arbiter_matrix_weighted test failed"


def generate_test_params():
    """
    Parameter sweep based on REG_LEVEL.

    REG_LEVEL=GATE: 2, 4 clients, both ACK modes
    REG_LEVEL=FUNC: 2, 4, 5, 8 clients, no-ACK only (default)
    REG_LEVEL=FULL: 2, 4, 5, 8 clients, both ACK modes
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        client_counts = [2, 4]
    else:
        client_counts = [2, 4, 5, 8]

    params = []
    for clients in client_counts:
        if reg_level == 'FUNC':
            params.append((clients, 0))  # no-ACK mode only for quick regression
        else:
            params.append((clients, 0))  # no-ACK mode
            params.append((clients, 1))  # ACK mode
    return params


@pytest.mark.parametrize("clients, wait_ack", generate_test_params())
def test_arbiter_matrix_weighted(request, clients, wait_ack):
    """Run the weighted matrix arbiter test with the requested configuration."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_common': 'rtl/common'
    })

    dut_name = "arbiter_matrix_weighted"
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module='arbiter_matrix_weighted'
    )

    cl_str = TBBase.format_dec(clients, 2)
    w_str = TBBase.format_dec(wait_ack, 1)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_{dut_name}_c{cl_str}_w{w_str}_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    rtl_parameters = {
        'CLIENTS': clients,
        'WAIT_GNT_ACK': wait_ack,
    }

    extra_env = {
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', reg_level.lower()),
        'LOG_PATH': log_path,
        'PARAM_CLIENTS': str(clients),
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
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

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params
    )

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            testcase="cocotb_arbiter_matrix_weighted_test",
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,
            waves=enable_waves,
        )
        print(f"Test completed! Logs: {log_path}")
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Configuration: CLIENTS={clients}, WAIT_GNT_ACK={wait_ack}")
        print(f"Logs: {log_path}")
        print(f"View waves: {cmd_filename}")
        raise
