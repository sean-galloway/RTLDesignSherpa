# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_divider_srt_radix4
# Purpose: Test for the divider_srt_radix4 integer divider module.
#
# Documentation: docs/markdown/rtl-math/overview.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2026-10-11

"""
Test for the restoring integer divider module.

Suite (shared driver in divider_tb_common): directed corners, divide-by-zero,
random sweep vs Python divmod; FULL adds exhaustive W=8 and back-to-back.
"""
import os
import random
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from TBClasses.shared.filelist_utils import get_sources_from_filelist

import divider_tb_common

DUT_NAME = "math_divider_srt_radix4"


def _grid():
    """(DATA_WIDTH, TEST_LEVEL) grid keyed on REG_LEVEL."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [(8, 'gate')]
    if reg_level == 'FULL':
        return [(8, 'full'), (32, 'full'), (33, 'full')]
    return [(32, 'func')]


@cocotb.test(timeout_time=500, timeout_unit="ms")
async def divider_test(dut):
    """Run the shared divider suite."""
    data_width = int(os.environ['PARAM_WIDTH'])
    level = os.environ.get('TEST_LEVEL', 'func').lower()
    seed = int(os.environ.get('SEED', '0'))
    await divider_tb_common.divider_suite(
        dut, DUT_NAME, data_width, level, seed)


@pytest.mark.parametrize("data_width,test_level", _grid())
def test_math_divider_srt_radix4(request, data_width, test_level):
    """PyTest function to run the cocotb test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common'
    })

    dut_name = DUT_NAME
    toplevel = dut_name

    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        module=dut_name
    )

    parameters = {'DATA_WIDTH': data_width}

    test_name_plus_params = f"test_{dut_name}_W{data_width}_{test_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)

    os.makedirs(log_dir, exist_ok=True)
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    seed = int(os.environ.get('SEED', str(random.randint(0, 100000))))

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': str(seed),
        'TEST_LEVEL': test_level,
        'PARAM_WIDTH': str(data_width),
    }

    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(
        log_dir, log_path, sim_build, module, test_name_plus_params)

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
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the Waveforms run this command: {cmd_filename}")
        raise
