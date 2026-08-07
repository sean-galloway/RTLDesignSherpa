# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_math_bf16_fma_systematic
# Purpose: Systematic edge-case testing for BF16 FMA around power-of-2 boundaries.
#
# Documentation: BF16_ARCHITECTURE.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-11-25

"""
Systematic Edge-Case Test for BF16 FMA.

This test systematically explores all combinations of power-of-2 boundary values
for the BF16 FMA. By testing at exponent boundaries (2^n - 1, 2^n, 2^n + 1),
we catch edge cases in:
- Exponent calculation and bias handling
- Mantissa normalization
- Overflow/underflow detection
- Rounding at boundaries

The test uses itertools.product to exhaustively cover all combinations,
making it easy to identify pass/fail patterns around specific boundaries.
"""
import os
import random
import struct
import itertools
import pytest
import cocotb
from cocotb.triggers import Timer
from cocotb_test.simulator import run

from TBClasses.shared.utilities import get_paths, create_view_cmd
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.math.math_bf16_fma_systematic_tb import BF16FMASystematicTB
from TBClasses.shared.tbbase import TBBase


@cocotb.test(timeout_time=120, timeout_unit="ms")
async def bf16_fma_systematic_test(dut):
    """Systematic power-of-2 boundary test for BF16 FMA."""
    tb = BF16FMASystematicTB(dut)

    await tb.wait_time(1, 'ns')

    passed = await tb.run_systematic_tests()

    assert passed, f"Systematic test failed with {tb.fail_count} failures"

def get_test_params():
    """Generate test parameters."""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    if reg_level == 'GATE':
        return [{'test_level': 'gate'}]
    if reg_level == 'FULL':
        return [{'test_level': 'gate'}, {'test_level': 'func'}, {'test_level': 'full'}]
    return [{'test_level': 'func'}]

@pytest.mark.parametrize("params", get_test_params())
def test_math_bf16_fma_systematic(request, params):
    """PyTest wrapper for systematic BF16 FMA test."""
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_cmn': 'rtl/common',
        'rtl_math': 'rtl/math'
    })

    dut_name = "math_bf16_fma"
    toplevel = dut_name

    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()
    test_name_plus_params = f"test_{dut_name}_systematic_{reg_level}"

    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    verilog_sources, includes = get_sources_from_filelist(

        repo_root=repo_root,

        filelist_path='rtl/math/filelists/math_bf16_fma.f'

    )

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
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
        'TEST_LEVEL': params['test_level'],
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    if bool(int(os.environ.get('WAVES', '0'))):
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    sim_args = ['--trace'] if enable_waves else []

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise
