# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: HammingECCTB
# Purpose: Hamming ECC Test with Parameterized Test Levels and Module Selection
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Hamming ECC Test with Parameterized Test Levels and Module Selection

This test uses module_type and test_level as parameters for maximum flexibility:

MODULE TYPES:
    encoder:  Test only the encoder module (combinational)
    decoder:  Test only the decoder module (sequential)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - data_width: [4, 8, 16, 32]
    - module_type: [encoder, decoder]
    - test_level: [gate, func, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Data width for ECC calculation
    TEST_MODULE: Module type (encoder/decoder/both)
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.dataint_ecc_tb import HammingECCTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def dataint_ecc_test(dut):
    """Unified test for Hamming ECC modules"""
    tb = HammingECCTB(dut)

    # Start clock if needed (for decoder module)
    if tb.MODULE_TYPE == 'decoder':
        await tb.start_clock('clk', 10, 'ns')

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"{tb.MODULE_TYPE.upper()} test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Hamming ECC {tb.MODULE_TYPE} test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (4-bit, both modules, gate)
    REG_LEVEL=FUNC: 6 tests (all widths, both modules, gate) - default
    REG_LEVEL=FULL: 18 tests (all combinations)

    Returns:
        List of tuples: (data_width, module_type, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [4, 8, 16]  # Different data widths
    modules = ['encoder', 'decoder']  # Module types
    test_levels = ['gate', 'func', 'full']

    if reg_level == 'GATE':
        # Quick smoke test: 4-bit, both modules, gate level
        return [(4, 'encoder', 'gate'), (4, 'decoder', 'gate')]

    elif reg_level == 'FUNC':
        # Functional coverage: all widths, both modules, gate level only
        return list(product(widths, modules, ['gate']))

    else:  # FULL
        # Comprehensive: all combinations
        return list(product(widths, modules, test_levels))

params = generate_params()

@pytest.mark.parametrize("data_width, module_type, test_level", params)
def test_dataint_ecc(request, data_width, module_type, test_level):
    """
    Parameterized Hamming ECC test with configurable module type and test level.

    Module type controls which DUT is compiled and tested:
    - encoder: Test only the encoder module (combinational)
    - decoder: Test only the decoder module (sequential)

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # Select DUT and sources based on module_type
    if module_type == 'encoder':
        dut_name = "dataint_ecc_hamming_encode_secded"
        # Get verilog sources and includes from filelist
        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='rtl/common/filelists/dataint_ecc_hamming_encode_secded.f'
        )
    else:  # decoder
        dut_name = "dataint_ecc_hamming_decode_secded"
        # Get verilog sources and includes from filelist
        verilog_sources, includes = get_sources_from_filelist(
            repo_root=repo_root,
            filelist_path='rtl/common/filelists/dataint_ecc_hamming_decode_secded.f'
        )

    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_hamming_{module_type}_w{w_str}_{test_level}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'WIDTH': str(data_width),
        'DEBUG': '1'  # Always enable debug for better failure analysis
    }

    # Adjust timeout based on test level and data width
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    width_factor = max(1.0, data_width / 8.0)  # Larger widths take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor)

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'COCOTB_RESULTS_FILE': results_path,
        'SEED': os.environ.get('SEED', str(random.randint(0, 100000))),
        'TEST_LEVEL': test_level,
        'TEST_WIDTH': str(data_width),
        'TEST_MODULE': module_type,
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    # Verilator --coverage flags when COVERAGE=1, else nothing. Without this
    # the run produces no coverage.dat at all and `make coverage-report`
    # silently reports 0.0% from 0 merged files.
    extra_args.extend(get_coverage_compile_args())

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: {module_type} module, width={data_width}")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # From filelist via get_sources_from_filelist()
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ {test_level.upper()} test PASSED: {module_type} module")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
