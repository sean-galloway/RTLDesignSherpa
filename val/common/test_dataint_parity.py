# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ParityTB
# Purpose: Generic Parity Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Parity Test with Parameterized Test Levels and Configuration

This test uses chunks, width, parity_type and test_level as parameters for maximum flexibility:

CONFIGURATION:
    chunks:      Number of parity chunks (1, 2, 4, 8)
    width:       Total data width (8, 16, 32, 64)
    parity_type: Even (1) or Odd (0) parity

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - chunks: [1, 2, 4, 8]
    - width: [8, 16, 32, 64]
    - parity_type: [0, 1] (odd, even)
    - test_level: [gate, func, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_WIDTH: Data width for parity calculation
    TEST_CHUNKS: Number of parity chunks
    TEST_PARITY_TYPE: Parity type (0=odd, 1=even)
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
from TBClasses.common.dataint_parity_tb import ParityTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def parity_test(dut):
    """Test for Generic Parity module"""
    tb = ParityTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"PARITY test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Parity test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 4 tests (16/32-bit, 1/2 chunks, even parity, gate)
    REG_LEVEL=FUNC: ~20 tests (varied configs, gate) - default
    REG_LEVEL=FULL: ~60 tests (all valid combinations, all levels)

    Returns:
        List of tuples: (data_width, chunks, parity_type, test_level)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    widths = [8, 16, 32, 64]      # Different data widths
    chunks_list = [1, 2, 4, 8]    # Different chunk counts
    parity_types = [0, 1]         # Odd and Even parity
    test_levels = ['gate', 'func', 'full']

    if reg_level == 'GATE':
        # Quick smoke test: 16/32-bit, simple chunks, even parity, gate
        return [
            (16, 1, 1, 'gate'),
            (16, 2, 1, 'gate'),
            (32, 1, 1, 'gate'),
            (32, 2, 1, 'gate'),
        ]

    elif reg_level == 'FUNC':
        # Functional coverage: varied configs, gate level, even parity only
        valid_params = []
        for width, chunks in product(widths, chunks_list):
            if chunks <= width:
                valid_params.append((width, chunks, 1, 'gate'))  # even parity only
        return valid_params

    else:  # FULL
        # Comprehensive: all valid combinations
        valid_params = []
        for width, chunks, parity_type, test_level in product(widths, chunks_list, parity_types, test_levels):
            if chunks <= width:
                valid_params.append((width, chunks, parity_type, test_level))
        return valid_params

params = generate_params()

@pytest.mark.parametrize("data_width, chunks, parity_type, test_level", params)
def test_dataint_parity(request, data_width, chunks, parity_type, test_level):
    """
    Parameterized Generic Parity test with configurable chunks, width, parity type and test level.

    Chunks controls how many parity bits are calculated in parallel:
    - 1: Single parity bit for entire data width
    - 2, 4, 8: Multiple parity bits for data chunks

    Parity type controls even vs odd parity:
    - 0: Odd parity (XOR + 1)
    - 1: Even parity (XOR)

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "dataint_parity"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/dataint_parity.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    w_str = TBBase.format_dec(data_width, 2)
    c_str = TBBase.format_dec(chunks, 1)
    p_str = "even" if parity_type else "odd"
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_parity_w{w_str}_c{c_str}_{p_str}_{test_level}_{reg_level}"

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
        'CHUNKS': str(chunks)
    }

    # Adjust timeout based on test level and data width
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    width_factor = max(1.0, data_width / 32.0)  # Larger widths take more time
    chunks_factor = max(1.0, chunks / 4.0)      # More chunks take more time
    base_timeout = 1500  # 1.5 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * width_factor * chunks_factor)

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
        'TEST_CHUNKS': str(chunks),
        'TEST_PARITY_TYPE': str(parity_type),
        'TEST_DEBUG': '1',
        'COCOTB_TEST_TIMEOUT': str(timeout_ms)
    }

    # Add coverage compile args if COVERAGE=1
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    print(f"\n{'='*60}")
    print(f"Running {test_level.upper()} test: {chunks} chunks, width={data_width}, {p_str} parity")
    print(f"Expected duration: {timeout_ms/1000:.1f}s")
    print(f"Log: {log_path}")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,  # from the filelist; was [] and dropped +incdir
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
        )
        print(f"✓ {test_level.upper()} test PASSED: {chunks} chunks, {p_str} parity")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
