# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ClockDividerTB
# Purpose: Clock Divider Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Clock Divider Test with Parameterized Test Levels and Configuration

This test uses N, PO_WIDTH, COUNTER_WIDTH and test_level as parameters for maximum flexibility:

CONFIGURATION:
    N:              Number of output clocks (1, 2, 4, 8)
    PO_WIDTH:       Width of pickoff point registers (4, 6, 8)
    COUNTER_WIDTH:  Width of the counter (16, 32, 64)

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - N: [1, 2, 4, 8]
    - PO_WIDTH: [4, 6, 8]
    - COUNTER_WIDTH: [16, 32, 64]
    - test_level: [gate, func, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_N: Number of output clocks
    TEST_PO_WIDTH: Width of pickoff point registers
    TEST_COUNTER_WIDTH: Width of the counter
"""

import os
import sys
import random
import math
from itertools import product
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer, FallingEdge
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.clock_divider_tb import ClockDividerTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd, sim_build_path
from cov_utils.conftest_coverage import get_coverage_compile_args


@cocotb.test(timeout_time=20000, timeout_unit="us")
async def clock_divider_test(dut):
    """Test for Clock Divider module"""
    tb = ClockDividerTB(dut)

    # Start clock
    clock_thread = cocotb.start_soon(tb.clock_gen(tb.clk, 10, 'ns'))

    # Run tests
    passed = await tb.run_all_tests()

    # Stop clock
    clock_thread.kill()

    # Report final result
    tb.log.info(f"CLOCK_DIVIDER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Clock Divider test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 3 tests (quick smoke at gate level)
    REG_LEVEL=FUNC: ~12 tests (all valid configs, gate level) - default
    REG_LEVEL=FULL: ~36 tests (all valid configs, all levels)

    Returns:
        List of tuples: (n, po_width, counter_width, test_level)

    RTL Constraint: PO_WIDTH > $clog2(COUNTER_WIDTH) to avoid truncation
                    Equivalently: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)
                    This ensures PO_WIDTH can hold the value COUNTER_WIDTH

    Examples:
        COUNTER_WIDTH=16 → needs PO_WIDTH >= 5 (since $clog2(16)=4, $clog2(17)=5)
        COUNTER_WIDTH=32 → needs PO_WIDTH >= 6 (since $clog2(32)=5, $clog2(33)=6)
        COUNTER_WIDTH=64 → needs PO_WIDTH >= 7 (since $clog2(64)=6, $clog2(65)=7)
    """
    import math
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    n_values = [1, 2, 4, 8]           # Number of output clocks
    po_width_values = [4, 6, 8]       # Width of pickoff registers
    counter_width_values = [16, 32, 64]  # Width of counter
    test_levels = ['gate', 'func', 'full']

    # Generate valid combinations respecting RTL constraint
    valid_configs = []
    for n, po_width, counter_width in product(n_values, po_width_values, counter_width_values):
        # RTL constraint: PO_WIDTH > $clog2(COUNTER_WIDTH)
        # Equivalently: PO_WIDTH >= $clog2(COUNTER_WIDTH + 1)
        # This prevents truncation when comparing w_pickoff_raw < w_counter_width_sized
        min_po_width = math.ceil(math.log2(counter_width + 1))
        if po_width >= min_po_width:
            valid_configs.append((n, po_width, counter_width))

    if reg_level == 'GATE':
        # Quick smoke test: 3 different configs at gate level
        return [(valid_configs[0] + ('gate',)),
                (valid_configs[len(valid_configs)//2] + ('gate',)),
                (valid_configs[-1] + ('gate',))]

    elif reg_level == 'FUNC':
        # All valid configs at gate level only
        return [(n, po, cw, 'gate') for n, po, cw in valid_configs]

    else:  # FULL
        # All valid configs at all test levels
        return [(n, po, cw, level)
                for n, po, cw in valid_configs
                for level in test_levels]

params = generate_params()

@pytest.mark.parametrize("n, po_width, counter_width, test_level", params)
def test_clock_divider(request, n, po_width, counter_width, test_level):
    """
    Parameterized Clock Divider test with configurable parameters and test level.

    N controls the number of divided clock outputs.
    PO_WIDTH controls the width of pickoff point configuration.
    COUNTER_WIDTH controls the width of the internal counter.
    Test level controls the depth and breadth of testing.
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "clock_divider"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/clock_divider.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    n_str = TBBase.format_dec(n, 1)
    po_str = TBBase.format_dec(po_width, 1)
    cw_str = TBBase.format_dec(counter_width, 2)
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name_plus_params = f"test_clock_divider_n{n_str}_po{po_str}_cw{cw_str}_{test_level}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name_plus_params = f"{test_name_plus_params}_{worker_id}"

    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    # Setup directories
    sim_build = sim_build_path(tests_dir, test_name_plus_params)
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    results_path = os.path.join(log_dir, f'results_{test_name_plus_params}.xml')

    # RTL parameters
    parameters = {
        'N': str(n),
        'PO_WIDTH': str(po_width),
        'COUNTER_WIDTH': str(counter_width)
    }

    # Adjust timeout based on test level and parameters
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    param_factor = max(1.0, (n * counter_width) / 128.0)  # More complex configs take more time
    base_timeout = 2000  # 2 seconds base
    timeout_ms = int(base_timeout * timeout_multipliers.get(test_level, 1) * param_factor)

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
        'TEST_N': str(n),
        'TEST_PO_WIDTH': str(po_width),
        'TEST_COUNTER_WIDTH': str(counter_width),
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
    print(f"Running {test_level.upper()} test: N={n}, PO_WIDTH={po_width}, COUNTER_WIDTH={counter_width}")
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
        print(f"✓ {test_level.upper()} test PASSED: N={n}, PO_WIDTH={po_width}, COUNTER_WIDTH={counter_width}")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
