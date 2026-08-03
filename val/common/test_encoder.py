# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: EncoderTB
# Purpose: Generic Encoder Test with Parameterized Test Levels and Configuration
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Generic Encoder Test with Parameterized Test Levels and Configuration

This test uses input_width and test_level as parameters for maximum flexibility:

CONFIGURATION:
    input_width: Number of input bits (4, 8, 16, 32)
    output_width: Number of output bits (log2(input_width))

TEST LEVELS:
    gate (1-2 min):   Quick verification during development
    func (3-5 min):  Integration testing for CI/branches
    full (8-15 min):   Comprehensive validation for regression

PARAMETER COMBINATIONS:
    - input_width: [4, 8, 16, 32]
    - test_level: [gate, func, full]

Environment Variables:
    TEST_LEVEL: Set test level in cocotb (gate/func/full)
    SEED: Set random seed for reproducibility
    TEST_INPUT_WIDTH: Input width for encoder

COVERAGE STRATEGY:
    The encoder RTL uses a for loop with a conditional:
        for (int i = 0; i < N; i++) begin
            if (decoded[i]) data = $clog2(N)'(i);
        end

    Verilator unrolls this and creates 2*N branches (TRUE/FALSE for each bit).
    For 100% coverage, we must exercise BOTH branches for EACH bit position:

    1. test_zero_input: All bits FALSE (covers all FALSE branches simultaneously)
    2. test_one_hot_encoding: Each bit TRUE individually (covers TRUE branch per bit)
    3. test_walking_patterns:
       - Walking ones: Redundant with one_hot but good for verification
       - Walking zeros: Each bit FALSE while others TRUE (critical for coverage!)
    4. test_priority_encoding: Multiple bits TRUE (priority logic verification)
    5. test_boundary_conditions: Edge cases (LSB, MSB, all bits, etc.)

    The walking zeros test is CRITICAL for coverage because it ensures that
    when a bit[i] is FALSE (while others are TRUE), the encoder correctly
    skips that bit and finds the highest remaining bit.
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
from TBClasses.common.encoder_tb import EncoderTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def encoder_test(dut):
    """Test for Generic Encoder module"""
    tb = EncoderTB(dut)

    # Run tests
    passed = await tb.run_all_tests()

    # Report final result
    tb.log.info(f"ENCODER test {'PASSED' if passed else 'FAILED'} at level {tb.TEST_LEVEL.upper()}")

    # Assert on failure
    assert passed, f"Encoder test FAILED - {len(tb.test_failures)} failures detected"

    return passed

def generate_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # GATE: Minimal - just 4-bit
        input_widths = [4]
        test_levels = ['full']
    elif reg_level == 'FUNC':
        # FUNC: Small and medium widths
        input_widths = [4, 8]
        test_levels = ['full']
    else:  # FULL
        # FULL: All widths
        input_widths = [4, 8, 16, 32]
        test_levels = ['full']

    return [(width, level) for width, level in product(input_widths, test_levels)]

params = generate_params()

@pytest.mark.parametrize("input_width, test_level", params)
def test_encoder(request, input_width, test_level):
    """
    Parameterized Generic Encoder test with configurable input width and test level.

    Input width controls the size of the encoder:
    - 4: 4-to-2 encoder
    - 8: 8-to-3 encoder
    - 16: 16-to-4 encoder
    - 32: 32-to-5 encoder

    Test level controls the depth and breadth of testing:
    - gate: Quick verification (1-2 min)
    - func: Integration testing (3-5 min)
    - full: Comprehensive validation (8-15 min)
    """
    # Get directory and module information
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})

    # DUT information
    dut_name = "encoder"
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/encoder.f'
    )
    toplevel = dut_name

    # Create human-readable test identifier
    output_width = int(math.log2(input_width))
    # Get REG_LEVEL before creating test name
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()  # GATE, FUNC, or FULL

    test_name_plus_params = f"test_encoder_{input_width}to{output_width}_{test_level}_{reg_level}"

    # Add worker ID for pytest-xdist parallel execution
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
        'N': str(input_width)
    }

    # Adjust timeout based on test level and input width
    timeout_multipliers = {'gate': 1, 'func': 2, 'full': 4}
    width_factor = max(1.0, input_width / 16.0)  # Larger inputs take more time
    base_timeout = 1000  # 1 second base
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
        'TEST_INPUT_WIDTH': str(input_width),
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
    print(f"Running {test_level.upper()} test: {input_width}-to-{output_width} encoder")
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
        print(f"✓ {test_level.upper()} test PASSED: {input_width}-to-{output_width} encoder")
    except Exception as e:
        print(f"✗ {test_level.upper()} test FAILED: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view the waveforms run: {cmd_filename}")
        raise
