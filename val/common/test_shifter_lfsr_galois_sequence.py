# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: SimpleLFSRTB
# Purpose: Get a prime number for the given bit width from lookup table
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

import os
import sys
import random
import pytest
import cocotb
from cocotb_test.simulator import run

# Add repo root to path for CocoTBFramework imports
from TBClasses.shared.tbbase import TBBase
from TBClasses.common.shifter_lfsr_galois_sequence_tb import SimpleLFSRTB
from TBClasses.shared.filelist_utils import get_sources_from_filelist
from TBClasses.shared.utilities import get_paths, create_view_cmd

# Prime lookup table for different bit widths


# LFSR parameters from the PDF table - using 4-tap configurations


@cocotb.test(timeout_time=10000, timeout_unit="us")
async def simple_generate_test(dut):
    """Simple test to generate LFSR values"""
    tb = SimpleLFSRTB(dut)
    
    # Start clock
    await tb.start_clock('clk', 10, 'ns')
    
    # Generate values
    values = await tb.generate_values()
    
    # Count first -- tautological on its own (the loop appends exactly COUNT
    # times), but it guards the comparison below against a short read.
    expected_count = tb.COUNT
    assert len(values) == expected_count, f"Expected {expected_count} values, got {len(values)}"

    # The real check. Until this existed the test generated a hex list, wrote
    # it to a file nobody reads, and asserted only that it had generated as
    # many values as it had been asked to generate -- so any LFSR output at
    # all, including a stuck-at-zero register, passed.
    expected = tb.reference_values(expected_count)
    mismatches = [(i, v, e) for i, (v, e) in enumerate(zip(values, expected)) if v != e]
    if mismatches:
        for i, v, e in mismatches[:8]:
            tb.log.error(f"LFSR mismatch at index {i}: actual=0x{v:x} expected=0x{e:x}")
    assert not mismatches, (
        f"{len(mismatches)}/{expected_count} generated values disagree with the "
        f"Galois reference (seed=0x{tb.config['seed']:x}, taps={tb.config['taps']}); "
        f"first: index {mismatches[0][0]} actual=0x{mismatches[0][1]:x} "
        f"expected=0x{mismatches[0][2]:x}")
    tb.log.info(f"All {expected_count} values match the Galois reference")

def generate_test_params():
    """
    Generate test parameters based on REG_LEVEL.

    REG_LEVEL=GATE: 2 tests (8, 16-bit)
    REG_LEVEL=FUNC: 4 tests (8, 16, 32, 64-bit) - default
    REG_LEVEL=FULL: 7 tests (all widths up to 512-bit)

    Returns:
        List of dicts with WIDTH, COUNT
    """
    import os
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
        ]
    elif reg_level == 'FUNC':
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
            {'WIDTH': 32, 'COUNT': 50},
            {'WIDTH': 64, 'COUNT': 50},
        ]
    else:  # FULL
        return [
            {'WIDTH': 8, 'COUNT': 100},
            {'WIDTH': 16, 'COUNT': 100},
            {'WIDTH': 32, 'COUNT': 50},
            {'WIDTH': 64, 'COUNT': 50},
            {'WIDTH': 128, 'COUNT': 25},
            {'WIDTH': 256, 'COUNT': 25},
            {'WIDTH': 512, 'COUNT': 10},
        ]

@pytest.mark.parametrize("params", generate_test_params())
def test_shifter_lfsr_galois_sequence(request, params):
    """Parameterized test for different LFSR widths"""
    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({'rtl_cmn': 'rtl/common', 'rtl_amba_includes': 'rtl/amba/includes'})
    
    dut_name = "shifter_lfsr_galois"
    toplevel = dut_name
    
    # Get verilog sources and includes from filelist
    verilog_sources, includes = get_sources_from_filelist(
        repo_root=repo_root,
        filelist_path='rtl/common/filelists/shifter_lfsr_galois.f'
    )
    
    # Test name
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"simple_lfsr_W{params['WIDTH']}_C{params['COUNT']}_{reg_level}"

    # Handle pytest-xdist parallel execution
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', '')
    if worker_id:
        test_name = f"{test_name}_{worker_id}"

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    log_path = os.path.join(log_dir, f'{test_name}.log')
    
    enable_waves = bool(int(os.environ.get('WAVES', '0')))
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)
    
    # Module parameters - fixed for 4-tap configuration
    parameters = {
        'WIDTH': params['WIDTH'],
        'TAP_INDEX_WIDTH': 12,
        'TAP_COUNT': 4
    }
    
    # Environment variables
    extra_env = {
        # Depth knob. Without this the TB reads TEST_LEVEL's default on every
        # run, so its gate/func/full branches are unreachable no matter what
        # REG_LEVEL selects ([[test-runner]]: both mechanisms are required,
        # and a mechanism nothing exports is not one).
        'TEST_LEVEL': reg_level.lower(),
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'TEST_WIDTH': str(params['WIDTH']),
        'TEST_COUNT': str(params['COUNT'])
    }
    
    extra_args = [
        '--trace-fst',
        '--trace-structs',
        '-Wno-TIMESCALEMOD',
    ]

    sim_args = ['--trace'] if enable_waves else []

    if enable_waves:
        extra_env['COCOTB_TRACE_FILE'] = os.path.join(sim_build, 'dump.fst')

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            toplevel=toplevel,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            extra_args=extra_args,
            plus_args=sim_args,

            waves=enable_waves,
            includes=includes,  # From filelist via get_sources_from_filelist()
        )
    except Exception as e:
        print(f"Test failed: {str(e)}")
        print(f"Logs at: {log_path}")
        raise
