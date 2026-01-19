# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_gaxi_drop_fifo_capacity
# Purpose: Simple test to verify basic FIFO capacity (no drop operations).
#
# Documentation: PRD.md
# Subsystem: tests
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple test to verify basic FIFO capacity (no drop operations).

This test isolates the fill/drain behavior to verify:
- FIFO accepts exactly DEPTH writes when full
- Backpressure (wr_ready=0) when capacity reached
- Correct drain behavior
- Count tracking accuracy

REG_LEVEL Control (parameter combinations):
    GATE: 1 test (~2 min) - smoke test (one config)
    FUNC: 2 tests (~5 min) - functional coverage - DEFAULT
    FULL: 4 tests (~12 min) - comprehensive validation

PARAMETER COMBINATIONS:
    GATE: 1 config = 1 test
    FUNC: 2 configs (2 depths) = 2 tests
    FULL: 4 configs (2 depths × 2 modes) = 4 tests

Environment Variables:
    REG_LEVEL: GATE|FUNC|FULL - controls parameter combinations (default: FUNC)
"""

import os
import sys
import pytest
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

# Import testbench class
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../../bin'))
from CocoTBFramework.tbclasses.gaxi.gaxi_drop_fifo_sync_tb import GaxiDropFifoSyncTB
from cocotb_test.simulator import run
from conftest import get_coverage_compile_args
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd


@cocotb.test()
async def capacity_only_cocotb(dut):
    """CocoTB test: FIFO capacity without any drop operations."""
    tb = GaxiDropFifoSyncTB(dut)
    await tb.setup_clocks_and_reset()

    tb.log.info(f"Testing FIFO capacity: depth={tb.depth}")

    # Test 1: Fill to capacity
    tb.log.info("=== Test 1: Fill to full capacity ===")
    success_count = 0

    for i in range(tb.depth + 2):  # Try to write more than capacity
        data = i & ((1 << tb.data_width) - 1)
        success = await tb.write_entry(data, expect_ready=False)

        if success:
            success_count += 1
            tb.log.info(f"Write {i}: SUCCESS, count={tb.get_fifo_count()}")
        else:
            tb.log.info(f"Write {i}: BLOCKED (wr_ready=0), count={tb.get_fifo_count()}")
            break

    final_count = tb.get_fifo_count()
    tb.log.info(f"Total successful writes: {success_count}/{tb.depth}")
    tb.log.info(f"Final FIFO count: {final_count}")

    # Verify capacity
    assert success_count == tb.depth, \
        f"FIFO capacity mismatch: accepted {success_count} writes, expected {tb.depth}"

    # Test 2: Drain and verify
    tb.log.info("=== Test 2: Drain FIFO ===")
    await tb.drain_fifo()

    final_count_after_drain = tb.get_fifo_count()
    tb.log.info(f"Count after drain: {final_count_after_drain}")

    assert final_count_after_drain == 0, \
        f"FIFO not empty after drain: count={final_count_after_drain}"

    tb.log.info("✅ Capacity test PASSED")


def generate_capacity_test_params():
    """
    Generate test parameter combinations based on REG_LEVEL.

    REG_LEVEL=GATE: 1 test (smoke test)
    REG_LEVEL=FUNC: 2 tests (functional coverage) - default
    REG_LEVEL=FULL: 4 tests (comprehensive validation)

    Returns:
        List of tuples: (data_width, depth, registered)
    """
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal - just prove basic capacity works
        return [
            (32, 16, 0),  # mux mode only
        ]

    elif reg_level == 'FUNC':
        # Functional coverage - test two different depths
        return [
            (32, 16, 0),  # Small FIFO
            (32, 64, 0),  # Medium FIFO
        ]

    else:  # FULL
        # Comprehensive - multiple depths and modes
        return [
            (32, 16,  0),  # Small mux
            (32, 16,  1),  # Small flop
            (32, 64,  0),  # Medium mux
            (32, 64,  1),  # Medium flop
        ]


@pytest.mark.parametrize("data_width, depth, registered", generate_capacity_test_params())
def test_gaxi_drop_fifo_capacity(request, data_width, depth, registered):
    """Pytest runner for capacity test with parameterization."""

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "gaxi_drop_fifo_sync"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_amba'], 'gaxi/gaxi_drop_fifo_sync.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin_load.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'fifo_control.sv'),
    ]

    mode_str = 'mux' if registered == 0 else 'flop'
    reg_level = os.environ.get("REG_LEVEL", "FUNC").upper()
    test_name = f"test_{worker_id}_capacity_dw{data_width}_d{depth}_{mode_str}_{reg_level}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    includes=[rtl_dict['rtl_amba_includes']]

    parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': str(registered),
        'ALMOST_WR_MARGIN': '1',
        'ALMOST_RD_MARGIN': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'WAVES': '1',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--Wno-UNOPTFLAT",
    ]

    # Add coverage compile args if COVERAGE=1
    compile_args.extend(get_coverage_compile_args())

    print(f"\n{'='*60}")
    print(f"Testing FIFO Capacity: depth={depth}")
    print(f"Log: {log_path}")
    print(f"Waveform: {sim_build}/dump.vcd")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Use VCD
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ Capacity test PASSED")
    except Exception as e:
        print(f"✗ Capacity test FAILED: {str(e)}")
        print(f"View waveform: gtkwave {sim_build}/dump.vcd")
        raise


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])

    # Get worker ID for parallel execution isolation
    worker_id = os.environ.get('PYTEST_XDIST_WORKER', 'gw0')

    """Pytest runner for capacity test with parameterization."""

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common',
        'rtl_amba_includes': 'rtl/amba/includes',
    })

    dut_name = "gaxi_drop_fifo_sync"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba_includes'], "fifo_defs.svh"),
        os.path.join(rtl_dict['rtl_amba'], 'gaxi/gaxi_drop_fifo_sync.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin_load.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'fifo_control.sv'),
    ]

    mode_str = 'mux' if registered == 0 else 'flop'
    test_name = f"test_{worker_id}_capacity_dw{data_width}_d{depth}_{mode_str}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    includes=[rtl_dict['rtl_amba_includes']]

    parameters = {
        'DATA_WIDTH': str(data_width),
        'DEPTH': str(depth),
        'REGISTERED': str(registered),
        'ALMOST_WR_MARGIN': '1',
        'ALMOST_RD_MARGIN': '1',
    }

    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.vcd",
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'WAVES': '1',
    }

    # VCD waveform generation support via WAVES environment variable
    # Trace compilation always enabled (minimal overhead)
    # Set WAVES=1 to enable VCD dumping for debugging
    compile_args = [
        "--trace",
        "--trace-structs",
        "--Wno-UNOPTFLAT",
    ]

    print(f"\n{'='*60}")
    print(f"Testing FIFO Capacity: depth={depth}")
    print(f"Log: {log_path}")
    print(f"Waveform: {sim_build}/dump.vcd")
    print(f"{'='*60}")

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=dut_name,
            module=module,
            parameters=parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Use VCD
            keep_files=True,
            compile_args=compile_args,
        )
        print(f"✓ Capacity test PASSED")
    except Exception as e:
        print(f"✗ Capacity test FAILED: {str(e)}")
        print(f"View waveform: gtkwave {sim_build}/dump.vcd")
        raise


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])
