"""
Simple test to verify basic FIFO capacity (no drop operations).

This test isolates the fill/drain behavior to identify the capacity bug.
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


def test_gaxi_drop_fifo_capacity():
    """Pytest runner for capacity test."""

    # Get paths
    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    # Test parameters
    data_width = 32
    depth = 16
    registered = 0

    dut_name = "gaxi_drop_fifo_sync"
    verilog_sources = [
        os.path.join(rtl_dict['rtl_amba'], 'gaxi/gaxi_drop_fifo_sync.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'counter_bin_load.sv'),
        os.path.join(rtl_dict['rtl_cmn'], 'fifo_control.sv'),
    ]

    test_name = f"test_capacity_dw{data_width}_d{depth}"
    log_path = os.path.join(log_dir, f'{test_name}.log')
    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

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
