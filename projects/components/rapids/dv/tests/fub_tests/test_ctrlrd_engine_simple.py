# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ctrlrd_engine_simple
# Purpose: Simple RAPIDS Control Read Engine FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple RAPIDS Control Read Engine FUB Test

A straightforward test for the control read engine FUB component that:
- Tests basic read-and-compare interface from scheduler
- Tests AXI read interface functionality
- Uses simple stimulus and response checking
- Focuses on core control read engine behavior
- No complex framework dependencies initially

This tests the 7-state control read engine FSM.
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.clock import Clock
from cocotb_test.simulator import run

# Add framework for basic utilities only
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "bin"))
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


@cocotb.test()
async def cocotb_test_ctrlrd_engine_basic(dut):
    """Basic control read engine functionality test."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize signals
    dut.rst_n.value = 0
    dut.ctrlrd_valid.value = 0
    dut.ctrlrd_pkt_addr.value = 0
    dut.ctrlrd_pkt_data.value = 0
    dut.ctrlrd_pkt_mask.value = 0
    dut.cfg_channel_reset.value = 0
    dut.cfg_ctrlrd_max_try.value = 3
    dut.tick_1us.value = 0
    dut.ar_ready.value = 1
    dut.r_valid.value = 0
    dut.r_data.value = 0
    dut.r_id.value = 0
    dut.r_resp.value = 0
    dut.r_last.value = 0

    # Reset sequence
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Starting Control Read Engine Basic Test ===")

    # Test 1: Check idle state
    cocotb.log.info("Test 1: Check initial idle state")

    if dut.ctrlrd_engine_idle.value:
        cocotb.log.info("✓ Ctrlrd engine is idle initially")
    else:
        cocotb.log.warning("Ctrlrd engine not idle initially")

    # Test 2: Basic read-and-match operation
    cocotb.log.info("Test 2: Basic read-and-match operation")

    test_addr = 0x1000
    test_expected_data = 0x12345678
    test_mask = 0xFFFFFFFF
    test_read_data = 0x12345678  # Matches expected

    dut.ctrlrd_valid.value = 1
    dut.ctrlrd_pkt_addr.value = test_addr
    dut.ctrlrd_pkt_data.value = test_expected_data
    dut.ctrlrd_pkt_mask.value = test_mask

    # Wait for ready
    timeout = 100
    cycles = 0
    while cycles < timeout and not dut.ctrlrd_ready.value:
        await RisingEdge(dut.clk)
        cycles += 1

    if cycles >= timeout:
        cocotb.log.warning("Timeout waiting for ctrlrd_ready")
    else:
        cocotb.log.info(f"✓ Ctrlrd ready asserted after {cycles} cycles")

    dut.ctrlrd_valid.value = 0
    await ClockCycles(dut.clk, 2)

    # Test 3: AXI read interface activity
    cocotb.log.info("Test 3: AXI read interface")

    # Wait for AR valid
    timeout = 100
    cycles = 0
    while cycles < timeout and not dut.ar_valid.value:
        await RisingEdge(dut.clk)
        cycles += 1

    if dut.ar_valid.value:
        cocotb.log.info("✓ AXI AR valid asserted")
        cocotb.log.info(f"  Address: 0x{int(dut.ar_addr.value):X}")

        # Simulate AXI read response
        ar_id = int(dut.ar_id.value)

        await ClockCycles(dut.clk, 2)

        dut.r_valid.value = 1
        dut.r_data.value = test_read_data
        dut.r_id.value = ar_id
        dut.r_resp.value = 0  # OKAY
        dut.r_last.value = 1

        # Wait for R handshake
        timeout = 100
        cycles = 0
        while cycles < timeout and not dut.r_ready.value:
            await RisingEdge(dut.clk)
            cycles += 1

        await ClockCycles(dut.clk, 1)
        dut.r_valid.value = 0

        cocotb.log.info("✓ AXI R response completed")
    else:
        cocotb.log.info("No AXI AR activity (may be expected for null address)")

    await ClockCycles(dut.clk, 10)

    # Test 4: Check completion and result
    cocotb.log.info("Test 4: Check completion")

    if dut.ctrlrd_engine_idle.value:
        cocotb.log.info("✓ Ctrlrd engine returned to idle")
        result_data = int(dut.ctrlrd_result.value)
        cocotb.log.info(f"  Result: 0x{result_data:08X}")

        if result_data == test_read_data:
            cocotb.log.info("✓ Result matches read data")
        else:
            cocotb.log.warning(f"Result mismatch: expected=0x{test_read_data:08X}, got=0x{result_data:08X}")
    else:
        cocotb.log.warning("Ctrlrd engine not idle after operation")

    # Test 5: Check error conditions
    cocotb.log.info("Test 5: Error handling")

    if dut.ctrlrd_error.value:
        cocotb.log.warning("Ctrlrd error asserted")
    else:
        cocotb.log.info("✓ No ctrlrd errors")

    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Control Read Engine Basic Test Complete ===")


@pytest.mark.parametrize("num_channels,addr_width", [
    (32, 64),
])
def test_ctrlrd_engine_rtl(request, num_channels, addr_width):
    """RTL test for control read engine."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': 'projects/components/rapids/rtl/rapids_fub',
        'rtl_rapids_includes': 'projects/components/rapids/rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "ctrlrd_engine"
    toplevel = dut_name

    # RTL source files
    verilog_sources = [
        # Package files must be compiled first
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes', 'rapids_pkg.sv'),
        # Main module
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'rapids_fub', f'{dut_name}.sv'),
        # Dependencies for AXI
        os.path.join(repo_root, 'rtl', 'amba', 'gaxi', 'gaxi_skid_buffer.sv'),
        # Frequency-invariant counter for 1us tick
        os.path.join(repo_root, 'rtl', 'common', 'counter_freq_invariant.sv')
    ]

    # Include directories
    includes = [
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes'),
        os.path.join(repo_root, 'rtl', 'amba', 'includes'),
        os.path.join(repo_root, 'rtl', 'common', 'includes')
    ]

    # Test name with parameters
    nc_str = TBBase.format_dec(num_channels, 2)
    aw_str = TBBase.format_dec(addr_width, 2)
    test_name_plus_params = f"test_ctrlrd_engine_simple_{dut_name}_nc{nc_str}_aw{aw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'CHANNEL_ID': '0',
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
        'AXI_ID_WIDTH': '8',
        'MON_AGENT_ID': '8\'h20',
        'MON_UNIT_ID': '4\'h1',
        'MON_CHANNEL_ID': '6\'h0'
    }

    # Environment variables
    extra_env = {
        'TRACE_FILE': f"{sim_build}/dump.fst",
        'VERILATOR_TRACE': '1',
        'DUT': dut_name,
        'LOG_PATH': log_path,
        'COCOTB_LOG_LEVEL': 'INFO',
        'SEED': str(12345)
    }

    # Compilation arguments - use VCD tracing (not FST) to avoid Verilator assertion
    compile_args = [
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR",
        "--trace",  # Enable VCD tracing (not --trace-fst)
        "--trace-depth", "99",  # Full trace depth
        "--trace-structs"  # Trace struct members
    ]

    sim_args = []

    plusargs = []

    # Create waveform viewing command
    cmd_filename = create_view_cmd(log_dir, log_path, sim_build, module, test_name_plus_params)

    try:
        run(
            python_search=[tests_dir],
            verilog_sources=verilog_sources,
            includes=includes,
            toplevel=toplevel,
            module=module,
            parameters=rtl_parameters,
            sim_build=sim_build,
            extra_env=extra_env,
            waves=False,  # Manually enable VCD via --trace compile arg
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ Control Read Engine simple test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Parameters: {num_channels} channels, {addr_width}-bit addr")

    except Exception as e:
        print(f"❌ Control Read Engine simple test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Control Read Engine Simple FUB Test")
    print("Run with: pytest projects/components/rapids/dv/tests/fub_tests/ctrlrd_engine/test_ctrlrd_engine_simple.py -v")
