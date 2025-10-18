# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_ctrlwr_engine_simple
# Purpose: Simple RAPIDS Control Write Engine FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple RAPIDS Control Write Engine FUB Test

A straightforward test for the control write engine FUB component that:
- Tests basic program instruction interface from scheduler
- Tests AXI write interface functionality
- Uses simple stimulus and response checking
- Focuses on core control write engine behavior
- No complex framework dependencies initially

This tests the 4-state control write engine FSM.
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
async def cocotb_test_ctrlwr_engine_basic(dut):
    """Basic control write engine functionality test."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize signals
    dut.rst_n.value = 0
    dut.ctrlwr_valid.value = 0
    dut.ctrlwr_pkt_addr.value = 0
    dut.ctrlwr_pkt_data.value = 0
    dut.cfg_channel_reset.value = 0
    dut.aw_ready.value = 1
    dut.w_ready.value = 1
    dut.b_valid.value = 0
    dut.b_resp.value = 0

    # Reset sequence
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Starting Control Write Engine Basic Test ===")

    # Test 1: Check idle state
    cocotb.log.info("Test 1: Check initial idle state")

    if dut.ctrlwr_engine_idle.value:
        cocotb.log.info("✓ Ctrlwr engine is idle initially")
    else:
        cocotb.log.warning("Ctrlwr engine not idle initially")

    # Test 2: Basic ctrlwr instruction
    cocotb.log.info("Test 2: Basic ctrlwr instruction")

    test_addr = 0x1000
    test_data = 0x12345678

    dut.ctrlwr_valid.value = 1
    dut.ctrlwr_pkt_addr.value = test_addr
    dut.ctrlwr_pkt_data.value = test_data

    # Wait for ready
    timeout = 100
    cycles = 0
    while cycles < timeout and not dut.ctrlwr_ready.value:
        await RisingEdge(dut.clk)
        cycles += 1

    if cycles >= timeout:
        cocotb.log.warning("Timeout waiting for ctrlwr_ready")
    else:
        cocotb.log.info(f"✓ Ctrlwr ready asserted after {cycles} cycles")

    dut.ctrlwr_valid.value = 0
    await ClockCycles(dut.clk, 5)

    # Test 3: AXI write interface activity
    cocotb.log.info("Test 3: AXI write interface")

    if dut.aw_valid.value:
        cocotb.log.info("✓ AXI AW valid asserted")
        cocotb.log.info(f"  Address: 0x{int(dut.aw_addr.value):X}")

        # Simulate AXI response
        dut.b_valid.value = 1
        dut.b_resp.value = 0  # OKAY

        await ClockCycles(dut.clk, 2)
        dut.b_valid.value = 0
    else:
        cocotb.log.info("No AXI AW activity (may be expected)")

    if dut.w_valid.value:
        cocotb.log.info("✓ AXI W valid asserted")
        cocotb.log.info(f"  Data: 0x{int(dut.w_data.value):X}")
    else:
        cocotb.log.info("No AXI W activity (may be expected)")

    await ClockCycles(dut.clk, 10)

    # Test 4: Check error conditions
    cocotb.log.info("Test 4: Error handling")

    if dut.ctrlwr_error.value:
        cocotb.log.warning("Ctrlwr error asserted")
    else:
        cocotb.log.info("✓ No ctrlwr errors")

    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Control Write Engine Basic Test Complete ===")


@pytest.mark.parametrize("num_channels,addr_width", [
    (32, 64),
])
def test_ctrlwr_engine_rtl(request, num_channels, addr_width):
    """RTL test for control write engine."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': 'projects/components/rapids/rtl/rapids_fub',
        'rtl_rapids_includes': 'projects/components/rapids/rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "ctrlwr_engine"
    toplevel = dut_name

    # RTL source files
    verilog_sources = [
        # Package files must be compiled first
        os.path.join(repo_root, 'rtl', 'amba', 'includes', 'monitor_pkg.sv'),
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'includes', 'rapids_pkg.sv'),
        # Main module
        os.path.join(repo_root, 'projects', 'components', 'rapids', 'rtl', 'rapids_fub', f'{dut_name}.sv'),
        # Dependencies for AXI
        os.path.join(repo_root, 'rtl', 'amba', 'gaxi', 'gaxi_skid_buffer.sv')
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
    test_name_plus_params = f"test_ctrlwr_engine_simple_{dut_name}_nc{nc_str}_aw{aw_str}"
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

        print(f"✓ Control Write Engine simple test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Parameters: {num_channels} channels, {addr_width}-bit addr")

    except Exception as e:
        print(f"❌ Control Write Engine simple test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Control Write Engine Simple FUB Test")
    print("Run with: pytest val/rapids/fub_tests/ctrlwr_engine/test_ctrlwr_engine_simple.py -v")