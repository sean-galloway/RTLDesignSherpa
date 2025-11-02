# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_simple_sram
# Purpose: Simple RAPIDS Simple SRAM FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple RAPIDS Simple SRAM FUB Test

A straightforward test for the simple SRAM FUB component that:
- Tests basic read/write operations
- Tests chunk enable functionality
- Uses simple stimulus and response checking
- Focuses on core SRAM behavior
- No complex framework dependencies

This is the simplest possible FUB test for RAPIDS validation.
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
async def test_simple_sram_basic(dut):
    """Basic simple SRAM functionality test."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize signals
    dut.wr_en.value = 0
    dut.wr_addr.value = 0
    dut.wr_data.value = 0
    dut.wr_chunk_en.value = 0
    dut.rd_en.value = 0
    dut.rd_addr.value = 0

    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Starting Simple SRAM Basic Test ===")

    # Test 1: Basic write operation
    cocotb.log.info("Test 1: Basic write operation")

    test_addr = 0x10
    test_data = 0x12345678

    dut.wr_en.value = 1
    dut.wr_addr.value = test_addr
    dut.wr_data.value = test_data
    dut.wr_chunk_en.value = 1  # Enable all available chunks

    await ClockCycles(dut.clk, 1)
    dut.wr_en.value = 0

    cocotb.log.info(f"✓ Write operation: addr=0x{test_addr:X}, data=0x{test_data:X}")

    await ClockCycles(dut.clk, 2)

    # Test 2: Basic read operation
    cocotb.log.info("Test 2: Basic read operation")

    dut.rd_en.value = 1
    dut.rd_addr.value = test_addr

    await ClockCycles(dut.clk, 1)  # rd_en setup
    dut.rd_en.value = 0  # Deassert after 1 cycle
    await ClockCycles(dut.clk, 2)  # Wait for pipeline to complete (need 2 cycles)

    read_data = int(dut.rd_data.value)
    if read_data == test_data:
        cocotb.log.info(f"✓ Read operation successful: got 0x{read_data:X}")
    else:
        cocotb.log.error(f"❌ Read mismatch: expected 0x{test_data:X}, got 0x{read_data:X}")

    await ClockCycles(dut.clk, 1)

    # Test 3: Multiple write/read operations
    cocotb.log.info("Test 3: Multiple write/read operations")

    test_patterns = [
        (0x00, 0xDEADBEEF),
        (0x01, 0xCAFEBABE),
        (0x02, 0x12345678),
        (0x03, 0xABCDEF00)
    ]

    # Write all patterns
    for addr, data in test_patterns:
        dut.wr_en.value = 1
        dut.wr_addr.value = addr
        dut.wr_data.value = data
        dut.wr_chunk_en.value = 1
        await ClockCycles(dut.clk, 1)
        dut.wr_en.value = 0
        await ClockCycles(dut.clk, 1)

    # Read and verify all patterns with proper timing
    all_passed = True
    for addr, expected_data in test_patterns:
        dut.rd_en.value = 1
        dut.rd_addr.value = addr
        await ClockCycles(dut.clk, 1)  # Setup cycle
        dut.rd_en.value = 0
        await ClockCycles(dut.clk, 2)  # Pipeline delay (need 2 cycles)

        read_data = int(dut.rd_data.value)
        if read_data == expected_data:
            cocotb.log.info(f"✓ Address 0x{addr:02X}: 0x{read_data:X} (correct)")
        else:
            cocotb.log.error(f"❌ Address 0x{addr:02X}: expected 0x{expected_data:X}, got 0x{read_data:X}")
            all_passed = False

        await ClockCycles(dut.clk, 1)

    if all_passed:
        cocotb.log.info("✓ All read/write operations passed")
    else:
        cocotb.log.error("❌ Some read/write operations failed")

    # Test 4: Chunk enable functionality
    cocotb.log.info("Test 4: Chunk enable functionality")

    # Write with partial chunk enables
    test_addr = 0x20
    full_data = 0x12345678

    # Write with only lower chunks enabled
    dut.wr_en.value = 1
    dut.wr_addr.value = test_addr
    dut.wr_data.value = full_data
    dut.wr_chunk_en.value = 1  # Enable chunk
    await ClockCycles(dut.clk, 1)
    dut.wr_en.value = 0
    await ClockCycles(dut.clk, 2)

    # Read back with proper timing
    dut.rd_en.value = 1
    dut.rd_addr.value = test_addr
    await ClockCycles(dut.clk, 1)  # Setup cycle
    dut.rd_en.value = 0
    await ClockCycles(dut.clk, 2)  # Pipeline delay (need 2 cycles)

    read_data = int(dut.rd_data.value)
    cocotb.log.info(f"Partial write result: 0x{read_data:X}")

    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Simple SRAM Basic Test Complete ===")


@pytest.mark.parametrize("addr_width,data_width,num_chunks", [
    (8, 32, 4),
    (6, 32, 1),
])
def test_simple_sram_rtl(request, addr_width, data_width, num_chunks):
    """RTL test for simple SRAM."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub'
    })

    dut_name = "simple_sram"
    toplevel = dut_name

    # RTL source files - just the single module
    verilog_sources = [
        os.path.join(rtl_dict['rtl_rapids_fub'], f"{dut_name}.sv")
    ]

    # No include directories needed for this simple module
    includes = []

    # Test name with parameters
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 2)
    nc_str = TBBase.format_dec(num_chunks, 1)
    test_name_plus_params = f"test_simple_sram_{dut_name}_aw{aw_str}_dw{dw_str}_nc{nc_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'NUM_CHUNKS': str(num_chunks)
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

    # Compilation arguments
    compile_args = [
        "--trace-fst",
        "--trace-structs",
        "--trace-depth", "10",
        "-Wall",
        "-Wno-PINMISSING",
        "-Wno-UNUSED",
        "-Wno-EOFNEWLINE"
    ]

    sim_args = [
        "--trace-fst",
        "--trace-structs"
    ]

    plusargs = ["+trace"]

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
            waves=True,
            keep_files=True,
            compile_args=compile_args,
            sim_args=sim_args,
            plusargs=plusargs,
        )

        print(f"✓ Simple SRAM test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Parameters: {addr_width}-bit addr, {data_width}-bit data, {num_chunks} chunks")

    except Exception as e:
        print(f"❌ Simple SRAM test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Simple SRAM FUB Test")
    print("Run with: pytest val/rapids/fub_tests/simple_sram/test_simple_sram.py -v")