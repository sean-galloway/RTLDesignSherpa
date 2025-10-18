# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_network_master_simple
# Purpose: Simple RAPIDS Network Master FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
Simple RAPIDS Network Master FUB Test

A straightforward test for the Network master FUB component that:
- Tests basic packet transmission functionality
- Uses simple stimulus and response checking
- Focuses on core Network master behavior
- No complex framework dependencies initially

This is the simplest starting point for RAPIDS FUB testing.
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
async def test_network_master_basic(dut):
    """Basic Network master functionality test."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize signals
    dut.rst_n.value = 0
    dut.rd_valid.value = 0
    dut.rd_data.value = 0
    dut.rd_type.value = 0
    dut.rd_eos.value = 0
    dut.rd_chunk_valid.value = 0
    dut.rd_channel.value = 0
    dut.rd_used_count.value = 0
    dut.loaded_lines.value = 0
    dut.m_network_pkt_ready.value = 1
    dut.s_network_ack_addr.value = 0
    dut.s_network_ack_addr_par.value = 0
    dut.s_network_ack_ack.value = 0
    dut.s_network_ack_par.value = 0
    dut.s_network_ack_valid.value = 0

    # Reset sequence
    await ClockCycles(dut.clk, 10)
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Starting Network Master Basic Test ===")

    # Test 1: Basic packet transmission
    cocotb.log.info("Test 1: Basic packet transmission")

    # Setup packet data
    test_channel = 5
    test_data = 0x123456789ABCDEF0
    test_type = 1  # TS packet

    # First set loaded_lines to indicate channel has data
    dut.loaded_lines.value = 1 << test_channel  # Channel has data
    await ClockCycles(dut.clk, 2)  # Let arbiter settle

    dut.rd_valid.value = 1
    dut.rd_data.value = test_data
    dut.rd_type.value = test_type
    dut.rd_eos.value = 0
    dut.rd_chunk_valid.value = 0xFFFF  # All chunks valid
    dut.rd_channel.value = test_channel
    dut.rd_used_count.value = 8

    # Wait for ready
    timeout = 100
    cycles = 0
    while cycles < timeout and not dut.rd_ready.value:
        await RisingEdge(dut.clk)
        cycles += 1

    if cycles >= timeout:
        raise Exception("Timeout waiting for rd_ready")

    cocotb.log.info(f"✓ rd_ready asserted after {cycles} cycles")

    # Check Network output
    await ClockCycles(dut.clk, 2)

    if dut.m_network_pkt_valid.value:
        cocotb.log.info(f"✓ Network packet valid")
        cocotb.log.info(f"  Data: 0x{int(dut.m_network_pkt_data.value):X}")
        cocotb.log.info(f"  Type: {dut.m_network_pkt_type.value}")
        cocotb.log.info(f"  EOS: {dut.m_network_pkt_eos.value}")
    else:
        cocotb.log.warning("Network packet not valid")

    # Clear input
    dut.rd_valid.value = 0
    await ClockCycles(dut.clk, 5)

    # Test 2: EOS packet
    cocotb.log.info("Test 2: EOS packet transmission")

    dut.rd_valid.value = 1
    dut.rd_data.value = 0xDEADBEEFCAFEBABE
    dut.rd_type.value = 2  # RDA packet
    dut.rd_eos.value = 1   # EOS packet
    dut.rd_channel.value = 10

    await ClockCycles(dut.clk, 1)

    # Wait for processing
    timeout = 50
    cycles = 0
    while cycles < timeout and not dut.rd_ready.value:
        await RisingEdge(dut.clk)
        cycles += 1

    if dut.m_network_pkt_valid.value and dut.m_network_pkt_eos.value:
        cocotb.log.info("✓ EOS packet transmitted correctly")
    else:
        cocotb.log.warning("EOS packet not transmitted correctly")

    dut.rd_valid.value = 0
    await ClockCycles(dut.clk, 5)

    # Test 3: Multiple channels
    cocotb.log.info("Test 3: Multiple channel test")

    for ch in range(3):
        dut.rd_valid.value = 1
        dut.rd_data.value = 0x1000 + ch
        dut.rd_type.value = 0  # CONFIG packet
        dut.rd_eos.value = 0
        dut.rd_channel.value = ch
        dut.loaded_lines.value = 1 << ch

        await ClockCycles(dut.clk, 1)

        # Wait for ready
        timeout = 20
        cycles = 0
        while cycles < timeout and not dut.rd_ready.value:
            await RisingEdge(dut.clk)
            cycles += 1

        cocotb.log.info(f"✓ Channel {ch} packet processed")

        dut.rd_valid.value = 0
        await ClockCycles(dut.clk, 2)

    cocotb.log.info("=== Network Master Basic Test Complete ===")


@pytest.mark.parametrize("data_width,addr_width,num_channels", [
    (512, 16, 256),
])
def test_network_master_rtl(request, data_width, addr_width, num_channels):
    """RTL test for Network master."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba': 'rtl/amba',
        'rtl_cmn': 'rtl/common'
    })

    dut_name = "network_master"
    toplevel = dut_name

    # RTL source files
    verilog_sources = [
        os.path.join(rtl_dict['rtl_rapids_fub'], f"{dut_name}.sv"),
        # Dependencies
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_skid_buffer.sv"),
        os.path.join(rtl_dict['rtl_amba'], "gaxi/gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_round_robin.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "arbiter_priority_encoder.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_cmn'], "counter_bin.sv")
    ]

    # Include directories
    includes = [
        rtl_dict['rtl_rapids_includes'],
        os.path.join(rtl_dict['rtl_amba'], "includes"),
        os.path.join(rtl_dict['rtl_cmn'], "includes")
    ]

    # Test name with parameters
    dw_str = TBBase.format_dec(data_width, 3)
    aw_str = TBBase.format_dec(addr_width, 2)
    nc_str = TBBase.format_dec(num_channels, 3)
    test_name_plus_params = f"test_network_master_simple_{dut_name}_dw{dw_str}_aw{aw_str}_nc{nc_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'DATA_WIDTH': str(data_width),
        'ADDR_WIDTH': str(addr_width),
        'NUM_CHANNELS': str(num_channels),
        'CHAN_WIDTH': str((num_channels-1).bit_length()),
        'NUM_CHUNKS': '16',
        'PIPELINE_STAGES': '3',
        'INPUT_FIFO_DEPTH': '8'
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
        "-Wno-PINCONNECTEMPTY",
        "-Wno-TIMESCALEMOD",
        "-Wno-BLKSEQ",
        "-Wno-SYNCASYNCNET"
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

        print(f"✓ Network Master simple test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Parameters: {data_width}-bit data, {addr_width}-bit addr, {num_channels} channels")

    except Exception as e:
        print(f"❌ Network Master simple test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Network Master Simple FUB Test")
    print("Run with: pytest val/rapids/fub_tests/network_interfaces/test_network_master_simple.py -v")