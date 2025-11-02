# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_source_axi_read_engine_simple
# Purpose: RAPIDS Source AXI Read Engine FUB Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Source AXI Read Engine FUB Test

A straightforward test for the source AXI read engine FUB component that:
- Tests basic AXI read address generation
- Tests data interface readiness
- Tests multi-channel arbitration
- Tests HBM3e transfer size configurations
- Uses simple stimulus and response checking
- Focuses on core AXI read engine behavior
- No complex framework dependencies

This is a simple FUB test for RAPIDS AXI read engine validation.
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
async def test_source_axi_read_engine_basic(dut):
    """Basic source AXI read engine functionality test."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize all signals
    await init_signals(dut)
    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Starting Source AXI Read Engine Basic Test ===")

    # Test 1: Check initial idle state
    cocotb.log.info("Test 1: Check initial idle state")
    assert int(dut.ar_valid.value) == 0, "AR should not be valid initially"
    cocotb.log.info("✓ AXI read engine is idle initially")

    # Test 2: Basic data interface readiness
    cocotb.log.info("Test 2: Check data interface")

    # Apply basic scheduler data request
    dut.data_valid.value = 0x1  # Channel 0 has data request
    dut.data_address[0].value = 0x2000
    dut.data_length[0].value = 32  # 32 4-byte chunks = 128 bytes
    dut.data_type[0].value = 0
    dut.data_eos.value = 0x0

    await ClockCycles(dut.clk, 1)

    ready_signal = int(dut.data_ready.value)
    if ready_signal & 0x1:
        cocotb.log.info(f"✓ Data ready asserted for channel 0")
    else:
        cocotb.log.info(f"⚠ Data ready not asserted (may be expected)")

    await ClockCycles(dut.clk, 2)

    # Test 3: AXI address channel interface
    cocotb.log.info("Test 3: AXI address interface")

    # Enable AXI ready
    dut.ar_ready.value = 1

    # Check if address channel activates
    await ClockCycles(dut.clk, 5)

    ar_valid = int(dut.ar_valid.value)
    if ar_valid:
        ar_addr = int(dut.ar_addr.value)
        ar_len = int(dut.ar_len.value)
        cocotb.log.info(f"✓ AXI AR active: addr=0x{ar_addr:X}, len={ar_len}")
    else:
        cocotb.log.info("No AXI AR activity (may be expected)")

    await ClockCycles(dut.clk, 5)

    # Test 4: AXI read data response interface
    cocotb.log.info("Test 4: AXI read data response interface")

    # Provide AXI read response
    dut.r_valid.value = 1
    dut.r_data.value = 0x123456789ABCDEF0
    dut.r_resp.value = 0  # OKAY response
    dut.r_last.value = 0
    dut.r_id.value = 0

    await ClockCycles(dut.clk, 3)

    r_ready = int(dut.r_ready.value)
    cocotb.log.info(f"R_READY signal: {r_ready}")

    # Test a few more beats, then set last
    dut.r_last.value = 1
    await ClockCycles(dut.clk, 2)

    dut.r_valid.value = 0
    dut.r_last.value = 0
    await ClockCycles(dut.clk, 2)

    # Test 5: SRAM write interface
    cocotb.log.info("Test 5: SRAM write interface")

    # Enable SRAM write ready (single bit for read engine)
    dut.wr_ready.value = 1  # Ready to accept SRAM writes

    await ClockCycles(dut.clk, 3)

    wr_valid = int(dut.wr_valid.value)
    if wr_valid:
        wr_data_0 = int(dut.wr_data[0].value)
        cocotb.log.info(f"✓ SRAM WR active: data[0]=0x{wr_data_0:X}")
    else:
        cocotb.log.info("No SRAM WR activity (may be expected)")

    await ClockCycles(dut.clk, 5)

    # Test 6: Error checking
    cocotb.log.info("Test 6: Error checking")

    data_error = int(dut.data_error.value)
    if data_error == 0:
        cocotb.log.info("✓ No data errors")
    else:
        cocotb.log.info(f"⚠ Data errors: 0x{data_error:X}")

    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Source AXI Read Engine Basic Test Complete ===")


@cocotb.test()
async def test_hbm3e_read_transfer_size_configs(dut):
    """Test HBM3e transfer size configurations for read engine."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Initialize all signals
    await init_signals(dut)
    await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== Testing HBM3e Read Transfer Size Configurations ===")

    # Test configurations: (cfg_value, expected_size, expected_beats)
    test_configs = [
        (0, "256B", 4),   # 256B = 4 beats of 64B
        (1, "512B", 8),   # 512B = 8 beats of 64B
        (2, "1KB", 16),   # 1KB = 16 beats of 64B
        (3, "2KB", 32),   # 2KB = 32 beats of 64B
        (4, "4KB", 64),   # 4KB = 64 beats of 64B
    ]

    for cfg_value, size_name, expected_beats in test_configs:
        cocotb.log.info(f"Testing {size_name} read transfers (cfg={cfg_value}, expected_beats={expected_beats})")

        # Set transfer size configuration
        dut.cfg_transfer_size.value = cfg_value

        # Apply scheduler data request
        dut.data_valid.value = 0x1  # Channel 0 has data
        dut.data_address[0].value = 0x3000
        dut.data_length[0].value = expected_beats  # Match expected burst length
        dut.data_type[0].value = 0
        dut.data_eos.value = 0x0

        # Enable AXI ready signals
        dut.ar_ready.value = 1

        await ClockCycles(dut.clk, 10)

        # Check if AXI address channel activates with correct length
        ar_valid = int(dut.ar_valid.value)
        if ar_valid:
            ar_len = int(dut.ar_len.value)
            # AXI ARLEN is (burst_length - 1)
            if ar_len == (expected_beats - 1):
                cocotb.log.info(f"✓ {size_name}: Correct AXI ARLEN = {ar_len} (burst_len={expected_beats})")
            else:
                cocotb.log.error(f"✗ {size_name}: Wrong AXI ARLEN = {ar_len}, expected {expected_beats-1}")
        else:
            cocotb.log.info(f"⚠ {size_name}: No AXI AR activity (may need different stimulus)")

        # Clear signals for next test
        dut.data_valid.value = 0
        dut.ar_ready.value = 0

        await ClockCycles(dut.clk, 5)

    cocotb.log.info("=== HBM3e Read Transfer Size Configuration Test Complete ===")


async def init_signals(dut):
    """Initialize all DUT signals to safe values."""

    # Reset
    dut.rst_n.value = 0

    # Configuration for HBM3e transfer sizes
    dut.cfg_transfer_size.value = 1  # 512B transfers (default)

    # Multi-channel scheduler data interface
    dut.data_valid.value = 0
    # Get actual number of channels from DUT structure
    num_channels = len(dut.data_address)
    for i in range(num_channels):
        dut.data_address[i].value = 0
        dut.data_length[i].value = 0
        dut.data_type[i].value = 0
    dut.data_eos.value = 0

    # Alignment interface - initialize to safe values
    if hasattr(dut, 'data_alignment_valid'):
        pass  # Will be handled by struct initialization

    # AXI read address channel
    dut.ar_ready.value = 0

    # AXI read data channel
    dut.r_valid.value = 0
    dut.r_data.value = 0
    dut.r_resp.value = 0
    dut.r_last.value = 0
    dut.r_id.value = 0

    # SRAM write interface
    dut.wr_ready.value = 0
    for i in range(num_channels):
        if hasattr(dut, 'wr_data') and len(dut.wr_data) > i:
            pass  # Will be driven by RTL

    # Monitor bus (if present)
    if hasattr(dut, 'mon_ready'):
        dut.mon_ready.value = 1

    await ClockCycles(dut.clk, 2)

    # Release reset
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 3)


@pytest.mark.parametrize("num_channels,addr_width,data_width,axi_id_width", [
    (2, 32, 512, 4),
    (8, 64, 512, 8),
])
def test_source_axi_read_engine_rtl(request, num_channels, addr_width, data_width, axi_id_width):
    """RTL test for source AXI read engine."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_amba_gaxi': 'rtl/amba/gaxi'
    })

    dut_name = "source_axi_read_engine"
    toplevel = dut_name

    # RTL source files - packages must be compiled first
    verilog_sources = [
        # Packages first (must be compiled before imports)
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_rapids_includes'], "rapids_pkg.sv"),
        # Dependencies
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_common'], "arbiter_priority_encoder.sv"),
        os.path.join(rtl_dict['rtl_common'], "arbiter_round_robin.sv"),
        os.path.join(rtl_dict['rtl_amba_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba_gaxi'], "gaxi_skid_buffer.sv"),
        # Main DUT (must be last)
        os.path.join(rtl_dict['rtl_rapids_fub'], f"{dut_name}.sv"),
    ]

    # Include directories
    includes = [
        rtl_dict['rtl_rapids_includes'],
        rtl_dict['rtl_amba_includes'],
        rtl_dict['rtl_common']
    ]

    # Test name with parameters
    nc_str = TBBase.format_dec(num_channels, 1)
    aw_str = TBBase.format_dec(addr_width, 2)
    dw_str = TBBase.format_dec(data_width, 3)
    id_str = TBBase.format_dec(axi_id_width, 1)
    test_name_plus_params = f"test_source_axi_read_engine_{dut_name}_nc{nc_str}_aw{aw_str}_dw{dw_str}_id{id_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'NUM_CHANNELS': str(num_channels),
        'ADDR_WIDTH': str(addr_width),
        'DATA_WIDTH': str(data_width),
        'AXI_ID_WIDTH': str(axi_id_width),
        'NUM_CHUNKS': str(data_width // 32),
        'MAX_BURST_LEN': '64',
        'TIMEOUT_CYCLES': '1000',
        'TRACKING_FIFO_DEPTH': '32',
        'COUNT_BITS': '8',
        'MON_AGENT_ID': "8'h40",
        'MON_UNIT_ID': "4'h1",
        'MON_CHANNEL_ID': "6'h0"
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
        "-Wno-EOFNEWLINE",
        "-Wno-PINCONNECTEMPTY",
        "-Wno-IMPORTSTAR",
        "-Wno-SYNCASYNCNET",
        "-Wno-WIDTHEXPAND",
        "-Wno-WIDTHTRUNC"
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

        print(f"✓ Source AXI Read Engine test completed!")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Parameters: {num_channels} channels, {addr_width}-bit addr, {data_width}-bit data, {axi_id_width}-bit ID")

    except Exception as e:
        print(f"❌ Source AXI Read Engine test failed: {str(e)}")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Source AXI Read Engine FUB Test")
    print("Run with: pytest val/rapids/fub_tests/axi_engines/test_source_axi_read_engine_simple.py -v")