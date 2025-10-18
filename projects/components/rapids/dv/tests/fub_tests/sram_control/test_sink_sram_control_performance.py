# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: test_sink_sram_control_performance
# Purpose: RAPIDS Sink SRAM Control Performance Validation Test
#
# Documentation: projects/components/rapids/PRD.md
# Subsystem: rapids
#
# Author: sean galloway
# Created: 2025-10-18

"""
RAPIDS Sink SRAM Control Performance Validation Test

This test validates the sink SRAM control under critical Network performance constraints:
- Network bus saturated at 16 channels operating simultaneously
- Each channel produces data at average rate of once every 16 clocks
- AXI read/write transfers must never fail under these constraints
- Any AXI transfer failure under these conditions is a BUG

Critical Performance Requirements:
1. Sustained write rate: 16 channels × (1/16 clocks) = 1 write/clock peak
2. Read bandwidth: Must keep up with AXI engine demands
3. Credit flow: Must handle backpressure gracefully
4. No data loss: All Network data must be stored successfully
5. FIFO interfaces: Must not become bottlenecks

Test Scenarios:
- Sustained Network write load (critical constraint validation)
- Concurrent read/write operations (performance validation)
- Credit backpressure handling (flow control validation)
- Multi-channel arbitration (fairness and throughput validation)
"""

import os
import sys
import random
import pytest
import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles, FallingEdge
from cocotb.clock import Clock
from cocotb_test.simulator import run

# Add framework for basic utilities only
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "..", "bin"))
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd
from CocoTBFramework.tbclasses.shared.tbbase import TBBase


@cocotb.test()
async def test_mnoc_sustained_write_performance(dut):
    """Test sustained Network write performance under critical constraints."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")  # 100MHz
    cocotb.start_soon(clock.start())

    # Initialize signals
    await init_signals(dut)
    await ClockCycles(dut.clk, 10)

    cocotb.log.info("=== CRITICAL: Network Sustained Write Performance Test ===")
    cocotb.log.info("Constraint: 16 channels × 1/16 clocks = 1 write/clock peak")

    num_test_channels = 16
    writes_per_channel = 64  # Enough to fill and test sustained operation
    clock_period_per_channel = 16  # Each channel writes every 16 clocks

    # Enable all read interfaces to prevent backpressure
    dut.rd_ready.value = 0xFFFF  # All channels ready
    dut.data_consumed_ready.value = 1
    dut.eos_completion_ready.value = 1
    dut.mon_ready.value = 1
    dut.drain_enable.value = 1

    # Track statistics
    total_writes_sent = 0
    total_writes_accepted = 0
    backpressure_cycles = 0

    # Generate sustained write pattern: 16 channels, each writing every 16 clocks
    cocotb.log.info(f"Starting sustained write test: {num_test_channels} channels")

    for cycle in range(writes_per_channel * clock_period_per_channel):
        await RisingEdge(dut.clk)

        # Determine which channel should write this cycle
        active_channel = cycle % num_test_channels
        channel_cycle = cycle // num_test_channels

        # Each channel writes every 16 clocks
        if channel_cycle % clock_period_per_channel == 0:
            # Apply write
            dut.wr_valid.value = 1
            dut.wr_channel.value = active_channel
            dut.wr_data.value = 0x123456789ABCDEF0 + (active_channel << 32) + channel_cycle
            dut.wr_type.value = active_channel % 4  # Vary types
            dut.wr_eos.value = (channel_cycle == writes_per_channel - 1)  # EOS on last write
            dut.wr_chunk_en.value = 0xFFFF  # All chunks valid

            total_writes_sent += 1

            await FallingEdge(dut.clk)

            # Check if write was accepted
            wr_ready = int(dut.wr_ready.value)
            if wr_ready:
                total_writes_accepted += 1
            else:
                backpressure_cycles += 1
                cocotb.log.warning(f"CRITICAL: Backpressure on channel {active_channel} at cycle {cycle}")
        else:
            # No write this cycle
            dut.wr_valid.value = 0
            dut.wr_eos.value = 0

    # Final statistics
    write_acceptance_rate = (total_writes_accepted / total_writes_sent) * 100
    cocotb.log.info(f"Write Performance Results:")
    cocotb.log.info(f"  Total writes sent: {total_writes_sent}")
    cocotb.log.info(f"  Total writes accepted: {total_writes_accepted}")
    cocotb.log.info(f"  Acceptance rate: {write_acceptance_rate:.1f}%")
    cocotb.log.info(f"  Backpressure cycles: {backpressure_cycles}")

    # CRITICAL ASSERTION: Under Network constraints, writes must never fail
    if write_acceptance_rate < 100.0:
        cocotb.log.error("❌ CRITICAL BUG: AXI transfers failed under Network constraints!")
        cocotb.log.error(f"Expected: 100% acceptance rate under 16ch×1/16clk constraint")
        cocotb.log.error(f"Actual: {write_acceptance_rate:.1f}% - THIS IS A BUG")
        assert False, f"CRITICAL: Write acceptance rate {write_acceptance_rate:.1f}% < 100%"
    else:
        cocotb.log.info("✅ PASSED: All writes accepted under Network constraints")

    await ClockCycles(dut.clk, 50)  # Let pipeline drain

    cocotb.log.info("=== Network Sustained Write Performance Test Complete ===")


@cocotb.test()
async def test_concurrent_read_write_performance(dut):
    """Test concurrent read/write under Network performance constraints."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Initialize signals
    await init_signals(dut)
    await ClockCycles(dut.clk, 10)

    cocotb.log.info("=== Concurrent Read/Write Performance Test ===")

    num_channels = 8  # Test subset for detailed analysis
    writes_per_channel = 32

    # Enable FIFO interfaces
    dut.data_consumed_ready.value = 1
    dut.eos_completion_ready.value = 1
    dut.mon_ready.value = 1
    dut.drain_enable.value = 1

    # Start concurrent operations
    cocotb.start_soon(write_stimulus_process(dut, num_channels, writes_per_channel))
    cocotb.start_soon(read_stimulus_process(dut, num_channels))
    cocotb.start_soon(monitor_process(dut))

    # Run for sufficient time to complete all operations
    test_duration = writes_per_channel * 20  # Allow for processing time
    await ClockCycles(dut.clk, test_duration)

    cocotb.log.info("=== Concurrent Read/Write Performance Test Complete ===")


@cocotb.test()
async def test_credit_backpressure_handling(dut):
    """Test credit flow control under backpressure conditions."""

    # Setup clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())

    # Initialize signals
    await init_signals(dut)
    await ClockCycles(dut.clk, 10)

    cocotb.log.info("=== Credit Backpressure Handling Test ===")

    # Create backpressure scenario
    dut.data_consumed_ready.value = 0  # Block credit return
    dut.eos_completion_ready.value = 0  # Block EOS completion
    dut.mon_ready.value = 0  # Block monitor
    dut.drain_enable.value = 1

    # Apply writes until backpressure
    channel_to_test = 0
    writes_sent = 0
    backpressure_detected = False

    for cycle in range(100):  # Test for reasonable duration
        await RisingEdge(dut.clk)

        dut.wr_valid.value = 1
        dut.wr_channel.value = channel_to_test
        dut.wr_data.value = 0xDEADBEEF00000000 + cycle
        dut.wr_type.value = 0
        dut.wr_eos.value = 0
        dut.wr_chunk_en.value = 0xFFFF

        writes_sent += 1

        await FallingEdge(dut.clk)

        # Check for backpressure
        wr_ready = int(dut.wr_ready.value)
        if not wr_ready:
            backpressure_detected = True
            cocotb.log.info(f"✓ Backpressure detected after {writes_sent} writes")
            break

    if not backpressure_detected:
        cocotb.log.warning("⚠ No backpressure detected - may indicate insufficient test")

    dut.wr_valid.value = 0

    # Release backpressure and verify recovery
    await ClockCycles(dut.clk, 10)
    dut.data_consumed_ready.value = 1
    dut.eos_completion_ready.value = 1
    dut.mon_ready.value = 1

    await ClockCycles(dut.clk, 20)

    # Verify system can accept writes again
    dut.wr_valid.value = 1
    dut.wr_channel.value = channel_to_test
    dut.wr_data.value = 0xABCDEF0000000000
    dut.wr_type.value = 0
    dut.wr_eos.value = 1  # Test EOS handling
    dut.wr_chunk_en.value = 0xFFFF

    await FallingEdge(dut.clk)
    wr_ready_after_release = int(dut.wr_ready.value)

    if wr_ready_after_release:
        cocotb.log.info("✓ System recovered from backpressure")
    else:
        cocotb.log.error("❌ System did not recover from backpressure")

    dut.wr_valid.value = 0
    await ClockCycles(dut.clk, 10)

    cocotb.log.info("=== Credit Backpressure Handling Test Complete ===")


async def write_stimulus_process(dut, num_channels, writes_per_channel):
    """Background process to generate write stimulus."""
    for channel in range(num_channels):
        for write_num in range(writes_per_channel):
            # Write pattern simulating Network arrival
            await ClockCycles(dut.clk, random.randint(1, 4))  # Variable timing

            dut.wr_valid.value = 1
            dut.wr_channel.value = channel
            dut.wr_data.value = 0x1000000000000000 + (channel << 40) + write_num
            dut.wr_type.value = channel % 4
            dut.wr_eos.value = (write_num == writes_per_channel - 1)
            dut.wr_chunk_en.value = 0xFFFF

            await FallingEdge(dut.clk)
            dut.wr_valid.value = 0
            dut.wr_eos.value = 0


async def read_stimulus_process(dut, num_channels):
    """Background process to generate read stimulus."""
    while True:
        await ClockCycles(dut.clk, random.randint(5, 15))

        # Randomly enable/disable read ready for channels
        ready_mask = random.randint(0, (1 << num_channels) - 1)
        dut.rd_ready.value = ready_mask

        await ClockCycles(dut.clk, random.randint(3, 10))


async def monitor_process(dut):
    """Background process to monitor system state."""
    while True:
        await ClockCycles(dut.clk, 20)

        # Check for overflow conditions
        channel_overflow = int(dut.channel_overflow.value)
        if channel_overflow != 0:
            cocotb.log.error(f"❌ Channel overflow detected: 0x{channel_overflow:X}")

        # Monitor FIFO states
        data_consumed_valid = int(dut.data_consumed_valid.value)
        eos_completion_valid = int(dut.eos_completion_valid.value)
        mon_valid = int(dut.mon_valid.value)

        if data_consumed_valid or eos_completion_valid or mon_valid:
            cocotb.log.debug(f"FIFO activity: data_cons={data_consumed_valid}, eos_comp={eos_completion_valid}, mon={mon_valid}")


async def init_signals(dut):
    """Initialize all DUT signals to safe values."""

    # Reset
    dut.rst_n.value = 0

    # Write interface
    dut.wr_valid.value = 0
    dut.wr_data.value = 0
    dut.wr_channel.value = 0
    dut.wr_type.value = 0
    dut.wr_eos.value = 0
    dut.wr_chunk_en.value = 0

    # Read interface
    dut.rd_ready.value = 0

    # FIFO interfaces
    dut.data_consumed_ready.value = 1
    dut.eos_completion_ready.value = 1
    dut.mon_ready.value = 1

    # Control
    dut.drain_enable.value = 0

    await ClockCycles(dut.clk, 5)

    # Release reset
    dut.rst_n.value = 1
    await ClockCycles(dut.clk, 5)


@pytest.mark.parametrize("channels,lines_per_channel,data_width", [
    (16, 256, 512),  # Critical Network constraint configuration
    (32, 256, 512),  # Full scale configuration
])
def test_sink_sram_control_performance_rtl(request, channels, lines_per_channel, data_width):
    """RTL test for sink SRAM control performance validation."""

    module, repo_root, tests_dir, log_dir, rtl_dict = get_paths({
        'rtl_rapids_fub': '../../rtl/rapids_fub',
        'rtl_rapids_includes': '../../rtl/includes',
        'rtl_amba_includes': 'rtl/amba/includes',
        'rtl_common': 'rtl/common',
        'rtl_amba_gaxi': 'rtl/amba/gaxi'
    })

    dut_name = "sink_sram_control"
    toplevel = dut_name

    # RTL source files
    verilog_sources = [
        # Packages first
        os.path.join(rtl_dict['rtl_amba_includes'], "monitor_pkg.sv"),
        os.path.join(rtl_dict['rtl_rapids_includes'], "rapids_pkg.sv"),
        # Dependencies
        os.path.join(rtl_dict['rtl_common'], "counter_bin.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_control.sv"),
        os.path.join(rtl_dict['rtl_common'], "fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_amba_gaxi'], "gaxi_fifo_sync.sv"),
        os.path.join(rtl_dict['rtl_rapids_fub'], "simple_sram.sv"),
        # Main DUT
        os.path.join(rtl_dict['rtl_rapids_fub'], f"{dut_name}.sv"),
    ]

    # Include directories
    includes = [
        rtl_dict['rtl_rapids_includes'],
        rtl_dict['rtl_amba_includes'],
        rtl_dict['rtl_common']
    ]

    # Test name with parameters
    ch_str = TBBase.format_dec(channels, 2)
    lpc_str = TBBase.format_dec(lines_per_channel, 3)
    dw_str = TBBase.format_dec(data_width, 3)
    test_name_plus_params = f"test_sink_sram_control_perf_ch{ch_str}_lpc{lpc_str}_dw{dw_str}"
    log_path = os.path.join(log_dir, f'{test_name_plus_params}.log')

    sim_build = os.path.join(tests_dir, 'local_sim_build', test_name_plus_params)
    os.makedirs(sim_build, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)

    # RTL parameters
    rtl_parameters = {
        'CHANNELS': str(channels),
        'LINES_PER_CHANNEL': str(lines_per_channel),
        'DATA_WIDTH': str(data_width),
        'PTR_BITS': str(int(lines_per_channel).bit_length() + 1),
        'CHAN_BITS': str(int(channels).bit_length()),
        'COUNT_BITS': str(int(lines_per_channel).bit_length()),  # Must be sufficient for LINES_PER_CHANNEL
        'NUM_CHUNKS': str(data_width // 32),
        'OVERFLOW_MARGIN': '8',
        'USED_THRESHOLD': '4',
        'MON_AGENT_ID': "8'h11",
        'MON_UNIT_ID': "4'h3",
        'MON_CHANNEL_ID': "6'h1",
        'DATA_CONSUMED_FIFO_DEPTH': '8',
        'EOS_COMPLETION_FIFO_DEPTH': '8',
        'MONITOR_FIFO_DEPTH': '16'
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
        "-Wno-WIDTHTRUNC",
        "-Wno-BLKSEQ"
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

        print(f"✅ Sink SRAM Control Performance test completed!")
        print(f"CRITICAL: Validated Network constraints (16ch × 1/16clk)")
        print(f"Logs: {log_path}")
        print(f"Waveforms: {cmd_filename}")
        print(f"Config: {channels} channels, {lines_per_channel} lines/ch, {data_width}-bit data")

    except Exception as e:
        print(f"❌ Sink SRAM Control Performance test failed: {str(e)}")
        print(f"CRITICAL: This may indicate AXI transfer failures under Network constraints")
        print(f"Logs preserved at: {log_path}")
        print(f"To view waveforms: {cmd_filename}")
        raise


if __name__ == "__main__":
    print("RAPIDS Sink SRAM Control Performance Validation Test")
    print("CRITICAL: Validates Network performance constraints (16ch × 1/16clk)")
    print("Run with: pytest val/rapids/fub_tests/sram_control/test_sink_sram_control_performance.py -v")