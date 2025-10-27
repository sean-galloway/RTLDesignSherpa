"""
Test runner for datapath_wr_test module.

Purpose: Validate write data path streaming performance.
         Tests SRAM → SRAM Controller → AXI Write Engine integration.

Author: sean galloway
Created: 2025-10-26
"""

import cocotb
from cocotb.triggers import Timer
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../../../'))
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.datapath_wr_test_tb import DatapathWrTestTB


@cocotb.test()
async def test_datapath_wr_basic_streaming(dut):
    """Test basic write streaming without backpressure.

    Validates:
    - SRAM data transfers to AXI correctly
    - AXI write transactions complete successfully
    - Data integrity through the write path
    - No stalls under continuous streaming
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 0
    dst_addr = 0x5000_0000  # Aligned to 64 bytes (512-bit)
    total_beats = 64
    burst_len = 16

    # Run streaming test
    success, cycles, stalls, data_ok = await tb.run_streaming_test(
        channel_id=channel_id,
        dst_addr=dst_addr,
        total_beats=total_beats,
        burst_len=burst_len,
        check_stalls=True
    )

    # Verify results
    assert success, "Write streaming test failed"
    assert data_ok, "Data mismatch detected"

    stall_ratio = stalls / cycles if cycles > 0 else 0
    print(f"\nWrite Streaming Results:")
    print(f"  Total cycles: {cycles}")
    print(f"  Stall cycles: {stalls}")
    print(f"  Stall ratio: {stall_ratio*100:.1f}%")
    print(f"  Data match: {data_ok}")

    # For streaming, expect < 5% stalls
    assert stall_ratio < 0.05, \
        f"Too many stalls: {stall_ratio*100:.1f}% (expected < 5%)"


@cocotb.test()
async def test_datapath_wr_multiple_bursts(dut):
    """Test multiple write bursts from same channel.

    Validates:
    - Multiple burst transactions work correctly
    - SRAM reads don't underflow
    - Data integrity across multiple bursts
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 1
    dst_addr = 0x6000_0000
    burst_len = 8

    # Run multiple bursts
    for burst in range(4):
        addr = dst_addr + (burst * burst_len * 64)  # 64 bytes per beat

        success, cycles, stalls, data_ok = await tb.run_streaming_test(
            channel_id=channel_id,
            dst_addr=addr,
            total_beats=burst_len,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Burst {burst} failed"
        assert data_ok, f"Burst {burst} data mismatch"
        print(f"Burst {burst}: {cycles} cycles, {stalls} stalls, data OK")


@cocotb.test()
async def test_datapath_wr_max_burst(dut):
    """Test maximum burst length transfers.

    Validates:
    - MAX_BURST_LEN respected
    - Long transfers handled correctly
    - Performance at max burst size
    - Data integrity at high burst sizes
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 2
    dst_addr = 0x7000_0000
    total_beats = 256  # Large transfer
    burst_len = 16  # MAX_BURST_LEN

    # Run test
    success, cycles, stalls, data_ok = await tb.run_streaming_test(
        channel_id=channel_id,
        dst_addr=dst_addr,
        total_beats=total_beats,
        burst_len=burst_len,
        check_stalls=True
    )

    # Verify
    assert success, "Max burst test failed"
    assert data_ok, "Data mismatch in max burst test"

    print(f"\nMax Burst Test ({total_beats} beats @ burst_len={burst_len}):")
    print(f"  Cycles: {cycles}")
    print(f"  Stalls: {stalls}")
    print(f"  Data match: {data_ok}")


@cocotb.test()
async def test_datapath_wr_channel_isolation(dut):
    """Test channel isolation (no cross-channel interference).

    Validates:
    - Different channels write to correct addresses
    - SRAM segmentation works correctly
    - No data corruption between channels
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test different channels sequentially
    for channel_id in [0, 3, 7]:
        dst_addr = 0x8000_0000 + (channel_id * 0x1000)
        total_beats = 32
        burst_len = 8

        # Run transfer
        success, cycles, stalls, data_ok = await tb.run_streaming_test(
            channel_id=channel_id,
            dst_addr=dst_addr,
            total_beats=total_beats,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Channel {channel_id} test failed"
        assert data_ok, f"Channel {channel_id} data mismatch"

        print(f"Channel {channel_id}: {cycles} cycles, data OK")


@cocotb.test()
async def test_datapath_wr_aligned_addresses(dut):
    """Test various aligned addresses.

    Validates:
    - Different aligned addresses work
    - No address calculation errors
    - Burst boundaries respected
    - Data written to correct addresses
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 4
    burst_len = 8

    # Test different aligned addresses
    test_addrs = [
        0x9000_0000,  # Base aligned
        0x9000_0200,  # Aligned + 512 bytes
        0x9000_0400,  # Aligned + 1024 bytes
        0xA000_0000,  # High address
    ]

    for addr in test_addrs:
        success, cycles, stalls, data_ok = await tb.run_streaming_test(
            channel_id=channel_id,
            dst_addr=addr,
            total_beats=burst_len,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Address 0x{addr:016X} test failed"
        assert data_ok, f"Address 0x{addr:016X} data mismatch"
        print(f"Address 0x{addr:016X}: OK")


@cocotb.test()
async def test_datapath_wr_data_patterns(dut):
    """Test different data patterns through write path.

    Validates:
    - Increment pattern integrity
    - Fixed pattern integrity
    - No data corruption
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 5
    dst_addr = 0xB000_0000
    total_beats = 32
    burst_len = 8

    # Test increment pattern (default in TB)
    success, cycles, stalls, data_ok = await tb.run_streaming_test(
        channel_id=channel_id,
        dst_addr=dst_addr,
        total_beats=total_beats,
        burst_len=burst_len,
        check_stalls=False
    )

    assert success, "Increment pattern test failed"
    assert data_ok, "Increment pattern data mismatch"
    print(f"Increment pattern: OK ({cycles} cycles)")

    # TODO: Add fixed and random pattern tests when TB support added


@cocotb.test()
async def test_datapath_wr_back_to_back(dut):
    """Test back-to-back write operations.

    Validates:
    - Minimal idle cycles between transfers
    - Ready/valid handshaking correct
    - No data loss between operations
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 6
    dst_addr = 0xC000_0000
    burst_len = 8

    total_cycles = 0

    # Run back-to-back operations
    for op in range(8):
        addr = dst_addr + (op * burst_len * 64)

        success, cycles, stalls, data_ok = await tb.run_streaming_test(
            channel_id=channel_id,
            dst_addr=addr,
            total_beats=burst_len,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Operation {op} failed"
        assert data_ok, f"Operation {op} data mismatch"

        total_cycles += cycles

    avg_cycles = total_cycles / 8
    print(f"Back-to-back: 8 ops, {total_cycles} total cycles, {avg_cycles:.1f} avg")


@cocotb.test()
async def test_datapath_wr_extended_streaming_aggressive(dut):
    """AGGRESSIVE: Test extended streaming (2048 beats) for bubble-free operation.

    Validates:
    - Sustained streaming performance over long transfers
    - No degradation over extended operation
    - Continuous valid assertion (zero bubbles)
    - Theoretical bandwidth utilization > 95%
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    dst_addr = 0x1000_0000
    total_beats = 2048  # Large transfer
    burst_len = 16

    # Preload SRAM with test data
    sram_offset = channel_id * (tb.sram_depth // tb.num_channels)
    await tb.preload_sram(sram_offset, total_beats, pattern='increment')

    # Issue request
    await tb.issue_write_request(channel_id, dst_addr, total_beats, burst_len)

    # Run enhanced metrics in parallel with transaction
    import cocotb
    from cocotb.triggers import Join

    # Start continuous monitoring
    continuous_task = cocotb.start_soon(tb.verify_continuous_streaming(total_beats))
    bandwidth_task = cocotb.start_soon(tb.measure_bandwidth_utilization(total_beats))

    # Wait for completion
    max_consecutive, invalid_gaps, beats_done = await continuous_task
    actual_cycles, utilization, beats_bw = await bandwidth_task

    # Verify all beats transferred
    assert beats_done == total_beats, \
        f"Continuous monitor: {beats_done}/{total_beats} beats"
    assert beats_bw == total_beats, \
        f"Bandwidth monitor: {beats_bw}/{total_beats} beats"

    # Report
    print(f"\n=== AGGRESSIVE Extended Streaming Results ({total_beats} beats) ===")
    print(f"  Transfer cycles: {actual_cycles}")
    print(f"  Max consecutive valid: {max_consecutive}")
    print(f"  Invalid gaps: {invalid_gaps}")
    print(f"  Bandwidth utilization: {utilization:.2f}%")
    print(f"  Beats transferred: {beats_done}/{total_beats}")

    # AGGRESSIVE assertions for perfect bubble-free operation
    assert invalid_gaps == 0, \
        f"Found {invalid_gaps} gaps in streaming - NOT BUBBLE-FREE!"

    assert utilization > 95.0, \
        f"Bandwidth utilization {utilization:.2f}% < 95% - NOT OPTIMAL!"

    assert max_consecutive >= total_beats * 0.95, \
        f"Max consecutive {max_consecutive} < 95% of {total_beats} - BUBBLES DETECTED!"

    print(">>> PERFECT BUBBLE-FREE OPERATION ACHIEVED <<<")


@cocotb.test()
async def test_datapath_wr_burst_to_burst_latency_aggressive(dut):
    """AGGRESSIVE: Measure cycles between consecutive bursts.

    Validates:
    - Immediate ready after burst completion
    - No idle cycles between bursts
    - Pipeline doesn't drain
    - Inter-burst gap < 5 cycles
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    dst_addr = 0x2000_0000
    burst_len = 16
    num_bursts = 20  # Many bursts to average

    # Run burst-to-burst measurement
    gaps, avg_gap, max_gap = await tb.measure_burst_to_burst_latency(
        channel_id, dst_addr, burst_len, num_bursts)

    # Report
    print(f"\n=== AGGRESSIVE Burst-to-Burst Latency ===")
    print(f"  Number of bursts: {num_bursts}")
    print(f"  Burst length: {burst_len} beats")
    print(f"  Average gap: {avg_gap:.1f} cycles")
    print(f"  Maximum gap: {max_gap} cycles")
    print(f"  Minimum gap: {min(gaps) if gaps else 0} cycles")
    print(f"  All gaps: {gaps}")

    # AGGRESSIVE assertions for minimal latency
    assert max_gap <= 5, \
        f"Maximum gap {max_gap} cycles > 5 - NOT BUBBLE-FREE!"

    assert avg_gap <= 3, \
        f"Average gap {avg_gap:.1f} cycles > 3 - INEFFICIENT!"

    # Check for consistency (all gaps should be similar)
    if len(gaps) > 1:
        gap_variance = max(gaps) - min(gaps)
        assert gap_variance <= 3, \
            f"Gap variance {gap_variance} cycles > 3 - INCONSISTENT!"

    print(">>> MINIMAL INTER-BURST LATENCY ACHIEVED <<<")


@cocotb.test()
async def test_datapath_wr_sustained_throughput_aggressive(dut):
    """AGGRESSIVE: Test sustained throughput with continuous back-to-back operations.

    Validates:
    - Continuous operation over multiple transfers
    - No performance degradation
    - Sustained bandwidth > 95%
    """
    # Initialize testbench
    tb = DatapathWrTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE CONTINUOUS OPERATION
    channel_id = 0
    base_addr = 0x3000_0000
    beats_per_op = 256
    num_operations = 8  # 8 × 256 = 2048 total beats

    total_cycles = 0
    total_beats = 0
    min_utilization = 100.0

    print(f"\n=== AGGRESSIVE Sustained Throughput Test ===")
    print(f"  Operations: {num_operations} × {beats_per_op} beats")

    for op in range(num_operations):
        dst_addr = base_addr + (op * beats_per_op * 64)

        # Preload SRAM
        sram_offset = channel_id * (tb.sram_depth // tb.num_channels)
        await tb.preload_sram(sram_offset, beats_per_op, pattern='increment')

        # Issue request
        await tb.issue_write_request(channel_id, dst_addr, beats_per_op, 16)

        # Measure this operation
        actual_cycles, utilization, beats_done = await tb.measure_bandwidth_utilization(beats_per_op)

        total_cycles += actual_cycles
        total_beats += beats_done
        min_utilization = min(min_utilization, utilization)

        print(f"  Op {op}: {actual_cycles} cycles, {utilization:.2f}% BW")

        # Each operation should maintain high bandwidth
        assert utilization > 90.0, \
            f"Op {op} bandwidth {utilization:.2f}% < 90% - DEGRADATION!"

    # Overall metrics
    overall_utilization = (total_beats / total_cycles * 100) if total_cycles > 0 else 0

    print(f"\n  Total: {total_beats} beats in {total_cycles} cycles")
    print(f"  Overall BW utilization: {overall_utilization:.2f}%")
    print(f"  Minimum BW per op: {min_utilization:.2f}%")

    # AGGRESSIVE assertions
    assert overall_utilization > 95.0, \
        f"Overall bandwidth {overall_utilization:.2f}% < 95%!"

    assert min_utilization > 90.0, \
        f"Minimum per-op bandwidth {min_utilization:.2f}% < 90%!"

    print(">>> SUSTAINED HIGH THROUGHPUT ACHIEVED <<<")
