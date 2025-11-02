"""
Test runner for datapath_rd_test module.

Purpose: Validate read data path streaming performance.
         Tests AXI Read Engine → SRAM Controller → SRAM integration.

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

from projects.components.stream.dv.tbclasses.datapath_rd_test_tb import DatapathRdTestTB


@cocotb.test()
async def test_datapath_rd_basic_streaming(dut):
    """Test basic read streaming without backpressure.

    Validates:
    - AXI read transactions complete successfully
    - SRAM fills with data from memory
    - No stalls under continuous streaming
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 0
    src_addr = 0x1000_0000  # Aligned to 64 bytes (512-bit)
    total_beats = 64
    burst_len = 16

    # Run streaming test
    success, cycles, stalls = await tb.run_streaming_test(
        channel_id=channel_id,
        src_addr=src_addr,
        total_beats=total_beats,
        burst_len=burst_len,
        check_stalls=True
    )

    # Verify results
    assert success, "Read streaming test failed"
    stall_ratio = stalls / cycles if cycles > 0 else 0
    print(f"\nRead Streaming Results:")
    print(f"  Total cycles: {cycles}")
    print(f"  Stall cycles: {stalls}")
    print(f"  Stall ratio: {stall_ratio*100:.1f}%")

    # For streaming, expect < 5% stalls
    assert stall_ratio < 0.05, \
        f"Too many stalls: {stall_ratio*100:.1f}% (expected < 5%)"


@cocotb.test()
async def test_datapath_rd_multiple_bursts(dut):
    """Test multiple read bursts to same channel.

    Validates:
    - Multiple burst transactions work correctly
    - SRAM doesn't overflow
    - Completion signaling accurate
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 1
    src_addr = 0x2000_0000
    burst_len = 8

    # Run multiple bursts
    for burst in range(4):
        addr = src_addr + (burst * burst_len * 64)  # 64 bytes per beat

        success, cycles, stalls = await tb.run_streaming_test(
            channel_id=channel_id,
            src_addr=addr,
            total_beats=burst_len,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Burst {burst} failed"
        print(f"Burst {burst}: {cycles} cycles, {stalls} stalls")


@cocotb.test()
async def test_datapath_rd_max_burst(dut):
    """Test maximum burst length transfers.

    Validates:
    - MAX_BURST_LEN respected
    - Long transfers handled correctly
    - Performance at max burst size
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 2
    src_addr = 0x3000_0000
    total_beats = 256  # Large transfer
    burst_len = 16  # MAX_BURST_LEN

    # Run test
    success, cycles, stalls = await tb.run_streaming_test(
        channel_id=channel_id,
        src_addr=src_addr,
        total_beats=total_beats,
        burst_len=burst_len,
        check_stalls=True
    )

    # Verify
    assert success, "Max burst test failed"
    print(f"\nMax Burst Test ({total_beats} beats @ burst_len={burst_len}):")
    print(f"  Cycles: {cycles}")
    print(f"  Stalls: {stalls}")


@cocotb.test()
async def test_datapath_rd_channel_isolation(dut):
    """Test channel isolation (no cross-channel interference).

    Validates:
    - Different channels don't interfere
    - SRAM segmentation works correctly
    - Per-channel status accurate
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test different channels sequentially
    for channel_id in [0, 3, 7]:
        src_addr = 0x4000_0000 + (channel_id * 0x1000)
        total_beats = 32
        burst_len = 8

        # Check initial SRAM state
        initial_count = await tb.check_sram_fill(channel_id)

        # Run transfer
        success, cycles, stalls = await tb.run_streaming_test(
            channel_id=channel_id,
            src_addr=src_addr,
            total_beats=total_beats,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Channel {channel_id} test failed"

        # Check final SRAM state
        final_count = await tb.check_sram_fill(channel_id)
        assert final_count >= initial_count, \
            f"Channel {channel_id} SRAM count decreased"

        print(f"Channel {channel_id}: {initial_count} → {final_count} entries")


@cocotb.test()
async def test_datapath_rd_aligned_addresses(dut):
    """Test various aligned addresses.

    Validates:
    - Different aligned addresses work
    - No address calculation errors
    - Burst boundaries respected
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters
    channel_id = 4
    burst_len = 8

    # Test different aligned addresses
    test_addrs = [
        0x1000_0000,  # Base aligned
        0x1000_0200,  # Aligned + 512 bytes
        0x1000_0400,  # Aligned + 1024 bytes
        0x8000_0000,  # High address
    ]

    for addr in test_addrs:
        success, cycles, stalls = await tb.run_streaming_test(
            channel_id=channel_id,
            src_addr=addr,
            total_beats=burst_len,
            burst_len=burst_len,
            check_stalls=False
        )

        assert success, f"Address 0x{addr:016X} test failed"
        print(f"Address 0x{addr:016X}: OK")


@cocotb.test()
async def test_datapath_rd_extended_streaming_aggressive(dut):
    """AGGRESSIVE: Test extended streaming (2048 beats) for bubble-free operation.

    Validates:
    - Sustained streaming performance over long transfers
    - No degradation over extended operation
    - Continuous valid assertion (zero bubbles)
    - Theoretical bandwidth utilization > 95%
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    src_addr = 0x1000_0000
    total_beats = 2048  # Large transfer
    burst_len = 16

    # Populate source memory
    await tb.populate_memory(src_addr, total_beats, pattern='increment')

    # Issue request
    await tb.issue_read_request(channel_id, src_addr, total_beats, burst_len)

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
async def test_datapath_rd_burst_to_burst_latency_aggressive(dut):
    """AGGRESSIVE: Measure cycles between consecutive bursts.

    Validates:
    - Immediate ready after burst completion
    - No idle cycles between bursts
    - Pipeline doesn't drain
    - Inter-burst gap < 5 cycles
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    src_addr = 0x2000_0000
    burst_len = 16
    num_bursts = 20  # Many bursts to average

    # Run burst-to-burst measurement
    gaps, avg_gap, max_gap = await tb.measure_burst_to_burst_latency(
        channel_id, src_addr, burst_len, num_bursts)

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
async def test_datapath_rd_sustained_throughput_aggressive(dut):
    """AGGRESSIVE: Test sustained throughput with continuous back-to-back operations.

    Validates:
    - Continuous operation over multiple transfers
    - No performance degradation
    - Sustained bandwidth > 95%
    """
    # Initialize testbench
    tb = DatapathRdTestTB(dut)
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
        src_addr = base_addr + (op * beats_per_op * 64)

        # Populate memory
        await tb.populate_memory(src_addr, beats_per_op, pattern='increment')

        # Issue request
        await tb.issue_read_request(channel_id, src_addr, beats_per_op, 16)

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
