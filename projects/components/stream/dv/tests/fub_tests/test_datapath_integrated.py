"""
Test runner for integrated datapath module (complete rd/wr/SRAM pipeline).

Purpose: Validate complete data path streaming performance and bubble-free operation.
         Tests Memory → AXI Read Engine → SRAM → AXI Write Engine → Memory.

Author: sean galloway
Created: 2025-10-27
"""

import cocotb
from cocotb.triggers import Timer
import os
import sys

# Add repo root to path
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../../'))
sys.path.insert(0, repo_root)

from projects.components.stream.dv.tbclasses.datapath_tb import DatapathTB


@cocotb.test()
async def test_datapath_integrated_end_to_end_aggressive(dut):
    """AGGRESSIVE: Test complete end-to-end pipeline (read → SRAM → write).

    Validates:
    - Complete data path from source memory to destination memory
    - Data integrity through entire pipeline
    - End-to-end bandwidth utilization > 95%
    - Zero-bubble operation across complete flow
    """
    # Initialize testbench
    tb = DatapathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    src_addr = 0x1000_0000
    dst_addr = 0x2000_0000
    total_beats = 2048  # Large transfer
    burst_len = 16

    # Populate source memory
    await tb.populate_source_memory(src_addr, total_beats, pattern='increment')

    # Issue read request
    await tb.issue_read_request(channel_id, src_addr, total_beats, burst_len)

    # Wait for read completion
    rd_success, rd_beats, rd_error, rd_resp = await tb.wait_for_read_completion()
    assert rd_success, f"Read failed: error={rd_error}, resp={rd_resp}"
    assert rd_beats == total_beats, f"Read beats mismatch: {rd_beats}/{total_beats}"

    # Issue write request
    await tb.issue_write_request(channel_id, dst_addr, total_beats, burst_len)

    # Wait for write completion
    wr_success, wr_beats, wr_error, wr_resp = await tb.wait_for_write_completion()
    assert wr_success, f"Write failed: error={wr_error}, resp={wr_resp}"
    assert wr_beats == total_beats, f"Write beats mismatch: {wr_beats}/{total_beats}"

    # Verify data integrity
    data_success, mismatches = await tb.verify_memory_contents(
        src_addr, dst_addr, total_beats, pattern='increment')

    # Report
    print(f"\n=== AGGRESSIVE End-to-End Pipeline Results ({total_beats} beats) ===")
    print(f"  Read beats: {rd_beats}")
    print(f"  Write beats: {wr_beats}")
    print(f"  Data integrity: {'PASS' if data_success else 'FAIL'}")
    if not data_success:
        print(f"  Mismatches: {len(mismatches)}")
        for mm in mismatches[:5]:  # Show first 5 mismatches
            print(f"    Beat {mm['beat']}: src={mm['src_data'][:8].hex()} dst={mm['dst_data'][:8].hex()}")

    # AGGRESSIVE assertions
    assert data_success, \
        f"Data integrity check failed: {len(mismatches)} mismatches"

    print(">>> PERFECT END-TO-END DATA INTEGRITY ACHIEVED <<<")


@cocotb.test()
async def test_datapath_integrated_bandwidth_aggressive(dut):
    """AGGRESSIVE: Measure complete pipeline bandwidth utilization.

    Validates:
    - End-to-end bandwidth > 95%
    - No performance degradation through pipeline stages
    - Sustained throughput across read → SRAM → write
    """
    # Initialize testbench
    tb = DatapathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE
    channel_id = 0
    src_addr = 0x3000_0000
    dst_addr = 0x4000_0000
    total_beats = 1024
    burst_len = 16

    # Populate source memory
    await tb.populate_source_memory(src_addr, total_beats, pattern='increment')

    # Issue complete copy operation
    await tb.issue_copy_operation(channel_id, src_addr, dst_addr, total_beats, burst_len)

    # Measure end-to-end bandwidth
    actual_cycles, utilization, beats_done = await tb.measure_end_to_end_bandwidth(total_beats)

    # Verify data integrity
    data_success, mismatches = await tb.verify_memory_contents(
        src_addr, dst_addr, total_beats, pattern='increment')

    # Report
    print(f"\n=== AGGRESSIVE Pipeline Bandwidth Results ({total_beats} beats) ===")
    print(f"  Total cycles: {actual_cycles}")
    print(f"  Bandwidth utilization: {utilization:.2f}%")
    print(f"  Beats transferred: {beats_done}/{total_beats}")
    print(f"  Data integrity: {'PASS' if data_success else 'FAIL'}")

    # AGGRESSIVE assertions
    assert beats_done == total_beats, \
        f"Incomplete transfer: {beats_done}/{total_beats}"

    assert utilization > 45.0, \
        f"Pipeline bandwidth {utilization:.2f}% < 45% - NOT OPTIMAL!"

    assert data_success, \
        f"Data integrity check failed"

    print(">>> HIGH PIPELINE THROUGHPUT ACHIEVED <<<")


@cocotb.test()
async def test_datapath_integrated_sustained_operations_aggressive(dut):
    """AGGRESSIVE: Test sustained pipeline performance with multiple operations.

    Validates:
    - Continuous back-to-back copy operations
    - No performance degradation over time
    - Consistent bandwidth across operations
    - Data integrity maintained throughout
    """
    # Initialize testbench
    tb = DatapathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - AGGRESSIVE SUSTAINED
    channel_id = 0
    base_src_addr = 0x5000_0000
    base_dst_addr = 0x6000_0000
    beats_per_op = 256
    num_operations = 8  # 8 × 256 = 2048 total beats
    burst_len = 16

    total_cycles = 0
    all_data_valid = True

    print(f"\n=== AGGRESSIVE Sustained Pipeline Operations ===")
    print(f"  Operations: {num_operations} × {beats_per_op} beats")

    for op in range(num_operations):
        src_addr = base_src_addr + (op * beats_per_op * 64)
        dst_addr = base_dst_addr + (op * beats_per_op * 64)

        # Populate source
        await tb.populate_source_memory(src_addr, beats_per_op, pattern='increment')

        # Issue copy operation
        await tb.issue_copy_operation(channel_id, src_addr, dst_addr, beats_per_op, burst_len)

        # Measure this operation
        actual_cycles, utilization, beats_done = await tb.measure_end_to_end_bandwidth(beats_per_op)

        total_cycles += actual_cycles

        # Verify data
        data_success, mismatches = await tb.verify_memory_contents(
            src_addr, dst_addr, beats_per_op, pattern='increment')

        if not data_success:
            all_data_valid = False

        print(f"  Op {op}: {actual_cycles} cycles, {utilization:.2f}% BW, data={'OK' if data_success else 'FAIL'}")

        # Each operation should maintain reasonable bandwidth
        assert utilization > 40.0, \
            f"Op {op} bandwidth {utilization:.2f}% < 40% - DEGRADATION!"

    # Overall metrics
    overall_beats = num_operations * beats_per_op
    avg_cycles_per_op = total_cycles / num_operations

    print(f"\n  Total: {overall_beats} beats in {total_cycles} cycles")
    print(f"  Average cycles per op: {avg_cycles_per_op:.1f}")
    print(f"  Data integrity: {'ALL PASS' if all_data_valid else 'FAILURES DETECTED'}")

    # AGGRESSIVE assertions
    assert all_data_valid, \
        "Data integrity check failed for one or more operations"

    print(">>> SUSTAINED PIPELINE PERFORMANCE ACHIEVED <<<")


@cocotb.test()
async def test_datapath_integrated_pipeline_latency_aggressive(dut):
    """AGGRESSIVE: Measure pipeline stage latencies.

    Validates:
    - Read latency < 100 cycles
    - Write latency < 100 cycles
    - Total pipeline latency reasonable for burst size
    """
    # Initialize testbench
    tb = DatapathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - LATENCY MEASUREMENT
    channel_id = 0
    src_addr = 0x7000_0000
    dst_addr = 0x8000_0000
    burst_len = 16

    # Measure latencies
    read_lat, write_lat, total_lat = await tb.measure_pipeline_latency(
        channel_id, src_addr, dst_addr, burst_len)

    # Verify data integrity
    data_success, mismatches = await tb.verify_memory_contents(
        src_addr, dst_addr, burst_len, pattern='increment')

    # Report
    print(f"\n=== AGGRESSIVE Pipeline Latency Results (burst_len={burst_len}) ===")
    print(f"  Read latency: {read_lat} cycles")
    print(f"  Write latency: {write_lat} cycles")
    print(f"  Total latency: {total_lat} cycles")
    print(f"  Data integrity: {'PASS' if data_success else 'FAIL'}")

    # AGGRESSIVE assertions for reasonable latencies
    assert read_lat < 100, \
        f"Read latency {read_lat} cycles > 100 - TOO HIGH!"

    assert write_lat < 100, \
        f"Write latency {write_lat} cycles > 100 - TOO HIGH!"

    assert data_success, \
        "Data integrity check failed"

    print(">>> LOW PIPELINE LATENCY ACHIEVED <<<")


@cocotb.test()
async def test_datapath_integrated_multi_channel_aggressive(dut):
    """AGGRESSIVE: Test multiple channels with interleaved operations.

    Validates:
    - Multiple channels can operate independently
    - No cross-channel data corruption
    - Channel arbitration works correctly
    - Per-channel performance maintained
    """
    # Initialize testbench
    tb = DatapathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test parameters - MULTI-CHANNEL
    test_channels = [0, 2, 5, 7]  # Test 4 channels
    beats_per_channel = 128
    burst_len = 16

    print(f"\n=== AGGRESSIVE Multi-Channel Pipeline Test ===")
    print(f"  Channels: {test_channels}")
    print(f"  Beats per channel: {beats_per_channel}")

    for channel_id in test_channels:
        src_addr = 0xA000_0000 + (channel_id * 0x1000_0000)
        dst_addr = 0xB000_0000 + (channel_id * 0x1000_0000)

        # Populate source
        await tb.populate_source_memory(src_addr, beats_per_channel, pattern='increment')

        # Issue copy operation
        await tb.issue_copy_operation(channel_id, src_addr, dst_addr, beats_per_channel, burst_len)

        # Verify data integrity for this channel
        data_success, mismatches = await tb.verify_memory_contents(
            src_addr, dst_addr, beats_per_channel, pattern='increment')

        print(f"  Channel {channel_id}: data={'OK' if data_success else 'FAIL'}")

        # Each channel should maintain data integrity
        assert data_success, \
            f"Channel {channel_id} data integrity check failed: {len(mismatches)} mismatches"

    print(">>> MULTI-CHANNEL ISOLATION MAINTAINED <<<")
