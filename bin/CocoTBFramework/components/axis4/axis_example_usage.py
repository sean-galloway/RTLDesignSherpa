# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axis_example_usage
# Purpose: AXIS Components Example Usage
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Components Example Usage

This example demonstrates how to use all four AXIS components
(Master, Slave, Monitor, and packet handling) in a typical testbench.

The API is designed to be similar to AXI4 for consistency while
being optimized for stream protocol characteristics.
"""

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.clock import Clock

# Import AXIS components - similar to AXI4 imports
from CocoTBFramework.components.axis import (
    create_axis_master,
    create_axis_slave,
    create_axis_monitor,
    create_axis_testbench,
    AXISPacket,
    AXISFieldConfigs,
    create_axis_packet
)


@cocotb.test()
async def test_axis_basic_transfer(dut):
    """Basic AXIS transfer test using all four components."""
    
    # Create clock
    clock = Clock(dut.aclk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Wait for reset
    await ClockCycles(dut.aclk, 10)
    
    # Method 1: Create individual components (similar to AXI4 pattern)
    master_components = create_axis_master(
        dut=dut,
        clock=dut.aclk,
        prefix="m_axis_",
        data_width=32,
        id_width=8,
        dest_width=4,
        user_width=1,
        log=cocotb.logging.getLogger("axis_master")
    )
    
    slave_components = create_axis_slave(
        dut=dut,
        clock=dut.aclk,
        prefix="s_axis_",
        data_width=32,
        id_width=8,
        dest_width=4,
        user_width=1,
        log=cocotb.logging.getLogger("axis_slave")
    )
    
    monitor_components = create_axis_monitor(
        dut=dut,
        clock=dut.aclk,
        prefix="m_axis_",
        data_width=32,
        id_width=8,
        dest_width=4,
        user_width=1,
        is_slave=False,  # Monitor master side
        log=cocotb.logging.getLogger("axis_monitor")
    )
    
    # Extract the actual component instances
    axis_master = master_components['interface']
    axis_slave = slave_components['interface']
    axis_monitor = monitor_components['interface']
    
    # Method 2: Create complete testbench setup
    # axis_tb = create_axis_testbench(
    #     dut=dut,
    #     clock=dut.aclk,
    #     master_prefix="m_axis_",
    #     slave_prefix="s_axis_",
    #     data_width=32,
    #     log=cocotb.logging.getLogger("axis_tb")
    # )
    
    # Configure slave to be always ready
    axis_slave.set_ready_always(True)
    
    # Wait a bit more for initialization
    await ClockCycles(dut.aclk, 10)
    
    # Test 1: Send single beat
    dut._log.info("=== Test 1: Single Beat Transfer ===")
    success = await axis_master.send_single_beat(
        data=0xDEADBEEF,
        last=1,
        id=0x55,
        dest=0x3,
        user=0x1
    )
    assert success, "Single beat transfer failed"
    
    # Wait for transfer to complete
    await ClockCycles(dut.aclk, 10)
    
    # Test 2: Send stream data (multiple beats)
    dut._log.info("=== Test 2: Multi-Beat Stream ===")
    stream_data = [0x12345678, 0x9ABCDEF0, 0x11223344, 0x55667788]
    success = await axis_master.send_stream_data(
        data_list=stream_data,
        id=0xAA,
        dest=0x2,
        user=0x0,
        auto_last=True  # Automatically set TLAST on final transfer
    )
    assert success, "Multi-beat stream transfer failed"
    
    # Wait for transfers to complete
    await ClockCycles(dut.aclk, 20)
    
    # Test 3: Send complete frame
    dut._log.info("=== Test 3: Complete Frame ===")
    frame_data = [0x00010203, 0x04050607, 0x08090A0B, 0x0C0D0E0F]
    success = await axis_master.send_frame(
        frame_data=frame_data,
        frame_id=0x10,
        dest=0x1,
        user=0x1
    )
    assert success, "Frame transfer failed"
    
    # Wait for frame to complete
    await ClockCycles(dut.aclk, 20)
    
    # Test 4: Create and send custom packets
    dut._log.info("=== Test 4: Custom Packets ===")
    
    # Create field configuration
    field_config = AXISFieldConfigs.create_default_axis_config(data_width=32)
    
    # Create custom packet using factory function
    packet1 = create_axis_packet(
        data=0xCAFEBABE,
        strb=0xF,  # All 4 bytes valid
        last=0,    # Not last
        id=0x77,
        dest=0x4,
        user=0x1,
        field_config=field_config
    )
    
    # Create packet manually
    packet2 = AXISPacket(field_config=field_config)
    packet2.data = 0xFEEDFACE
    packet2.strb = 0xF
    packet2.last = 1  # This is the last packet
    packet2.id = 0x77
    packet2.dest = 0x4
    packet2.user = 0x1
    
    # Send custom packets
    success = await axis_master.send_packet(packet1)
    assert success, "Custom packet 1 failed"
    
    success = await axis_master.send_packet(packet2)
    assert success, "Custom packet 2 failed"
    
    # Wait for packets to complete
    await ClockCycles(dut.aclk, 20)
    
    # Test 5: Apply backpressure and test flow control
    dut._log.info("=== Test 5: Backpressure Test ===")
    
    # Apply random backpressure
    axis_slave.apply_backpressure(probability=0.5, min_cycles=1, max_cycles=3)
    
    # Send data with backpressure
    backpressure_data = [0x10101010, 0x20202020, 0x30303030]
    success = await axis_master.send_stream_data(
        data_list=backpressure_data,
        id=0x99,
        auto_last=True
    )
    assert success, "Backpressure test failed"
    
    # Wait for completion
    await ClockCycles(dut.aclk, 50)
    
    # Test 6: Wait for specific events
    dut._log.info("=== Test 6: Event Waiting ===")
    
    # Wait for slave to receive frames
    initial_frames = axis_slave.frames_received
    
    # Send a frame
    test_frame = [0xAAAABBBB, 0xCCCCDDDD]
    await axis_master.send_frame(test_frame, frame_id=0xFF)
    
    # Wait for frame to be received
    frame_received = await axis_slave.wait_for_frame(timeout_cycles=100)
    assert frame_received, "Frame reception timeout"
    
    # Wait for monitor to observe packets
    initial_packets = axis_monitor.packets_observed
    await axis_master.send_single_beat(data=0x12341234, last=1)
    
    packet_observed = await axis_monitor.wait_for_packets(1, timeout_cycles=50)
    assert packet_observed, "Packet observation timeout"
    
    # Final wait
    await ClockCycles(dut.aclk, 50)
    
    # Print comprehensive statistics
    dut._log.info("=== Final Statistics ===")
    
    # Master statistics
    master_stats = axis_master.get_stats()
    dut._log.info(f"Master Stats: {master_stats}")
    
    # Slave statistics  
    slave_stats = axis_slave.get_stats()
    dut._log.info(f"Slave Stats: {slave_stats}")
    
    # Monitor statistics
    monitor_stats = axis_monitor.get_stats()
    dut._log.info(f"Monitor Stats: {monitor_stats}")
    
    # Verify basic functionality
    assert master_stats['packets_sent'] > 0, "No packets sent by master"
    assert slave_stats['packets_received'] > 0, "No packets received by slave"
    assert monitor_stats['packets_observed'] > 0, "No packets observed by monitor"
    
    # Check for frame completion
    assert slave_stats['frames_received'] > 0, "No frames received"
    assert monitor_stats['frames_observed'] > 0, "No frames observed"
    
    dut._log.info("All AXIS tests completed successfully!")


@cocotb.test()
async def test_axis_simple_components(dut):
    """Test simple AXIS components with minimal sideband signals."""
    
    # Create clock
    clock = Clock(dut.aclk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Wait for reset
    await ClockCycles(dut.aclk, 10)
    
    # Import simple component creators
    from CocoTBFramework.components.axis import (
        create_simple_axis_master,
        create_simple_axis_slave
    )
    
    # Create simple components (no ID, DEST, USER signals)
    simple_master = create_simple_axis_master(
        dut=dut,
        clock=dut.aclk,
        prefix="simple_axis_",
        data_width=32,
        log=cocotb.logging.getLogger("simple_master")
    )
    
    simple_slave = create_simple_axis_slave(
        dut=dut,
        clock=dut.aclk,
        prefix="simple_axis_",
        data_width=32,
        log=cocotb.logging.getLogger("simple_slave")
    )
    
    # Configure slave
    simple_slave.set_ready_always(True)
    
    # Wait for initialization
    await ClockCycles(dut.aclk, 10)
    
    # Send simple data (only data, strb, last)
    simple_data = [0x11111111, 0x22222222, 0x33333333]
    success = await simple_master.send_stream_data(simple_data)
    assert success, "Simple stream transfer failed"
    
    # Wait and check
    await ClockCycles(dut.aclk, 20)
    
    stats = simple_slave.get_stats()
    assert stats['packets_received'] > 0, "Simple slave received no packets"
    
    dut._log.info("Simple AXIS components test completed!")


@cocotb.test()
async def test_axis_manual_signal_mapping(dut):
    """Test AXIS components with manual signal mapping."""
    
    # Create clock
    clock = Clock(dut.aclk, 10, units="ns") 
    cocotb.start_soon(clock.start())
    
    await ClockCycles(dut.aclk, 10)
    
    # Import signal mapping utility
    from CocoTBFramework.components.axis import get_axis_signal_map
    
    # Create manual signal mapping
    master_signal_map = get_axis_signal_map(prefix="custom_m_", direction="master")
    slave_signal_map = get_axis_signal_map(prefix="custom_s_", direction="slave")
    
    # Create components with manual signal mapping
    master_with_mapping = create_axis_master(
        dut=dut,
        clock=dut.aclk,
        prefix="",  # Empty prefix since we're using manual mapping
        data_width=32,
        signal_map=master_signal_map,
        log=cocotb.logging.getLogger("mapped_master")
    )
    
    # This demonstrates how to override automatic signal discovery
    # when your DUT has non-standard signal names
    
    dut._log.info("Manual signal mapping test completed!")


# Example of packet manipulation utilities
def demonstrate_packet_utilities():
    """
    Demonstrate AXIS packet manipulation utilities.
    This would typically be called from within a test.
    """
    
    # Create field configuration
    field_config = AXISFieldConfigs.create_default_axis_config(data_width=32)
    
    # Create packet
    packet = AXISPacket(field_config=field_config)
    
    # Set data using bytes
    byte_data = [0xAA, 0xBB, 0xCC, 0xDD]
    packet.set_data_bytes(byte_data)
    
    # Get data back as bytes
    retrieved_bytes = packet.get_data_bytes()
    print(f"Byte data: {[hex(b) for b in retrieved_bytes]}")
    
    # Check packet properties
    print(f"Is last: {packet.is_last()}")
    print(f"Byte count: {packet.get_byte_count()}")
    print(f"Packet: {packet}")
    
    # Packet representations
    print(f"String: {str(packet)}")
    print(f"Repr: {repr(packet)}")
    
    return packet


# Example testbench configuration patterns
AXIS_CONFIG_EXAMPLES = {
    "minimal": {
        "data_width": 32,
        "id_width": 0,
        "dest_width": 0, 
        "user_width": 0
    },
    
    "standard": {
        "data_width": 32,
        "id_width": 8,
        "dest_width": 4,
        "user_width": 1
    },
    
    "wide_data": {
        "data_width": 512,
        "id_width": 8,
        "dest_width": 4,
        "user_width": 32
    },
    
    "multi_stream": {
        "data_width": 64,
        "id_width": 16,  # Support many streams
        "dest_width": 8,  # Many destinations
        "user_width": 8
    }
}


def create_axis_config_from_example(config_name):
    """Create AXIS configuration from predefined examples."""
    if config_name not in AXIS_CONFIG_EXAMPLES:
        raise ValueError(f"Unknown config: {config_name}")
    
    config = AXIS_CONFIG_EXAMPLES[config_name]
    return AXISFieldConfigs.create_axis_config_from_hw_params(**config)
