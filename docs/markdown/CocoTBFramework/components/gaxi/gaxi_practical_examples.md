# GAXI Framework Practical Examples

This document provides practical, end-to-end examples of using the GAXI framework for different verification scenarios. These examples showcase how to integrate different components and implement common testing patterns.

## Example 1: Basic Skid Buffer Verification

This example demonstrates how to verify a simple skid buffer using the GAXI framework.

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard


@cocotb.test()
async def test_skid_buffer(dut):
    """Test a basic skid buffer with randomized valid/ready signals"""
    
    # Create a clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field_dict('data', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data value'
    })
    
    # Create randomizers
    master_randomizer = FlexRandomizer({
        'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
    })
    slave_randomizer = FlexRandomizer({
        'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
    })
    
    # Create master, slave and monitors
    master = GAXIMaster(
        dut, 'Master', '', dut.clk,
        field_config=field_config,
        randomizer=master_randomizer,
        signal_map={
            'm2s_valid': 'i_valid',
            's2m_ready': 'o_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'i_data'
        }
    )
    
    slave = GAXISlave(
        dut, 'Slave', '', dut.clk,
        field_config=field_config,
        randomizer=slave_randomizer,
        signal_map={
            'm2s_valid': 'o_valid',
            's2m_ready': 'i_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'o_data'
        }
    )
    
    master_monitor = GAXIMonitor(
        dut, 'MasterMonitor', '', dut.clk,
        field_config=field_config,
        is_slave=False,
        signal_map={
            'm2s_valid': 'i_valid',
            's2m_ready': 'o_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'i_data'
        }
    )
    
    slave_monitor = GAXIMonitor(
        dut, 'SlaveMonitor', '', dut.clk,
        field_config=field_config,
        is_slave=True,
        signal_map={
            'm2s_valid': 'o_valid',
            's2m_ready': 'i_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'o_data'
        }
    )
    
    # Create scoreboard
    scoreboard = GAXIScoreboard('SkidScoreboard', field_config)
    
    # Add callbacks to monitor for scoreboard integration
    def master_callback(transaction):
        scoreboard.add_expected(transaction)
    
    def slave_callback(transaction):
        scoreboard.add_actual(transaction)
    
    master_monitor.add_callback(master_callback)
    slave_monitor.add_callback(slave_callback)
    
    # Reset the interfaces
    await master.reset_bus()
    await slave.reset_bus()
    
    # Send test packets
    num_packets = 100
    for i in range(num_packets):
        packet = GAXIPacket(field_config)
        packet.data = i
        await master.send(packet)
    
    # Wait for all transactions to complete
    while master.transfer_busy:
        await RisingEdge(dut.clk)
    
    # Wait additional cycles to ensure all data is received
    for _ in range(50):
        await RisingEdge(dut.clk)
    
    # Check scoreboard results
    result = scoreboard.check_complete()
    assert result, f"Scoreboard check failed: {scoreboard.error_count} errors"
    
    # Clear the queues
    master_monitor.clear_queue()
    slave_monitor.clear_queue()
```

## Example 2: Memory-Mapped Interface Testing

This example shows how to test a memory-mapped interface using the GAXI framework with memory integration.

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler


@cocotb.test()
async def test_memory_interface(dut):
    """Test a memory-mapped interface with automatic memory handling"""
    
    # Create a clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field_dict('cmd', {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Command (0=read, 1=write)'
    })
    field_config.add_field_dict('addr', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Address'
    })
    field_config.add_field_dict('data', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data'
    })
    field_config.add_field_dict('strb', {
        'bits': 4,
        'default': 0xF,
        'format': 'bin',
        'display_width': 4,
        'active_bits': (3, 0),
        'description': 'Byte strobe'
    })
    
    # Create memory model
    memory_model = MemoryModel(
        num_lines=1024,    # 1024 lines
        bytes_per_line=4,  # 4 bytes per line (32-bit)
        log=dut._log
    )
    
    # Define memory field mapping
    memory_fields = {
        'addr': 'addr',  # Address field name
        'data': 'data',  # Data field name
        'strb': 'strb'   # Strobe field name
    }
    
    # Create master and slave with memory integration
    master = GAXIMaster(
        dut, 'Master', '', dut.clk,
        field_config=field_config,
        memory_model=memory_model,
        memory_fields=memory_fields,
        signal_map={
            'm2s_valid': 'i_valid',
            's2m_ready': 'o_ready'
        },
        optional_signal_map={
            'm2s_pkt_cmd': 'i_cmd',
            'm2s_pkt_addr': 'i_addr',
            'm2s_pkt_data': 'i_data',
            'm2s_pkt_strb': 'i_strb'
        },
        multi_sig=True
    )
    
    slave = GAXISlave(
        dut, 'Slave', '', dut.clk,
        field_config=field_config,
        memory_model=memory_model,
        memory_fields=memory_fields,
        signal_map={
            'm2s_valid': 'o_valid',
            's2m_ready': 'i_ready'
        },
        optional_signal_map={
            'm2s_pkt_cmd': 'o_cmd',
            'm2s_pkt_addr': 'o_addr',
            'm2s_pkt_data': 'o_data',
            'm2s_pkt_strb': 'o_strb'
        },
        multi_sig=True
    )
    
    # Create command handler
    command_handler = GAXICommandHandler(master, slave, memory_model)
    await command_handler.start()
    
    # Write test pattern to memory
    for i in range(10):
        addr = i * 4
        data = 0xA5000000 | addr
        
        # Create write packet
        write_packet = GAXIPacket(field_config)
        write_packet.cmd = 1  # Write command
        write_packet.addr = addr
        write_packet.data = data
        write_packet.strb = 0xF  # All bytes enabled
        
        # Send packet
        await master.send(write_packet)
    
    # Wait for writes to complete
    while master.transfer_busy:
        await RisingEdge(dut.clk)
    
    # Additional delay to ensure all transactions complete
    for _ in range(20):
        await RisingEdge(dut.clk)
    
    # Read back and verify data
    for i in range(10):
        addr = i * 4
        expected_data = 0xA5000000 | addr
        
        # Create read packet
        read_packet = GAXIPacket(field_config)
        read_packet.cmd = 0  # Read command
        read_packet.addr = addr
        
        # Send packet
        await master.send(read_packet)
        
        # Wait for read to complete
        while master.transfer_busy:
            await RisingEdge(dut.clk)
        
        # Check slave received queue for response
        await RisingEdge(dut.clk)
        
        # Verify data was correctly read back
        assert len(slave.received_queue) > 0, f"No response received for read at address 0x{addr:08X}"
        response = slave.received_queue.popleft()
        assert response.data == expected_data, f"Data mismatch at address 0x{addr:08X}: expected 0x{expected_data:08X}, got 0x{response.data:08X}"
    
    # Get memory statistics
    master_stats = master.get_memory_stats()
    slave_stats = slave.get_memory_stats()
    
    print(f"Master memory writes: {master_stats['writes']}")
    print(f"Slave memory reads: {slave_stats['reads']}")
    
    # Stop command handler
    await command_handler.stop()
```

## Example 3: Data Collector Verification

This example demonstrates how to test a data collection module that combines data from multiple sources using the GAXI framework.

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock
import random

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.flex_randomizer import FlexRandomizer
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket


class DataCollectScoreboard:
    """Simple scoreboard for data collector verification"""
    def __init__(self, log=None):
        self.log = log
        self.input_queues = {'A': [], 'B': [], 'C': [], 'D': []}
        self.expected_queue = []
        self.actual_queue = []
        self.error_count = 0
    
    def add_input(self, channel, data):
        """Add input data from a specific channel"""
        self.input_queues[channel].append(data)
        
        # Check if we have enough data to form an output packet
        if len(self.input_queues[channel]) >= 4:
            # Take 4 data items from this channel
            data0 = self.input_queues[channel].pop(0)
            data1 = self.input_queues[channel].pop(0)
            data2 = self.input_queues[channel].pop(0)
            data3 = self.input_queues[channel].pop(0)
            
            # Create expected output
            expected = {
                'id': ord(channel),  # Use ASCII value of channel letter
                'data0': data0,
                'data1': data1,
                'data2': data2,
                'data3': data3
            }
            self.expected_queue.append(expected)
    
    def add_actual(self, packet):
        """Add actual output packet"""
        actual = {
            'id': packet.id,
            'data0': packet.data0,
            'data1': packet.data1,
            'data2': packet.data2,
            'data3': packet.data3
        }
        self.actual_queue.append(actual)
    
    def check(self):
        """Check for matches between expected and actual outputs"""
        while self.expected_queue and self.actual_queue:
            expected = self.expected_queue.pop(0)
            actual = self.actual_queue.pop(0)
            
            if expected['id'] != actual['id']:
                self.log.error(f"ID mismatch: expected {expected['id']}, got {actual['id']}")
                self.error_count += 1
            
            if expected['data0'] != actual['data0']:
                self.log.error(f"data0 mismatch: expected {expected['data0']}, got {actual['data0']}")
                self.error_count += 1
            
            if expected['data1'] != actual['data1']:
                self.log.error(f"data1 mismatch: expected {expected['data1']}, got {actual['data1']}")
                self.error_count += 1
            
            if expected['data2'] != actual['data2']:
                self.log.error(f"data2 mismatch: expected {expected['data2']}, got {actual['data2']}")
                self.error_count += 1
            
            if expected['data3'] != actual['data3']:
                self.log.error(f"data3 mismatch: expected {expected['data3']}, got {actual['data3']}")
                self.error_count += 1
        
        return self.error_count == 0


@cocotb.test()
async def test_data_collector(dut):
    """Test a data collector module that combines data from multiple sources"""
    
    # Create a clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Create input field configuration
    input_field_config = FieldConfig()
    input_field_config.add_field_dict('data', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data value'
    })
    input_field_config.add_field_dict('id', {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Channel ID'
    })
    
    # Create output field configuration
    output_field_config = FieldConfig()
    output_field_config.add_field_dict('data0', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data0 value'
    })
    output_field_config.add_field_dict('data1', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data1 value'
    })
    output_field_config.add_field_dict('data2', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data2 value'
    })
    output_field_config.add_field_dict('data3', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data3 value'
    })
    output_field_config.add_field_dict('id', {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Channel ID'
    })
    
    # Create randomizers
    input_randomizer = FlexRandomizer({
        'valid_delay': ([[0, 0], [1, 5]], [8, 2])  # Mostly back-to-back
    })
    output_randomizer = FlexRandomizer({
        'ready_delay': ([[0, 0], [1, 3]], [8, 2])  # Mostly back-to-back
    })
    
    # Create input masters
    master_a = GAXIMaster(
        dut, 'MasterA', '', dut.clk,
        field_config=input_field_config,
        randomizer=input_randomizer,
        signal_map={
            'm2s_valid': 'i_a_valid',
            's2m_ready': 'o_a_ready'
        },
        optional_signal_map={
            'm2s_pkt_data': 'i_a_data',
            'm2s_pkt_id': 'i_a_id'
        },
        multi_sig=True
    )
    
    master_b = GAXIMaster(
        dut, 'MasterB', '', dut.clk,
        field_config=input_field_config,
        randomizer=input_randomizer,
        signal_map={
            'm2s_valid': 'i_b_valid',
            's2m_ready': 'o_b_ready'
        },
        optional_signal_map={
            'm2s_pkt_data': 'i_b_data',
            'm2s_pkt_id': 'i_b_id'
        },
        multi_sig=True
    )
    
    master_c = GAXIMaster(
        dut, 'MasterC', '', dut.clk,
        field_config=input_field_config,
        randomizer=input_randomizer,
        signal_map={
            'm2s_valid': 'i_c_valid',
            's2m_ready': 'o_c_ready'
        },
        optional_signal_map={
            'm2s_pkt_data': 'i_c_data',
            'm2s_pkt_id': 'i_c_id'
        },
        multi_sig=True
    )
    
    master_d = GAXIMaster(
        dut, 'MasterD', '', dut.clk,
        field_config=input_field_config,
        randomizer=input_randomizer,
        signal_map={
            'm2s_valid': 'i_d_valid',
            's2m_ready': 'o_d_ready'
        },
        optional_signal_map={
            'm2s_pkt_data': 'i_d_data',
            'm2s_pkt_id': 'i_d_id'
        },
        multi_sig=True
    )
    
    # Create output slave
    slave_e = GAXISlave(
        dut, 'SlaveE', '', dut.clk,
        field_config=output_field_config,
        randomizer=output_randomizer,
        signal_map={
            'm2s_valid': 'o_e_valid',
            's2m_ready': 'i_e_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'o_e_data'
        }
    )
    
    # Create output monitor
    monitor_e = GAXIMonitor(
        dut, 'MonitorE', '', dut.clk,
        field_config=output_field_config,
        is_slave=True,
        signal_map={
            'm2s_valid': 'o_e_valid',
            's2m_ready': 'i_e_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'o_e_data'
        }
    )
    
    # Create scoreboard
    scoreboard = DataCollectScoreboard(log=dut._log)
    
    # Set up weights for the arbiter
    dut.i_weight_a.value = 8
    dut.i_weight_b.value = 8
    dut.i_weight_c.value = 8
    dut.i_weight_d.value = 8
    
    # Add callback for output monitoring
    def output_callback(transaction):
        scoreboard.add_actual(transaction)
    
    monitor_e.add_callback(output_callback)
    
    # Reset the interfaces
    await master_a.reset_bus()
    await master_b.reset_bus()
    await master_c.reset_bus()
    await master_d.reset_bus()
    await slave_e.reset_bus()
    
    # Send 40 packets on each channel
    packets_per_channel = 40
    for i in range(packets_per_channel):
        # Channel A (ID: 0xAA)
        packet_a = GAXIPacket(input_field_config)
        packet_a.id = 0xAA
        packet_a.data = 0xA0000000 | i
        await master_a.send(packet_a)
        scoreboard.add_input('A', packet_a.data)
        
        # Channel B (ID: 0xBB)
        packet_b = GAXIPacket(input_field_config)
        packet_b.id = 0xBB
        packet_b.data = 0xB0000000 | i
        await master_b.send(packet_b)
        scoreboard.add_input('B', packet_b.data)
        
        # Channel C (ID: 0xCC)
        packet_c = GAXIPacket(input_field_config)
        packet_c.id = 0xCC
        packet_c.data = 0xC0000000 | i
        await master_c.send(packet_c)
        scoreboard.add_input('C', packet_c.data)
        
        # Channel D (ID: 0xDD)
        packet_d = GAXIPacket(input_field_config)
        packet_d.id = 0xDD
        packet_d.data = 0xD0000000 | i
        await master_d.send(packet_d)
        scoreboard.add_input('D', packet_d.data)
    
    # Wait for all masters to finish
    while (master_a.transfer_busy or master_b.transfer_busy or 
          master_c.transfer_busy or master_d.transfer_busy):
        await RisingEdge(dut.clk)
    
    # Wait for all outputs to be processed
    # Each channel produces packets_per_channel/4 outputs (10 per channel)
    expected_outputs = (packets_per_channel * 4) // 4
    for _ in range(500):  # Maximum wait time
        if len(monitor_e.observed_queue) >= expected_outputs:
            break
        await RisingEdge(dut.clk)
    
    # Check the results
    result = scoreboard.check()
    assert result, f"Data collector test failed with {scoreboard.error_count} errors"
```

## Example 4: Using Enhanced Components and Command Handler

This example demonstrates how to use enhanced GAXI components and command handler for more advanced verification scenarios.

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_sequence import GAXISequence
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler
from CocoTBFramework.tbclasses.gaxi.gaxi_enhancements import EnhancedGAXIMaster, EnhancedGAXISlave


@cocotb.test()
async def test_enhanced_components(dut):
    """Test enhanced GAXI components and command handler"""
    
    # Create a clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field_dict('cmd', {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Command (0=read, 1=write)'
    })
    field_config.add_field_dict('addr', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Address'
    })
    field_config.add_field_dict('data', {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Data'
    })
    
    # Create memory model
    memory_model = MemoryModel(
        num_lines=1024,
        bytes_per_line=4,
        log=dut._log
    )
    
    # Create base components
    master = GAXIMaster(
        dut, 'Master', '', dut.clk,
        field_config=field_config,
        signal_map={
            'm2s_valid': 'i_valid',
            's2m_ready': 'o_ready'
        },
        optional_signal_map={
            'm2s_pkt_cmd': 'i_cmd',
            'm2s_pkt_addr': 'i_addr',
            'm2s_pkt_data': 'i_data'
        },
        multi_sig=True
    )
    
    slave = GAXISlave(
        dut, 'Slave', '', dut.clk,
        field_config=field_config,
        signal_map={
            'm2s_valid': 'o_valid',
            's2m_ready': 'i_ready'
        },
        optional_signal_map={
            'm2s_pkt_cmd': 'o_cmd',
            'm2s_pkt_addr': 'o_addr',
            'm2s_pkt_data': 'o_data'
        },
        multi_sig=True
    )
    
    # Create enhanced components
    enhanced_master = EnhancedGAXIMaster(master, memory_model, log=dut._log)
    enhanced_slave = EnhancedGAXISlave(slave, memory_model, log=dut._log)
    
    # Create command handler
    command_handler = GAXICommandHandler(master, slave, memory_model, log=dut._log)
    
    # Start processors
    await enhanced_master.start_processor()
    await enhanced_slave.start_processor()
    await command_handler.start()
    
    # Create a test sequence
    sequence = GAXISequence("memory_test", field_config)
    
    # Add write transactions to sequence
    for i in range(10):
        addr = i * 4
        data = 0x12345670 + i
        
        # Add write transaction
        sequence.add_transaction({
            'cmd': 1,      # Write
            'addr': addr,
            'data': data
        }, delay=0)
    
    # Add read transactions to sequence with dependencies
    for i in range(10):
        addr = i * 4
        
        # Add read transaction dependent on corresponding write
        sequence.add_transaction_with_dependency({
            'cmd': 0,      # Read
            'addr': addr,
            'data': 0      # Will be filled by memory model
        }, delay=0, depends_on_index=i)
    
    # Process the sequence through command handler
    response_map = await command_handler.process_sequence(sequence)
    
    # Check read responses
    for i in range(10, 20):  # Read transactions are at indexes 10-19
        response = response_map[i]
        addr = (i - 10) * 4
        expected_data = 0x12345670 + (i - 10)
        
        # Verify data was correctly read back
        assert response.data == expected_data, f"Data mismatch at address 0x{addr:08X}: expected 0x{expected_data:08X}, got 0x{response.data:08X}"
    
    # Use enhanced master for direct memory operations
    await enhanced_master.write(0x100, 0xABCDEF01)
    data = await enhanced_master.read(0x100)
    assert data == 0xABCDEF01, f"Direct memory operation failed: expected 0xABCDEF01, got 0x{data:08X}"
    
    # Use enhanced slave with custom callbacks
    received_callbacks = []
    
    def read_callback(addr, packet):
        received_callbacks.append(('read', addr))
        packet.data = 0x87654321  # Custom response data
    
    def write_callback(addr, data, packet):
        received_callbacks.append(('write', addr, data))
    
    enhanced_slave.set_read_callback(read_callback)
    enhanced_slave.set_write_callback(write_callback)
    
    # Send a transaction directly to the enhanced slave
    test_packet = GAXIPacket(field_config)
    test_packet.cmd = 0  # Read
    test_packet.addr = 0x200
    test_packet.data = 0
    
    await enhanced_slave.process_request(test_packet)
    
    # Verify callback was called
    assert ('read', 0x200) in received_callbacks, "Read callback was not called"
    assert test_packet.data == 0x87654321, f"Callback didn't set data correctly: expected 0x87654321, got 0x{test_packet.data:08X}"
    
    # Get memory and transaction statistics
    master_stats = master.get_memory_stats()
    slave_stats = slave.get_memory_stats()
    cmd_stats = command_handler.get_stats()
    
    print(f"Master memory operations: {master_stats}")
    print(f"Slave memory operations: {slave_stats}")
    print(f"Command handler statistics: {cmd_stats}")
    
    # Stop processors
    await enhanced_master.stop_processor()
    await enhanced_slave.stop_processor()
    await command_handler.stop()
```

## Example 5: Factory Functions for Quick Setup

This example shows how to use the GAXI factory functions to quickly set up a verification environment.

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.clock import Clock

from CocoTBFramework.components.field_config import FieldConfig
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.gaxi.gaxi_factories import (
    create_gaxi_components, get_default_field_config
)
from CocoTBFramework.components.gaxi.gaxi_command_handler import GAXICommandHandler


@cocotb.test()
async def test_factory_setup(dut):
    """Test setting up verification environment using factory functions"""
    
    # Create a clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    await RisingEdge(dut.clk)
    dut.rst_n.value = 1
    
    # Create field configuration
    field_config = get_default_field_config(data_width=32)
    
    # Create memory model
    memory_model = MemoryModel(
        num_lines=1024,
        bytes_per_line=4,
        log=dut._log
    )
    
    # Create all components in one call
    components = create_gaxi_components(
        dut, dut.clk,
        title_prefix="Test",
        field_config=field_config,
        memory_model=memory_model,
        signal_map={
            'm2s_valid': 'i_valid',
            's2m_ready': 'o_ready'
        },
        optional_signal_map={
            'm2s_pkt': 'i_data'
        }
    )
    
    # Extract components
    master = components['master']
    slave = components['slave']
    master_monitor = components['master_monitor']
    slave_monitor = components['slave_monitor']
    scoreboard = components['scoreboard']
    
    # Create a command handler
    command_handler = GAXICommandHandler(master, slave, memory_model, log=dut._log)
    await command_handler.start()
    
    # Add callbacks to monitors for scoreboard integration
    def master_callback(transaction):
        scoreboard.add_expected(transaction)
    
    def slave_callback(transaction):
        scoreboard.add_actual(transaction)
    
    master_monitor.add_callback(master_callback)
    slave_monitor.add_callback(slave_callback)
    
    # Send test packets
    for i in range(20):
        packet = GAXIPacket(field_config)
        packet.data = i
        await master.send(packet)
    
    # Wait for all transactions to complete
    while master.transfer_busy:
        await RisingEdge(dut.clk)
    
    # Wait additional cycles to ensure all data is received
    for _ in range(20):
        await RisingEdge(dut.clk)
    
    # Check scoreboard results
    result = scoreboard.check_complete()
    assert result, f"Scoreboard check failed: {scoreboard.error_count} errors"
    
    # Stop command handler
    await command_handler.stop()
```

## Tips for Effective GAXI Testing

1. **Start Simple**: Begin with simple test cases and build up to more complex scenarios
2. **Reuse Components**: Create reusable sequences and component configurations
3. **Memory Integration**: Use memory models for automated data handling in memory-mapped interfaces
4. **Randomization**: Configure randomizers appropriately for realistic test coverage
5. **Command Handlers**: Use command handlers for coordinating complex test scenarios
6. **Monitors and Callbacks**: Set up monitors and callbacks for scoreboard integration
7. **Statistics Collection**: Monitor component statistics to identify performance issues
8. **Signal Mapping**: Provide explicit signal mappings for clarity
9. **Factory Functions**: Use factory functions for quick and consistent setup
10. **Enhanced Components**: Use enhanced components for higher-level functionality when appropriate

These examples demonstrate the flexibility and power of the GAXI framework for verifying a wide range of AXI-style interfaces and components. The modular architecture allows for easy adaptation to different design requirements, while the built-in utilities simplify common verification tasks.

## Navigation

[↑ GAXI Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
