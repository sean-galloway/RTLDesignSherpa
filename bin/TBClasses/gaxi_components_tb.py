#!/usr/bin/env python
"""
GAXITestbench class for testing GAXI Master/Slave/Monitor components

This class provides a flexible testbench for GAXI components with support for:
- Different signal modes (standard, multi_signal)
- Different handshaking modes (skid, fifo_mux, fifo_flop)
- Memory model integration
- Randomized delays
"""

import os
import logging
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, FallingEdge, Timer, ClockCycles
from cocotb_bus.scoreboard import Scoreboard
from cocotb.result import TestFailure

# Import GAXI components
from Components.gaxi_components import (
    GAXIMaster, GAXISlave, GAXIMonitor,
    gaxi_master_signals, gaxi_slave_signals,
    gaxi_master_default_constraints, gaxi_slave_default_constraints
)
from Components.gaxi_packet import GAXIPacket
from Components.flex_randomizer import FlexRandomizer

# Mapping of test modes to handshaking and signal configurations
TEST_MODE_MAP = {
    'standard': {'signal_mode': 'standard', 'handshake_mode': 'skid'},
    'multi_signal': {'signal_mode': 'multi_signal', 'handshake_mode': 'skid'},
    'fifo_mux': {'signal_mode': 'standard', 'handshake_mode': 'fifo_mux'},
    'fifo_flop': {'signal_mode': 'standard', 'handshake_mode': 'fifo_flop'},
    'skid_multi': {'signal_mode': 'multi_signal', 'handshake_mode': 'skid'},
    'fifo_mux_multi': {'signal_mode': 'multi_signal', 'handshake_mode': 'fifo_mux'},
    'fifo_flop_multi': {'signal_mode': 'multi_signal', 'handshake_mode': 'fifo_flop'}
}

# Mapping of handshake modes to DUT test_mode values
HANDSHAKE_TO_DUT_MODE = {
    'skid': 0,
    'fifo_mux': 1,
    'fifo_flop': 2
}

# Memory model for testing
class MemoryModel:
    """Memory model for testing memory integration"""
    def __init__(self, size=4096, bytes_per_line=4):
        self.memory = bytearray(size)
        self.size = size
        self.bytes_per_line = bytes_per_line
        
    def read(self, addr, length):
        """Read from memory"""
        if addr + length > self.size:
            raise ValueError(f"Address out of range: {addr} + {length} > {self.size}")
        return self.memory[addr:addr+length]
    
    def write(self, addr, data, strb=0xFF):
        """Write to memory with strobe support"""
        if addr + len(data) > self.size:
            raise ValueError(f"Address out of range: {addr} + {len(data)} > {self.size}")
        
        for i, b in enumerate(data):
            if strb & (1 << (i % 4)):
                self.memory[addr + i] = b
    
    def integer_to_bytearray(self, value, length):
        """Convert integer to bytearray (little-endian)"""
        result = bytearray(length)
        for i in range(length):
            result[i] = (value >> (i * 8)) & 0xFF
        return result
    
    def bytearray_to_integer(self, data):
        """Convert bytearray to integer (little-endian)"""
        result = 0
        for i, b in enumerate(data):
            result |= b << (i * 8)
        return result

# Test field configuration based on parameters
def create_field_config(data_width=32, ctrl_width=8):
    """Create field configuration based on parameters"""
    return {
        'addr': {
            'bits': 32,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (31, 2),  # Only bits 31:2 are used in FIFO
            'description': 'Address'
        },
        'data': {
            'bits': data_width,
            'default': 0,
            'format': 'hex',
            'display_width': data_width // 4,
            'active_bits': (data_width - 1, 0),
            'description': 'Data'
        },
        'ctrl': {
            'bits': ctrl_width,
            'default': 0,
            'format': 'hex',
            'display_width': ctrl_width // 4,
            'active_bits': (ctrl_width - 1, 0),
            'description': 'Control'
        }
    }

# Test fixture for GAXI components with loopback
class GAXITestbench:
    """Testbench for GAXI components with loopback"""
    def __init__(self, dut, test_mode='standard', use_memory=True, 
                randomize_delays=True, clock_period=10, data_width=32, ctrl_width=8):
        self.dut = dut
        self.use_memory = use_memory
        self.randomize_delays = randomize_delays
        self.clock_period = clock_period
        self.data_width = data_width
        self.ctrl_width = ctrl_width
        
        # Extract signal and handshake modes from test_mode
        if test_mode in TEST_MODE_MAP:
            config = TEST_MODE_MAP[test_mode]
            self.signal_mode = config['signal_mode']
            self.handshake_mode = config['handshake_mode']
        else:
            # Parse components if mode is not in the map
            parts = test_mode.split('_')
            if len(parts) >= 2 and 'multi' in parts:
                self.signal_mode = 'multi_signal'
                # Remove 'multi' to get handshake mode
                parts.remove('multi')
                self.handshake_mode = '_'.join(parts)
            else:
                # Default to standard signal mode
                self.signal_mode = 'standard'
                self.handshake_mode = test_mode
            
            # Validate handshake mode
            if self.handshake_mode not in ['skid', 'fifo_mux', 'fifo_flop']:
                self.log.warning(f"Unknown handshake mode: {self.handshake_mode}, defaulting to 'skid'")
                self.handshake_mode = 'skid'
                
        # Create logger
        self.log = logging.getLogger("gaxi_testbench")
        self.log.info(f"Initializing testbench with signal_mode={self.signal_mode}, handshake_mode={self.handshake_mode}")
                
        # Field configuration
        self.field_config = create_field_config(data_width, ctrl_width)
        
        # Memory model
        if use_memory:
            self.memory = MemoryModel(size=8192, bytes_per_line=data_width // 8)
        else:
            self.memory = None
        
        # Components
        self.master = None
        self.slave = None
        self.monitor = None
        
        # Packet queues for verification
        self.expected_packets = []
        self.received_packets = []
        
        # Scoreboard for automated verification
        self.scoreboard = Scoreboard(self.log)
        
        # Clock instance for DUT
        self.clock = None
    
    async def setup(self):
        """Setup the testbench based on signal and handshake modes"""
        # Start clock
        self.clock = Clock(self.dut.clk, self.clock_period, units="ns")
        cocotb.start_soon(self.clock.start())
        
        # Wait for clock stabilization
        await ClockCycles(self.dut.clk, 5)
        
        # Set DUT test_mode based on handshake mode
        if hasattr(self.dut, 'test_mode'):
            dut_mode = HANDSHAKE_TO_DUT_MODE.get(self.handshake_mode, 0)
            self.dut.test_mode.value = dut_mode
            self.log.info(f"Setting DUT test_mode to {dut_mode} for {self.handshake_mode} mode")
        
        # Setup randomizers based on config
        if self.randomize_delays:
            master_randomizer = FlexRandomizer({
                'valid_delay': ([[0, 0], [1, 5], [6, 15]], [6, 3, 1])
            })
            
            slave_randomizer = FlexRandomizer({
                'ready_delay': ([[0, 0], [1, 3], [4, 12]], [5, 4, 1])
            })
        else:
            # No delays
            master_randomizer = FlexRandomizer({
                'valid_delay': ([[0, 0]], [1])
            })
            
            slave_randomizer = FlexRandomizer({
                'ready_delay': ([[0, 0]], [1])
            })
        
        # Setup components based on signal mode and handshake mode
        self.setup_components(master_randomizer, slave_randomizer)
        
        # Set up monitor callback
        self.monitor._recv = self._monitor_callback
        
        # Start monitor
        cocotb.start_soon(self.monitor._monitor_recv())
        
        # Add scoreboard comparator
        self.scoreboard.add_interface(self, "gaxi_packets")
        
        # Reset the bus
        await self.reset_dut()
        
    def setup_components(self, master_randomizer, slave_randomizer):
        """Setup components based on mode configurations"""
        self.log.info(f"Setting up components with signal_mode={self.signal_mode}, handshake_mode={self.handshake_mode}")
        
        # Configure based on signal mode (standard vs multi_signal)
        if self.signal_mode == 'multi_signal':
            self._setup_multi_signal_components(master_randomizer, slave_randomizer)
        else:  # standard signal mode
            self._setup_standard_components(master_randomizer, slave_randomizer)
    
    def _setup_standard_components(self, master_randomizer, slave_randomizer):
        """Setup components in standard signal mode"""
        self.log.info("Setting up components in standard signal mode")
        
        # Standard signal parameters
        master_signals = gaxi_master_signals
        slave_signals = gaxi_slave_signals
        
        # Master
        self.master = GAXIMaster(
            self.dut,
            f"tb_master_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            signals=master_signals,
            field_config=self.field_config,
            memory_model=self.memory,
            randomizer=master_randomizer,
            log=self.log
        )
        
        # Slave - apply handshake mode
        self.slave = GAXISlave(
            self.dut,
            f"tb_slave_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            signals=slave_signals,
            field_config=self.field_config,
            memory_model=self.memory,
            randomizer=slave_randomizer,
            mode=self.handshake_mode,  # Apply handshake mode
            log=self.log
        )
        
        # Monitor - apply handshake mode
        self.monitor = GAXIMonitor(
            self.dut,
            f"tb_monitor_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            field_config=self.field_config,
            is_slave=False,  # Monitor master side
            mode=self.handshake_mode,  # Apply handshake mode
            log=self.log
        )
    
    def _setup_multi_signal_components(self, master_randomizer, slave_randomizer):
        """Setup components in multi-signal mode"""
        self.log.info("Setting up components in multi-signal mode")
        
        # Signal mappings for master
        master_signal_map = {
            'i_wr_valid': 'i_wr_valid',
            'o_wr_ready': 'o_wr_ready',
            'i_wr_data_addr': 'i_wr_addr',
            'i_wr_data_data': 'i_wr_data_data',
            'i_wr_data_ctrl': 'i_wr_ctrl'
        }
        
        # Signal mappings for slave
        slave_signal_map = {
            'o_rd_valid': 'o_rd_valid',
            'i_rd_ready': 'i_rd_ready',
            'o_rd_data_addr': 'o_rd_addr',
            'o_rd_data_data': 'o_rd_data_data',
            'o_rd_data_ctrl': 'o_rd_ctrl'
        }
        
        # Master
        self.master = GAXIMaster(
            self.dut,
            f"tb_multi_master_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            signal_map=master_signal_map,
            field_config=self.field_config,
            memory_model=self.memory,
            randomizer=master_randomizer,
            log=self.log
        )
        
        # Slave - apply handshake mode
        self.slave = GAXISlave(
            self.dut,
            f"tb_multi_slave_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            signal_map=slave_signal_map,
            field_config=self.field_config,
            memory_model=self.memory,
            randomizer=slave_randomizer,
            mode=self.handshake_mode,  # Apply handshake mode
            log=self.log
        )
        
        # Monitor - apply handshake mode
        self.monitor = GAXIMonitor(
            self.dut,
            f"tb_multi_monitor_{self.handshake_mode}",
            "",  # Prefix
            self.dut.clk,
            signal_map=master_signal_map,  # Use master signals for monitoring
            field_config=self.field_config,
            is_slave=False,
            mode=self.handshake_mode,  # Apply handshake mode
            log=self.log
        )
    
    async def reset_dut(self):
        """Reset the DUT and all components"""
        self.log.info("Resetting DUT and components")
        
        # Reset DUT
        if hasattr(self.dut, 'rst_n'):
            self.dut.rst_n.value = 0
        elif hasattr(self.dut, 'reset'):
            self.dut.reset.value = 1
        else:
            self.log.warning("No reset signal found on DUT")
            
        await ClockCycles(self.dut.clk, 5)
        
        if hasattr(self.dut, 'rst_n'):
            self.dut.rst_n.value = 1
        elif hasattr(self.dut, 'reset'):
            self.dut.reset.value = 0
            
        await ClockCycles(self.dut.clk, 5)
        
        # Reset components
        await self.master.reset_bus()
        await self.slave.reset_bus()
        
        self.log.info("Reset completed")
    
    def _monitor_callback(self, transaction):
        """Callback for monitor to process received transactions"""
        self.log.debug(f"Monitor received: {transaction.formatted(compact=True)}")
        self.received_packets.append(transaction)
        
        # Compare with expected packets
        if self.expected_packets:
            exp = self.expected_packets.pop(0)
            result = self.scoreboard.compare("gaxi_packets", transaction, exp)
            
            # Log comparison results
            if result:
                self.log.info(f"Packet comparison: MATCH")
            else:
                self.log.error(f"Packet comparison: MISMATCH")
                self.log.error(f"Expected: {exp.formatted()}")
                self.log.error(f"Received: {transaction.formatted()}")
        else:
            self.log.warning("Received unexpected transaction")
    
    async def send_and_verify_packet(self, packet):
        """Send a packet and verify it was received correctly"""
        self.log.info(f"Sending packet: {packet.formatted(compact=True)}")
        self.expected_packets.append(packet)
        await self.master.send(packet)
        
        # Wait for transmission to complete
        while self.master.transfer_busy:
            await RisingEdge(self.dut.clk)
        
        # Wait additional cycles based on handshake mode
        if self.handshake_mode == 'fifo_flop':
            # In fifo_flop mode, we need extra cycles for the data to propagate
            await ClockCycles(self.dut.clk, 10)
        else:
            # For other modes, fewer cycles are needed
            await ClockCycles(self.dut.clk, 5)
        
        # Check if packet was received
        if len(self.received_packets) < len(self.expected_packets):
            raise TestFailure("Packet not received by monitor")
    
    async def send_multiple_packets(self, num_packets):
        """Generate and send multiple packets"""
        self.log.info(f"Sending {num_packets} packets")
        
        test_packets = []
        
        # Create test packets
        for i in range(num_packets):
            packet = GAXIPacket(
                self.field_config,
                addr=0x1000 + (i * 4),
                data=0xABCD0000 + i,
                ctrl=i & 0xFF
            )
            test_packets.append(packet)
            self.expected_packets.append(packet)
        
        # Setup packet generator
        packet_idx = 0
        
        def packet_generator():
            nonlocal packet_idx
            if packet_idx < len(test_packets):
                packet = test_packets[packet_idx]
                packet_idx += 1
                return packet
            return None
        
        self.master.set_packet_generator(packet_generator)
        
        # Send all packets
        await self.master.send_packets(num_packets)
        
        # Wait for transmission to complete
        while self.master.transfer_busy:
            await RisingEdge(self.dut.clk)
        
        # Wait additional cycles based on handshake mode
        if self.handshake_mode == 'fifo_flop':
            # In fifo_flop mode, we need extra cycles for all data to propagate
            await ClockCycles(self.dut.clk, 15)
        else:
            # For other modes, fewer cycles are needed
            await ClockCycles(self.dut.clk, 10)
        
        # Check if all packets were received
        received_count = len(self.received_packets)
        expected_count = len(self.expected_packets) + num_packets
        if received_count != num_packets:
            raise TestFailure(f"Expected {num_packets} packets, received {received_count}")
        
        self.log.info(f"Successfully sent and received {num_packets} packets")
        return test_packets

    async def test_memory_integration(self):
        """Test memory model integration with read/write operations"""
        if not self.memory:
            self.log.info("Memory model not enabled, skipping memory test")
            return True
            
        self.log.info("Testing memory integration")
        
        # Write to memory through master
        write_addr = 0x2000
        write_data = 0x87654321
        
        write_packet = GAXIPacket(
            self.field_config,
            addr=write_addr,
            data=write_data,
            ctrl=0x01  # Write command
        )
        
        # Send write packet
        await self.master.send(write_packet)
        while self.master.transfer_busy:
            await RisingEdge(self.dut.clk)
        
        # Verify memory contents directly
        mem_data = self.memory.read(write_addr, self.memory.bytes_per_line)
        read_value = self.memory.bytearray_to_integer(mem_data)
        
        if read_value != write_data:
            self.log.error(f"Memory write failed: expected 0x{write_data:X}, got 0x{read_value:X}")
            return False
        
        # Read back through slave
        read_packet = GAXIPacket(
            self.field_config,
            addr=write_addr,
            data=0,  # Will be filled from memory
            ctrl=0x02  # Read command
        )
        
        # Manually trigger memory read through slave
        read_data = self.slave._read_from_memory(read_packet)
        
        if read_data != write_data:
            self.log.error(f"Memory read failed: expected 0x{write_data:X}, got 0x{read_data:X}")
            return False
            
        self.log.info("Memory integration test passed")
        return True
