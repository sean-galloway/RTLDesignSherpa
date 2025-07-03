"""
AXI4 Master - Thin wrapper coordinating multiple GAXI components.

This master provides AXI4 functionality following the same "thin wrapper" 
design pattern as AXI4Slave, with improved parameter interface.

Key Features:
- Thin wrapper coordinating multiple GAXI components
- Handles AW/W/B write transactions with proper coordination
- Handles AR/R read transactions with burst support
- Memory model integration for transaction tracking
- Transaction ID management and matching
- Delegates signal handling to underlying GAXI components
- Consistent design patterns with AXI4Slave
"""

import cocotb
from collections import defaultdict, deque
from typing import Dict, List, Optional, Any, Callable
from cocotb.triggers import RisingEdge, Event
from cocotb.utils import get_sim_time

from ..shared.field_config import FieldConfig, FieldDefinition
from ..shared.memory_model import MemoryModel
from .axi4_packet import AXI4Packet
from .axi4_timing_config import AXI4TimingConfig
from .axi4_randomization_config import AXI4RandomizationConfig


class AXI4Master:
    """
    AXI4 Master - Thin wrapper coordinating multiple GAXI components.

    Provides AXI4-specific transaction methods while delegating actual
    signal handling to individual GAXI components created by the factory.

    Implements tight coordination between channels:
    - AW/W coordination for write transactions
    - AR/R coordination for read transactions
    - Same-clock assertion capability for W with AW
    """

    def __init__(self, channel_components, timing_config=None, protocol_randomizer=None,
                 memory_model=None, inorder=False, log=None, **kwargs):
        """
        Initialize AXI4 Master with pre-created GAXI channel components.

        Args:
            channel_components: Dict of channel components {"AW": component, "W": component, ...}
            timing_config: AXI4TimingConfig for timing randomization
            protocol_randomizer: AXI4RandomizationConfig for field values
            memory_model: Memory model for transaction tracking
            inorder: Whether to enforce in-order transactions
            log: Logger instance
            **kwargs: Additional arguments
        """
        self.channel_components = channel_components
        self.channels = list(channel_components.keys())
        self.log = log

        # Store configurations
        self.timing_config = timing_config or AXI4TimingConfig()
        self.protocol_randomizer = protocol_randomizer or AXI4RandomizationConfig()
        self.memory_model = memory_model or MemoryModel(log=log)
        self.inorder = inorder

        # Easy access to individual channels (may be None if channel not present)
        self.aw_master = self.channel_components.get('AW')
        self.w_master = self.channel_components.get('W')
        self.b_slave = self.channel_components.get('B')
        self.ar_master = self.channel_components.get('AR')
        self.r_slave = self.channel_components.get('R')

        # AXI4 transaction tracking
        self.pending_writes = {}  # awid -> {aw_packet, w_packets, b_packet, complete}
        self.pending_reads = {}   # arid -> {ar_packet, r_packets, complete}
        self.next_write_id = 0
        self.next_read_id = 0

        # Coordination state
        self.write_coordination = {}  # awid -> coordination state
        self.read_coordination = {}   # arid -> coordination state

        # Transaction queues (for inorder mode)
        self.write_transaction_queue = deque()
        self.read_transaction_queue = deque()

        # Statistics
        self.stats = {
            'write_transactions': 0,
            'read_transactions': 0,
            'write_bursts': 0,
            'read_bursts': 0,
            'coordination_events': 0,
            'memory_operations': 0
        }

        # Set up channel coordination
        self._setup_channel_coordination()

        if self.log:
            self.log.info(f"AXI4Master created with channels: {self.channels}, inorder: {self.inorder}")

    def _setup_channel_coordination(self):
        """Set up coordination callbacks between related channels."""
        # Set up write response coordination: B -> completion tracking
        if self.b_slave:
            self.b_slave.add_recv_callback(self._handle_b_packet)

        # Set up read response coordination: R -> completion tracking
        if self.r_slave:
            self.r_slave.add_recv_callback(self._handle_r_packet)

        if self.log:
            self.log.debug("Channel coordination callbacks set up")

    # Response handling coordination

    def _handle_b_packet(self, b_packet):
        """Handle B channel packet - complete write transaction."""
        bid = getattr(b_packet, 'bid', 0)

        if bid in self.pending_writes:
            self.pending_writes[bid]['b_packet'] = b_packet
            self.pending_writes[bid]['complete'] = True
            self.pending_writes[bid]['end_time'] = get_sim_time()

            # Transaction complete - could trigger callbacks here
            self._complete_write_transaction(bid)

        self.stats['coordination_events'] += 1

        if self.log:
            self.log.debug(f"B response received: ID={bid}")

    def _handle_r_packet(self, r_packet):
        """Handle R channel packet - complete read transaction."""
        rid = getattr(r_packet, 'rid', 0)

        if rid in self.pending_reads:
            self.pending_reads[rid]['r_packets'].append(r_packet)

            # Check if this completes the burst
            rlast = getattr(r_packet, 'rlast', True)
            if rlast:
                self.pending_reads[rid]['complete'] = True
                self.pending_reads[rid]['end_time'] = get_sim_time()
                self._complete_read_transaction(rid)

        self.stats['coordination_events'] += 1

        if self.log:
            self.log.debug(f"R response received: ID={rid}, LAST={getattr(r_packet, 'rlast', 0)}")

    def _complete_write_transaction(self, awid):
        """Complete write transaction and update statistics."""
        self.stats['write_transactions'] += 1
        
        # Track in memory model if address/data available
        if awid in self.pending_writes:
            aw_packet = self.pending_writes[awid].get('aw_packet')
            w_packets = self.pending_writes[awid].get('w_packets', [])
            
            if aw_packet and w_packets:
                awaddr = getattr(aw_packet, 'awaddr', 0)
                for i, w_packet in enumerate(w_packets):
                    addr = awaddr + (i * self._get_data_width() // 8)
                    data = getattr(w_packet, 'wdata', 0)
                    strb = getattr(w_packet, 'wstrb', 0xFF)
                    self.memory_model.write(addr, data, strb)
                    self.stats['memory_operations'] += 1

        if self.log:
            self.log.debug(f"Write transaction {awid} completed")

        # Clean up completed transaction
        if awid in self.write_coordination:
            del self.write_coordination[awid]
        if awid in self.pending_writes:
            del self.pending_writes[awid]

    def _complete_read_transaction(self, arid):
        """Complete read transaction and update statistics."""
        self.stats['read_transactions'] += 1
        
        # Track in memory model if address available
        if arid in self.pending_reads:
            ar_packet = self.pending_reads[arid].get('ar_packet')
            r_packets = self.pending_reads[arid].get('r_packets', [])
            
            if ar_packet and r_packets:
                araddr = getattr(ar_packet, 'araddr', 0)
                for i, r_packet in enumerate(r_packets):
                    addr = araddr + (i * self._get_data_width() // 8)
                    data = getattr(r_packet, 'rdata', 0)
                    self.memory_model.read(addr)  # Track read access
                    self.stats['memory_operations'] += 1

        if self.log:
            self.log.debug(f"Read transaction {arid} completed")

        # Clean up completed transaction
        if arid in self.read_coordination:
            del self.read_coordination[arid]
        if arid in self.pending_reads:
            del self.pending_reads[arid]

    # High-level transaction methods

    async def write_single(self, addr: int, data: int, **kwargs) -> Any:
        """
        Perform a single AXI4 write transaction.

        This coordinates both AW and W phases, with proper ID management.
        """
        if not (self.aw_master and self.w_master):
            raise RuntimeError("Write channels (AW, W) not available")

        # Generate transaction ID
        awid = self.next_write_id
        self.next_write_id = (self.next_write_id + 1) % (1 << self._get_id_width())

        # Apply timing delays
        aw_delay = self.timing_config.get_master_delay() if hasattr(self.timing_config, 'get_master_delay') else 0
        w_delay = aw_delay  # Same delay for coordinated W

        # Create AW packet with protocol randomization
        aw_packet = AXI4Packet.create_aw_packet(
            awid=awid,
            awaddr=addr,
            awlen=0,  # Single beat
            awsize=self._calculate_size(),
            **kwargs
        )
        self.protocol_randomizer.randomize_packet(aw_packet)

        # Create W packet with protocol randomization
        w_packet = AXI4Packet.create_w_packet(
            wdata=data,
            wstrb=(1 << (self._get_data_width() // 8)) - 1,  # All bytes valid
            wlast=1,
            **kwargs
        )
        self.protocol_randomizer.randomize_packet(w_packet)

        # Track transaction
        self.pending_writes[awid] = {
            'aw_packet': aw_packet,
            'w_packets': [w_packet],
            'complete': False,
            'start_time': get_sim_time()
        }

        # Send AW and W (coordination handled by underlying components)
        await self.aw_master.send(aw_packet)
        await self.w_master.send(w_packet)

        # Wait for B response if available
        if self.b_slave:
            return await self._wait_for_write_response(awid)

        return awid

    async def read_single(self, addr: int, **kwargs) -> Any:
        """
        Perform a single AXI4 read transaction.

        This sends AR and waits for R response.
        """
        if not self.ar_master:
            raise RuntimeError("Read address channel (AR) not available")

        # Generate transaction ID
        arid = self.next_read_id
        self.next_read_id = (self.next_read_id + 1) % (1 << self._get_id_width())

        # Apply timing delays
        ar_delay = self.timing_config.get_master_delay() if hasattr(self.timing_config, 'get_master_delay') else 0

        # Create AR packet with protocol randomization
        ar_packet = AXI4Packet.create_ar_packet(
            arid=arid,
            araddr=addr,
            arlen=0,  # Single beat
            arsize=self._calculate_size(),
            **kwargs
        )
        self.protocol_randomizer.randomize_packet(ar_packet)

        # Track transaction
        self.pending_reads[arid] = {
            'ar_packet': ar_packet,
            'r_packets': [],
            'complete': False,
            'start_time': get_sim_time()
        }

        # Send AR
        await self.ar_master.send(ar_packet)

        # Wait for R response if available
        if self.r_slave:
            return await self._wait_for_read_response(arid)

        return arid

    async def write_burst(self, addr: int, data_list: List[int], **kwargs) -> Any:
        """
        Perform an AXI4 write burst transaction.
        
        Args:
            addr: Starting address
            data_list: List of data values to write
            **kwargs: Additional AXI4 fields
            
        Returns:
            Transaction ID or B response
        """
        if not (self.aw_master and self.w_master):
            raise RuntimeError("Write channels (AW, W) not available")

        burst_len = len(data_list)
        if burst_len == 0:
            raise ValueError("Data list cannot be empty")

        # Generate transaction ID
        awid = self.next_write_id
        self.next_write_id = (self.next_write_id + 1) % (1 << self._get_id_width())

        # Create AW packet for burst
        aw_packet = AXI4Packet.create_aw_packet(
            awid=awid,
            awaddr=addr,
            awlen=burst_len - 1,  # AXI4 uses length-1 encoding
            awsize=self._calculate_size(),
            **kwargs
        )
        self.protocol_randomizer.randomize_packet(aw_packet)

        # Create W packets for burst
        w_packets = []
        for i, data in enumerate(data_list):
            w_packet = AXI4Packet.create_w_packet(
                wdata=data,
                wstrb=(1 << (self._get_data_width() // 8)) - 1,
                wlast=1 if (i == burst_len - 1) else 0,
                **kwargs
            )
            self.protocol_randomizer.randomize_packet(w_packet)
            w_packets.append(w_packet)

        # Track transaction
        self.pending_writes[awid] = {
            'aw_packet': aw_packet,
            'w_packets': w_packets,
            'complete': False,
            'start_time': get_sim_time()
        }

        # Send AW first
        await self.aw_master.send(aw_packet)

        # Send W packets
        for w_packet in w_packets:
            await self.w_master.send(w_packet)

        self.stats['write_bursts'] += 1

        # Wait for B response if available
        if self.b_slave:
            return await self._wait_for_write_response(awid)

        return awid

    async def read_burst(self, addr: int, burst_len: int, **kwargs) -> Any:
        """
        Perform an AXI4 read burst transaction.
        
        Args:
            addr: Starting address
            burst_len: Number of beats to read
            **kwargs: Additional AXI4 fields
            
        Returns:
            Transaction ID or R responses
        """
        if not self.ar_master:
            raise RuntimeError("Read address channel (AR) not available")

        if burst_len == 0:
            raise ValueError("Burst length cannot be zero")

        # Generate transaction ID
        arid = self.next_read_id
        self.next_read_id = (self.next_read_id + 1) % (1 << self._get_id_width())

        # Create AR packet for burst
        ar_packet = AXI4Packet.create_ar_packet(
            arid=arid,
            araddr=addr,
            arlen=burst_len - 1,  # AXI4 uses length-1 encoding
            arsize=self._calculate_size(),
            **kwargs
        )
        self.protocol_randomizer.randomize_packet(ar_packet)

        # Track transaction
        self.pending_reads[arid] = {
            'ar_packet': ar_packet,
            'r_packets': [],
            'complete': False,
            'start_time': get_sim_time()
        }

        # Send AR
        await self.ar_master.send(ar_packet)

        self.stats['read_bursts'] += 1

        # Wait for R responses if available
        if self.r_slave:
            return await self._wait_for_read_response(arid)

        return arid

    async def _wait_for_write_response(self, awid):
        """Wait for write response with timeout."""
        timeout_cycles = 1000
        for _ in range(timeout_cycles):
            if awid in self.pending_writes and self.pending_writes[awid]['complete']:
                return self.pending_writes[awid]['b_packet']
            await RisingEdge(self.aw_master.clock)

        raise TimeoutError(f"Write response timeout for ID {awid}")

    async def _wait_for_read_response(self, arid):
        """Wait for read response with timeout."""
        timeout_cycles = 1000
        for _ in range(timeout_cycles):
            if arid in self.pending_reads and self.pending_reads[arid]['complete']:
                return self.pending_reads[arid]['r_packets']
            await RisingEdge(self.ar_master.clock)

        raise TimeoutError(f"Read response timeout for ID {arid}")

    # Utility methods

    def _calculate_size(self):
        """Calculate AXI size field from data width."""
        return (self._get_data_width() // 8).bit_length() - 1

    def _get_data_width(self):
        """Get data width from channel components or default."""
        # Try to get from components, fallback to sensible default
        for component in self.channel_components.values():
            if hasattr(component, 'data_width'):
                return component.data_width
        return 32  # Default data width

    def _get_id_width(self):
        """Get ID width from channel components or default."""
        # Try to get from components, fallback to sensible default
        for component in self.channel_components.values():
            if hasattr(component, 'id_width'):
                return component.id_width
        return 8  # Default ID width

    def get_stats(self) -> Dict[str, Any]:
        """Get comprehensive statistics."""
        combined_stats = {
            'master_stats': self.stats.copy(),
            'channel_stats': {},
            'pending_transactions': {
                'writes': len(self.pending_writes),
                'reads': len(self.pending_reads)
            },
            'memory_stats': self.memory_model.get_stats() if hasattr(self.memory_model, 'get_stats') else {}
        }

        # Gather stats from individual channel components
        for channel, component in self.channel_components.items():
            if hasattr(component, 'get_stats'):
                combined_stats['channel_stats'][channel] = component.get_stats()

        return combined_stats

    def reset_stats(self):
        """Reset statistics counters."""
        for key in self.stats:
            self.stats[key] = 0

    async def start(self):
        """Start the master (compatibility method)."""
        # The actual work is done by underlying GAXI components
        # This method exists for interface compatibility
        if self.log:
            self.log.info(f"Started AXI4 Master with channels: {self.channels}")

    async def stop(self):
        """Stop the master (compatibility method)."""
        # The actual work is done by underlying GAXI components
        # This method exists for interface compatibility
        if self.log:
            self.log.info(f"Stopped AXI4 Master")