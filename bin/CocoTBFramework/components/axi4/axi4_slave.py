"""
AXI4 Slave for Both Read and Write Transactions

This slave provides AXI4 functionality for both read and write operations
following the same "thin wrapper" design pattern as AXI4Master.

Key Features:
- Thin wrapper coordinating multiple GAXI components
- Handles AW/W/B write transactions with proper coordination
- Handles AR/R read transactions with burst support
- Memory model integration for data storage/retrieval
- Transaction ID management and matching
- Delegates signal handling to underlying GAXI components
- Same design patterns as AXI4Master
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time
from collections import defaultdict, deque
from typing import Dict, List, Optional, Any, Callable

from ..shared.field_config import FieldConfig, FieldDefinition
from ..shared.memory_model import MemoryModel
from .axi4_packet import AXI4Packet
from .axi4_timing_config import AXI4TimingConfig
from .axi4_randomization_config import AXI4RandomizationConfig


class AXI4Slave:
    """
    AXI4 Slave - Thin wrapper coordinating multiple GAXI components.
    
    Provides AXI4-specific response methods while delegating actual
    signal handling to individual GAXI components created by the factory.

    Implements tight coordination between channels:
    - AW/W/B coordination for write transactions
    - AR/R coordination for read transactions
    - Memory model integration
    """

    def __init__(self, channel_components, timing_config=None, protocol_randomizer=None,
                 memory_model=None, inorder=False, log=None, **kwargs):
        """
        Initialize AXI4 Slave with pre-created GAXI channel components.

        Args:
            channel_components: Dict of channel components {"AW": component, "W": component, ...}
            timing_config: AXI4TimingConfig for timing randomization
            protocol_randomizer: AXI4RandomizationConfig for response field values
            memory_model: Memory model for transaction processing
            inorder: Whether to enforce in-order responses
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
        self.aw_slave = self.channel_components.get('AW')
        self.w_slave = self.channel_components.get('W')
        self.b_master = self.channel_components.get('B')
        self.ar_slave = self.channel_components.get('AR')
        self.r_master = self.channel_components.get('R')

        # AXI4 transaction tracking
        self.active_writes = {}  # awid -> {aw_packet, w_packets, ready_for_response}
        self.active_reads = {}   # arid -> {ar_packet, response_pending}

        # Response queues (for inorder mode)
        self.write_response_queue = deque()
        self.read_response_queue = deque()

        # Statistics
        self.stats = {
            'write_requests': 0,
            'read_requests': 0,
            'write_responses': 0,
            'read_responses': 0,
            'memory_operations': 0,
            'coordination_events': 0
        }

        # Set up channel coordination
        self._setup_channel_coordination()

        if self.log:
            self.log.info(f"AXI4Slave created with channels: {self.channels}, inorder: {self.inorder}")

    def _setup_channel_coordination(self):
        """Set up coordination callbacks between related channels."""
        # Set up write path coordination: AW + W -> B
        if self.aw_slave:
            self.aw_slave.add_recv_callback(self._handle_aw_packet)
        if self.w_slave:
            self.w_slave.add_recv_callback(self._handle_w_packet)

        # Set up read path coordination: AR -> R
        if self.ar_slave:
            self.ar_slave.add_recv_callback(self._handle_ar_packet)

        if self.log:
            self.log.debug("Channel coordination callbacks set up")

    # Write transaction coordination

    def _handle_aw_packet(self, aw_packet):
        """Handle AW channel packet - start write transaction tracking."""
        awid = getattr(aw_packet, 'awid', 0)

        # Start write transaction tracking
        if awid not in self.active_writes:
            self.active_writes[awid] = {
                'aw_packet': aw_packet,
                'w_packets': [],
                'ready_for_response': False,
                'start_time': get_sim_time()
            }

        self.stats['write_requests'] += 1
        self.stats['coordination_events'] += 1

        if self.log:
            self.log.debug(f"AW packet received: ID={awid}, ADDR=0x{getattr(aw_packet, 'awaddr', 0):08x}")

    def _handle_w_packet(self, w_packet):
        """Handle W channel packet - accumulate write data and trigger response when complete."""
        # Find corresponding AW transaction (simplified matching - use first active write)
        # In sophisticated implementation, context-based matching would be used
        if self.active_writes:
            awid = list(self.active_writes.keys())[0]  # Simplified matching

            if awid in self.active_writes:
                # Add W packet to transaction
                self.active_writes[awid]['w_packets'].append(w_packet)

                # Process write to memory
                aw_packet = self.active_writes[awid]['aw_packet']
                beat_index = len(self.active_writes[awid]['w_packets']) - 1
                
                # Calculate address for this beat
                addr = getattr(aw_packet, 'awaddr', 0) + (beat_index * (self._get_data_width() // 8))
                data = getattr(w_packet, 'wdata', 0)
                strb = getattr(w_packet, 'wstrb', (1 << (self.data_width // 8)) - 1)

                # Store in memory model
                self.memory_model.write(addr, data, strb)
                self.stats['memory_operations'] += 1

                # Check if write transaction is complete
                wlast = getattr(w_packet, 'wlast', True)
                if wlast:
                    self.active_writes[awid]['ready_for_response'] = True
                    # Trigger B response
                    cocotb.start_soon(self._send_write_response(awid))

                if self.log:
                    self.log.debug(f"W packet: ADDR=0x{addr:08x}, DATA=0x{data:08x}, LAST={wlast}")

    async def _send_write_response(self, awid):
        """Send B channel response for completed write transaction."""
        if not self.b_master:
            if self.log:
                self.log.warning("No B channel available for write response")
            return

        if awid in self.active_writes and self.active_writes[awid]['ready_for_response']:
            # Apply response timing
            delay = self.timing_config.get_slave_delay() if hasattr(self.timing_config, 'get_slave_delay') else 1
            if delay > 0:
                await Timer(delay, "ns")

            # Create B response packet
            b_packet = AXI4Packet.create_b_packet(
                bid=awid,
                bresp=0  # OKAY response
            )
            
            # Apply protocol randomization to response fields
            self.protocol_randomizer.randomize_packet(b_packet)

            # Send B response
            await self.b_master.send(b_packet)

            # Clean up completed transaction
            del self.active_writes[awid]
            self.stats['write_responses'] += 1

            if self.log:
                self.log.debug(f"B response sent: ID={awid}")

    # Read transaction coordination

    def _handle_ar_packet(self, ar_packet):
        """Handle AR channel packet - process read request and send R response(s)."""
        arid = getattr(ar_packet, 'arid', 0)
        araddr = getattr(ar_packet, 'araddr', 0)
        arlen = getattr(ar_packet, 'arlen', 0)

        # Start read transaction tracking
        self.active_reads[arid] = {
            'ar_packet': ar_packet,
            'response_pending': True,
            'start_time': get_sim_time()
        }

        self.stats['read_requests'] += 1
        self.stats['coordination_events'] += 1

        # Trigger R response(s)
        cocotb.start_soon(self._send_read_responses(arid, araddr, arlen))

        if self.log:
            self.log.debug(f"AR packet received: ID={arid}, ADDR=0x{araddr:08x}, LEN={arlen}")

    async def _send_read_responses(self, arid, araddr, arlen):
        """Send R channel response(s) for read transaction."""
        if not self.r_master:
            if self.log:
                self.log.warning("No R channel available for read response")
            return

        # Calculate number of beats
        num_beats = arlen + 1

        for beat in range(num_beats):
            # Apply response timing
            delay = self.timing_config.get_slave_delay() if hasattr(self.timing_config, 'get_slave_delay') else 2
            if delay > 0:
                await Timer(delay, "ns")

            # Calculate address for this beat
            addr = araddr + (beat * (self.data_width // 8))
            
            # Read data from memory model
            data = self.memory_model.read(addr)
            self.stats['memory_operations'] += 1

            # Create R response packet
            r_packet = AXI4Packet.create_r_packet(
                rid=arid,
                rdata=data,
                rresp=0,  # OKAY response
                rlast=1 if (beat == num_beats - 1) else 0
            )
            
            # Apply protocol randomization to response fields
            self.protocol_randomizer.randomize_packet(r_packet)

            # Send R response
            await self.r_master.send(r_packet)
            self.stats['read_responses'] += 1

            if self.log:
                self.log.debug(f"R response: ID={arid}, ADDR=0x{addr:08x}, DATA=0x{data:08x}, LAST={r_packet.rlast}")

        # Clean up completed transaction
        if arid in self.active_reads:
            del self.active_reads[arid]

    # High-level transaction processing methods

    async def process_write_transaction(self, aw_packet, w_packets):
        """
        Process a complete write transaction (for external coordination).
        
        Args:
            aw_packet: AXI4 AW packet
            w_packets: List of AXI4 W packets
            
        Returns:
            AXI4 B packet response
        """
        awid = getattr(aw_packet, 'awid', 0)
        awaddr = getattr(aw_packet, 'awaddr', 0)

        # Process all write beats
        for beat_index, w_packet in enumerate(w_packets):
            addr = awaddr + (beat_index * (self._get_data_width() // 8))
            data = getattr(w_packet, 'wdata', 0)
            strb = getattr(w_packet, 'wstrb', (1 << (self.data_width // 8)) - 1)
            
            self.memory_model.write(addr, data, strb)
            self.stats['memory_operations'] += 1

        # Create response
        b_packet = AXI4Packet.create_b_packet(
            bid=awid,
            bresp=0  # OKAY response
        )
        
        # Apply protocol randomization to response fields
        self.protocol_randomizer.randomize_packet(b_packet)

        self.stats['write_responses'] += 1
        return b_packet

    async def process_read_transaction(self, ar_packet):
        """
        Process a read transaction (for external coordination).
        
        Args:
            ar_packet: AXI4 AR packet
            
        Returns:
            List of AXI4 R packets
        """
        arid = getattr(ar_packet, 'arid', 0)
        araddr = getattr(ar_packet, 'araddr', 0)
        arlen = getattr(ar_packet, 'arlen', 0)

        # Generate R responses
        r_packets = []
        num_beats = arlen + 1

        for beat in range(num_beats):
            addr = araddr + (beat * (self._get_data_width() // 8))
            data = self.memory_model.read(addr)
            self.stats['memory_operations'] += 1

            r_packet = AXI4Packet.create_r_packet(
                rid=arid,
                rdata=data,
                rresp=0,  # OKAY response
                rlast=1 if (beat == num_beats - 1) else 0
            )
            
            # Apply protocol randomization to response fields
            self.protocol_randomizer.randomize_packet(r_packet)
            
            r_packets.append(r_packet)

        self.stats['read_responses'] += len(r_packets)
        return r_packets

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
            'slave_stats': self.stats.copy(),
            'channel_stats': {},
            'active_transactions': {
                'writes': len(self.active_writes),
                'reads': len(self.active_reads)
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
        """Start the slave (compatibility method)."""
        # The actual work is done by underlying GAXI components
        # This method exists for interface compatibility
        if self.log:
            self.log.info(f"Started AXI4 Slave with channels: {self.channels}")

    async def stop(self):
        """Stop the slave (compatibility method)."""
        # The actual work is done by underlying GAXI components
        # This method exists for interface compatibility
        if self.log:
            self.log.info(f"Stopped AXI4 Slave")
