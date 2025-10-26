# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISMaster
# Purpose: AXIS Master - Stream protocol master implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Master - Stream protocol master implementation

This module provides AXIS Master functionality using GAXI infrastructure.
Similar API to AXI4Master but adapted for stream protocol.
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time
from collections import deque

from ..gaxi.gaxi_master import GAXIMaster
from ..shared.master_statistics import MasterStatistics
from .axis_packet import AXISPacket
from .axis_field_configs import AXISFieldConfigs


class AXISMaster(GAXIMaster):
    """
    AXIS Master component for driving AXI4-Stream protocol.
    
    Inherits common functionality from GAXIComponentBase:
    - Signal resolution and data driving setup
    - Unified field configuration handling
    - Memory model integration
    - Statistics and logging patterns
    
    AXIS-specific features:
    - Stream data transmission
    - Flow control with backpressure
    - Packet/frame boundary handling with TLAST
    - Optional ID and destination routing
    """

    def __init__(self, dut, title, prefix, clock, field_config=None,
                timeout_cycles=1000, mode='skid',
                bus_name='', pkt_prefix='',
                multi_sig=False, randomizer=None, memory_model=None,
                log=None, super_debug=False, pipeline_debug=False,
                signal_map=None, **kwargs):
        """
        Initialize AXIS Master.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "m_axis_", "fub_axis_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            timeout_cycles: Maximum cycles to wait for ready
            mode: Protocol mode ('skid', 'blocking', etc.)
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for timing
            memory_model: Optional memory model
            log: Logger instance
            super_debug: Enable detailed debugging
            pipeline_debug: Enable pipeline debugging
            signal_map: Optional manual signal mapping
            **kwargs: Additional configuration
        """
        # Create default field config if none provided
        if field_config is None:
            field_config = AXISFieldConfigs.create_default_axis_config()

        # Initialize base component
        super().__init__(
            dut=dut, title=title, prefix=prefix, clock=clock,
            field_config=field_config, protocol_type='axis_master',
            mode=mode, bus_name=bus_name, pkt_prefix=pkt_prefix,
            multi_sig=multi_sig, randomizer=randomizer,
            memory_model=memory_model, log=log,
            super_debug=super_debug, signal_map=signal_map, **kwargs
        )

        # AXIS Master specific attributes
        self.timeout_cycles = timeout_cycles
        self.pipeline_debug = pipeline_debug
        
        # Transaction queue and state
        self._send_queue = deque()
        self._active_transaction = None
        self._busy = False
        
        # Statistics tracking
        self.stats = MasterStatistics()
        # AXIS-specific counters (not in base MasterStatistics)
        self.packets_sent = 0
        self.frames_sent = 0
        
        # Complete initialization
        self.complete_base_initialization()

        if self.log:
            self.log.info(f"AXISMaster '{self.title}' initialized: "
                         f"mode={self.mode}, timeout={self.timeout_cycles} cycles")

    async def send_stream_data(self, data_list, id=0, dest=0, user=0, 
                              auto_last=True, strb_list=None):
        """
        Send stream data with automatic packet management.
        
        Args:
            data_list: List of data values to send
            id: Stream ID for all transfers
            dest: Destination for all transfers  
            user: User signal for all transfers
            auto_last: Automatically set TLAST on final transfer
            strb_list: Optional list of strobe values (if None, auto-generate)
        
        Returns:
            True if successful, False if timeout
        """
        if not data_list:
            return True
            
        packets = []
        for i, data in enumerate(data_list):
            # Determine if this is the last transfer
            is_last = auto_last and (i == len(data_list) - 1)
            
            # Get strobe value
            strb = None
            if strb_list and i < len(strb_list):
                strb = strb_list[i]
            
            # Create packet
            packet = AXISPacket(field_config=self.field_config)
            packet.data = data
            packet.last = 1 if is_last else 0
            packet.id = id
            packet.dest = dest
            packet.user = user
            
            # Set strobe
            if strb is not None:
                packet.strb = strb
            else:
                # Auto-generate full strobe
                if 'strb' in self.field_config:
                    strb_bits = self.field_config['strb'].bits
                    packet.strb = (1 << strb_bits) - 1
            
            packets.append(packet)
        
        # Send all packets
        for packet in packets:
            success = await self.send_packet(packet)
            if not success:
                return False
        
        return True

    async def send_packet(self, packet):
        """
        Send a single AXIS packet.
        
        Args:
            packet: AXISPacket to send
        
        Returns:
            True if successful, False if timeout
        """
        if self.log and self.super_debug:
            self.log.debug(f"AXISMaster '{self.title}': Sending packet {packet}")
        
        # Add to send queue
        self._send_queue.append(packet)
        
        # Start driver if not already running
        if not self._busy:
            return await self._drive_transaction()
        
        return True

    async def _drive_transaction(self):
        """Drive a single transaction on the bus."""
        if not self._send_queue:
            return True
        
        self._busy = True
        packet = self._send_queue.popleft()
        self._active_transaction = packet
        
        try:
            # Prepare data for driving
            if self.data_driver:
                data_dict = self._packet_to_data_dict(packet)
                
                # Apply timing randomization
                if self.randomizer:
                    delay = self.randomizer.get_delay('valid_delay')
                    if delay > 0:
                        await Timer(delay * 1000, units='ps')  # Convert to ps
                
                # Drive the data
                success = await self._drive_with_timeout(data_dict)
                
                # Update statistics
                if success:
                    self.packets_sent += 1
                    self.stats.record_transaction_complete(0, packet.get_byte_count())  # 0 for start_time since we don't track it here
                    if packet.is_last():
                        self.frames_sent += 1

                    if self.log and self.super_debug:
                        self.log.debug(f"AXISMaster '{self.title}': "
                                     f"Successfully sent packet {packet}")
                else:
                    self.stats.record_timeout()
                    if self.log:
                        self.log.warning(f"AXISMaster '{self.title}': "
                                       f"Timeout sending packet {packet}")
                
                # Write to memory model if available
                if self.memory_model:
                    self.write_to_memory_unified(packet)
                
                return success
            else:
                if self.log:
                    self.log.error(f"AXISMaster '{self.title}': No data driver available")
                return False
                
        except Exception as e:
            if self.log:
                self.log.error(f"AXISMaster '{self.title}': Exception in _drive_transaction: {e}")
            self.stats.record_transaction_failed("exception", str(e))
            return False
        finally:
            self._active_transaction = None
            self._busy = False

    async def _drive_with_timeout(self, data_dict):
        """Drive data with timeout protection."""
        timeout_count = 0
        
        while timeout_count < self.timeout_cycles:
            try:
                # Use data driver to send the data
                await self.data_driver.drive_data(data_dict, self.clock)
                return True
            except Exception as e:
                timeout_count += 1
                if self.log and self.super_debug:
                    self.log.debug(f"AXISMaster '{self.title}': "
                                 f"Drive attempt {timeout_count}: {e}")
                await RisingEdge(self.clock)
        
        return False

    def _packet_to_data_dict(self, packet):
        """Convert packet to data dictionary for driving."""
        data_dict = {}
        
        if hasattr(packet, '_fields'):
            for field_name, field_value in packet._fields.items():
                data_dict[field_name] = field_value
        
        return data_dict

    async def send_frame(self, frame_data, frame_id=0, dest=0, user=0):
        """
        Send a complete frame (multiple transfers with TLAST on final).
        
        Args:
            frame_data: List of data values for the frame
            frame_id: Frame ID
            dest: Destination
            user: User signal
        
        Returns:
            True if successful
        """
        return await self.send_stream_data(
            data_list=frame_data,
            id=frame_id,
            dest=dest,
            user=user,
            auto_last=True
        )

    async def send_single_beat(self, data, last=1, id=0, dest=0, user=0, strb=None):
        """
        Send a single beat/transfer.
        
        Args:
            data: Data value
            last: TLAST value
            id: Stream ID
            dest: Destination
            user: User signal
            strb: Strobe value (if None, auto-generate)
        
        Returns:
            True if successful
        """
        packet = AXISPacket(field_config=self.field_config)
        packet.data = data
        packet.last = last
        packet.id = id
        packet.dest = dest
        packet.user = user
        
        if strb is not None:
            packet.strb = strb
        elif 'strb' in self.field_config:
            strb_bits = self.field_config['strb'].bits
            packet.strb = (1 << strb_bits) - 1
        
        return await self.send_packet(packet)

    def is_busy(self):
        """Check if master is currently busy sending."""
        return self._busy or len(self._send_queue) > 0

    def get_queue_depth(self):
        """Get current send queue depth."""
        return len(self._send_queue)

    def get_stats(self):
        """Get comprehensive statistics."""
        base_stats = self.get_base_stats_unified()
        
        # Add AXIS master specific statistics
        axis_stats = {
            'packets_sent': self.packets_sent,
            'frames_sent': self.frames_sent,
            'total_data_bytes': self.stats.bytes_transferred,
            'timeouts': self.stats.timeout_events,
            'errors': self.stats.transactions_failed,
            'queue_depth': self.get_queue_depth(),
            'is_busy': self.is_busy()
        }
        
        # Merge base stats with AXIS-specific stats
        base_stats.update(axis_stats)
        return base_stats

    def __str__(self):
        """String representation."""
        return (f"AXISMaster '{self.title}': "
                f"{self.packets_sent} packets sent, "
                f"{self.frames_sent} frames sent, "
                f"queue_depth={self.get_queue_depth()}")
