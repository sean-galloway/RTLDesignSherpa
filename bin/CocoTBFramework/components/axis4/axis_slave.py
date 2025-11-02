# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISSlave
# Purpose: AXIS Slave - Stream protocol slave implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Slave - Stream protocol slave implementation

This module provides AXIS Slave functionality using GAXI infrastructure.
Similar API to AXI4Slave but adapted for stream protocol.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..gaxi.gaxi_monitor_base import GAXIMonitorBase
from ..shared.monitor_statistics import MonitorStatistics
from .axis_packet import AXISPacket
from .axis_field_configs import AXISFieldConfigs


class AXISSlave(GAXIMonitorBase):
    """
    AXIS Slave component for receiving AXI4-Stream protocol.
    
    Inherits common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration
    
    AXIS-specific features:
    - Stream data reception with backpressure control
    - Frame boundary detection with TLAST
    - Ready signal timing control
    - Packet and frame statistics
    """

    def __init__(self, dut, title, prefix, clock, field_config=None,
                timeout_cycles=1000, mode='skid',
                bus_name='', pkt_prefix='', multi_sig=False,
                randomizer=None, memory_model=None, log=None,
                super_debug=False, pipeline_debug=False,
                signal_map=None, **kwargs):
        """
        Initialize AXIS Slave.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "s_axis_", "axis_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            timeout_cycles: Maximum cycles for operations
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

        # Initialize base monitor
        super().__init__(
            dut=dut, title=title, prefix=prefix, clock=clock,
            field_config=field_config, protocol_type='axis_slave',
            mode=mode, bus_name=bus_name, pkt_prefix=pkt_prefix,
            multi_sig=multi_sig, log=log, super_debug=super_debug,
            signal_map=signal_map, **kwargs
        )

        # AXIS Slave specific attributes
        self.timeout_cycles = timeout_cycles
        self.pipeline_debug = pipeline_debug
        self.randomizer = randomizer
        self.memory_model = memory_model
        
        # Reception state
        self._receiving = False
        self._current_frame = []
        self._frame_id = None
        
        # Statistics tracking
        self.packets_received = 0
        self.frames_received = 0
        self.total_data_bytes = 0
        self.errors = 0
        
        # Complete initialization
        self.complete_base_initialization()
        
        # Start monitoring
        if hasattr(self, '_start_monitoring'):
            cocotb.start_soon(self._start_monitoring())

        if self.log:
            self.log.info(f"AXISSlave '{self.title}' initialized: "
                         f"mode={self.mode}, timeout={self.timeout_cycles} cycles")

    async def _monitor_recv(self):
        """
        Monitor for incoming AXIS transfers.
        
        This is the main monitoring loop that watches for valid/ready handshakes
        and captures stream data.
        """
        try:
            while True:
                await RisingEdge(self.clock)
                
                # Check for valid handshake
                if self._is_handshake_valid():
                    current_time = get_sim_time(units='ns')
                    
                    # Create packet from current data
                    packet = AXISPacket(
                        field_config=self.field_config,
                        timestamp=current_time
                    )
                    
                    # Collect data using inherited functionality
                    data_dict = self._get_data_dict()
                    self._finish_packet(current_time, packet, data_dict)
                    
                    # Update statistics
                    self.packets_received += 1
                    self.total_data_bytes += packet.get_byte_count()
                    
                    # Handle frame boundaries
                    if packet.is_last():
                        self.frames_received += 1
                        self._current_frame.append(packet)
                        await self._process_complete_frame(self._current_frame)
                        self._current_frame = []
                        self._frame_id = None
                    else:
                        self._current_frame.append(packet)
                        if self._frame_id is None:
                            self._frame_id = packet.id
                    
                    # Write to memory model if available
                    if self.memory_model:
                        self.write_to_memory_unified(packet)
                    
                    if self.log and self.super_debug:
                        self.log.debug(f"AXISSlave '{self.title}': "
                                     f"Received packet {packet}")
                
                # Apply ready signal timing if randomizer is available
                if self.randomizer and hasattr(self, 'ready_signal'):
                    await self._apply_ready_timing()
                
                # Small delay to avoid oversampling
                await Timer(1, units='ps')

        except Exception as e:
            if self.log:
                self.log.error(f"AXISSlave '{self.title}': Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def _is_handshake_valid(self):
        """Check if valid/ready handshake is occurring."""
        try:
            # Get signals using inherited signal resolution
            valid_signal = getattr(self, 'valid_signal', None)
            ready_signal = getattr(self, 'ready_signal', None)
            
            if valid_signal is None or ready_signal is None:
                return False
                
            return bool(valid_signal.value) and bool(ready_signal.value)
            
        except Exception:
            return False

    async def _apply_ready_timing(self):
        """Apply randomized ready signal timing."""
        if not self.randomizer:
            return
            
        try:
            # Get ready delay from randomizer
            delay = self.randomizer.get_delay('ready_delay')
            
            if delay > 0:
                # Lower ready for delay cycles
                if hasattr(self, 'ready_signal'):
                    self.ready_signal.value = 0
                    
                    # Wait for delay cycles
                    for _ in range(delay):
                        await RisingEdge(self.clock)
                    
                    # Raise ready again
                    self.ready_signal.value = 1
                    
        except Exception as e:
            if self.log and self.super_debug:
                self.log.debug(f"AXISSlave '{self.title}': Ready timing error: {e}")

    async def _process_complete_frame(self, frame_packets):
        """
        Process a complete frame (packets ending with TLAST).
        
        Args:
            frame_packets: List of AXISPacket objects forming a complete frame
        """
        if not frame_packets:
            return
            
        frame_size = sum(p.get_byte_count() for p in frame_packets)
        frame_id = frame_packets[0].id if frame_packets else 0
        
        if self.log and self.super_debug:
            self.log.debug(f"AXISSlave '{self.title}': "
                         f"Completed frame ID={frame_id}, size={frame_size} bytes, "
                         f"packets={len(frame_packets)}")
        
        # Frame processing can be extended here for specific applications
        # For now, just log the completion

    def set_ready_always(self, ready=True):
        """
        Set ready signal to always be ready or never ready.
        
        Args:
            ready: True for always ready, False for never ready
        """
        if hasattr(self, 'ready_signal'):
            self.ready_signal.value = 1 if ready else 0
            if self.log:
                self.log.info(f"AXISSlave '{self.title}': "
                             f"Ready signal set to {'always ready' if ready else 'never ready'}")

    def apply_backpressure(self, probability=0.2, min_cycles=1, max_cycles=5):
        """
        Apply random backpressure by controlling ready signal.
        
        Args:
            probability: Probability of applying backpressure (0.0 to 1.0)
            min_cycles: Minimum cycles to hold ready low
            max_cycles: Maximum cycles to hold ready low
        """
        # This would be implemented with a background coroutine
        # For now, use randomizer for ready timing
        if self.randomizer:
            constraints = {
                'ready_delay': ([(0, 0), (min_cycles, max_cycles)], 
                              [1.0-probability, probability])
            }
            self.randomizer.update_constraints(constraints)

    def get_current_frame_info(self):
        """
        Get information about the currently receiving frame.
        
        Returns:
            Dictionary with frame information
        """
        return {
            'packets_in_frame': len(self._current_frame),
            'frame_id': self._frame_id,
            'total_bytes': sum(p.get_byte_count() for p in self._current_frame),
            'is_receiving': self._receiving
        }

    def get_stats(self):
        """Get comprehensive statistics."""
        base_stats = self.get_base_stats_unified()
        
        # Add AXIS slave specific statistics
        axis_stats = {
            'packets_received': self.packets_received,
            'frames_received': self.frames_received,
            'total_data_bytes': self.total_data_bytes,
            'errors': self.errors,
            'current_frame_info': self.get_current_frame_info()
        }
        
        # Add base monitor statistics
        if hasattr(self, 'stats'):
            axis_stats.update(self.stats.get_stats())
        
        # Merge base stats with AXIS-specific stats
        base_stats.update(axis_stats)
        return base_stats

    async def wait_for_frame(self, timeout_cycles=None):
        """
        Wait for a complete frame to be received.
        
        Args:
            timeout_cycles: Maximum cycles to wait (uses self.timeout_cycles if None)
        
        Returns:
            List of packets forming the frame, or None if timeout
        """
        if timeout_cycles is None:
            timeout_cycles = self.timeout_cycles
            
        initial_frame_count = self.frames_received
        cycles = 0
        
        while cycles < timeout_cycles:
            if self.frames_received > initial_frame_count:
                # Frame was completed
                return True
            
            await RisingEdge(self.clock)
            cycles += 1
        
        # Timeout
        return False

    def __str__(self):
        """String representation."""
        return (f"AXISSlave '{self.title}': "
                f"{self.packets_received} packets received, "
                f"{self.frames_received} frames received, "
                f"current_frame_packets={len(self._current_frame)}")
