# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: AXISMonitor
# Purpose: AXIS Monitor - Stream protocol monitor implementation
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXIS Monitor - Stream protocol monitor implementation

This module provides AXIS Monitor functionality using GAXI infrastructure.
Similar API to AXI4Monitor but adapted for stream protocol.
"""

import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from ..gaxi.gaxi_monitor_base import GAXIMonitorBase
from .axis_packet import AXISPacket
from .axis_field_configs import AXISFieldConfigs


class AXISMonitor(GAXIMonitorBase):
    """
    AXIS Monitor component for observing AXI4-Stream protocol.
    
    Inherits all common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration
    
    AXIS-specific features:
    - Stream transaction monitoring
    - Frame boundary detection with TLAST
    - Protocol violation detection
    - Comprehensive stream statistics
    """

    def __init__(self, dut, title, prefix, clock, field_config=None, 
                is_slave=False, mode='skid',
                bus_name='', pkt_prefix='', multi_sig=False,
                log=None, super_debug=False, signal_map=None, **kwargs):
        """
        Initialize AXIS Monitor.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix (e.g., "s_axis_", "m_axis_", "axis_")
            clock: Clock signal
            field_config: Field configuration (if None, creates default)
            is_slave: True if monitoring slave side, False for master side
            mode: Protocol mode ('skid', 'blocking', etc.)
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            log: Logger instance
            super_debug: Enable detailed debugging
            signal_map: Optional manual signal mapping
            **kwargs: Additional configuration
        """
        # Create default field config if none provided
        if field_config is None:
            field_config = AXISFieldConfigs.create_default_axis_config()

        # Initialize base monitor
        super().__init__(
            dut=dut, title=title, prefix=prefix, clock=clock,
            field_config=field_config, protocol_type='axis_slave' if is_slave else 'axis_master',
            mode=mode, bus_name=bus_name, pkt_prefix=pkt_prefix,
            multi_sig=multi_sig, log=log, super_debug=super_debug,
            signal_map=signal_map, **kwargs
        )

        # AXIS Monitor specific attributes
        self.is_slave = is_slave
        
        # Frame tracking
        self._current_frame = []
        self._frame_id = None
        
        # Statistics tracking
        self.packets_observed = 0
        self.frames_observed = 0
        self.total_data_bytes = 0
        self.protocol_violations = 0
        
        # Complete initialization
        self.complete_base_initialization()

        if self.log:
            side = "slave" if self.is_slave else "master"
            self.log.info(f"AXISMonitor '{self.title}' initialized: "
                         f"{side} side, mode={self.mode}")

    async def _monitor_recv(self):
        """
        Monitor for AXIS transfers.
        
        This is the main monitoring loop that watches for valid/ready handshakes
        and captures stream data for analysis.
        """
        try:
            while True:
                await FallingEdge(self.clock)
                
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
                    self.packets_observed += 1
                    self.total_data_bytes += packet.get_byte_count()
                    
                    # Handle frame boundaries
                    if packet.is_last():
                        self.frames_observed += 1
                        self._current_frame.append(packet)
                        await self._process_complete_frame(self._current_frame)
                        self._current_frame = []
                        self._frame_id = None
                    else:
                        self._current_frame.append(packet)
                        if self._frame_id is None:
                            self._frame_id = packet.id
                    
                    # Check for protocol violations
                    self._check_protocol_violations(packet)
                    
                    # Write to memory model if available
                    if self.memory_model:
                        self.write_to_memory_unified(packet)
                    
                    if self.log and self.super_debug:
                        self.log.debug(f"AXISMonitor '{self.title}': "
                                     f"Observed packet {packet}")
                
                # Small delay to avoid oversampling
                await Timer(1, units='ps')

        except Exception as e:
            if self.log:
                self.log.error(f"AXISMonitor '{self.title}': Exception in _monitor_recv: {e}")
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

    def _check_protocol_violations(self, packet):
        """
        Check for AXIS protocol violations.
        
        Args:
            packet: AXISPacket to check
        """
        violations = []
        
        # Check if strobe has any holes (non-contiguous 1s)
        if hasattr(packet, 'strb') and packet.strb:
            strb_val = packet.strb
            # Find first and last set bits
            first_bit = -1
            last_bit = -1
            bit_pos = 0
            temp_strb = strb_val
            
            while temp_strb > 0:
                if temp_strb & 1:
                    if first_bit == -1:
                        first_bit = bit_pos
                    last_bit = bit_pos
                temp_strb >>= 1
                bit_pos += 1
            
            # Check for holes between first and last bits
            if first_bit != -1 and last_bit != -1:
                for i in range(first_bit, last_bit + 1):
                    if not (strb_val & (1 << i)):
                        violations.append(f"Non-contiguous strobe at bit {i}")
                        break
        
        # Check for zero strobe with valid data
        if hasattr(packet, 'strb') and packet.strb == 0 and packet.data != 0:
            violations.append("Zero strobe with non-zero data")
        
        # Log violations
        if violations:
            self.protocol_violations += len(violations)
            if self.log:
                for violation in violations:
                    self.log.warning(f"AXISMonitor '{self.title}': "
                                   f"Protocol violation: {violation}")

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
            self.log.debug(f"AXISMonitor '{self.title}': "
                         f"Observed complete frame ID={frame_id}, size={frame_size} bytes, "
                         f"packets={len(frame_packets)}")

    def get_current_frame_info(self):
        """
        Get information about the currently observed frame.
        
        Returns:
            Dictionary with frame information
        """
        return {
            'packets_in_frame': len(self._current_frame),
            'frame_id': self._frame_id,
            'total_bytes': sum(p.get_byte_count() for p in self._current_frame) if self._current_frame else 0,
            'is_receiving': len(self._current_frame) > 0
        }

    def get_protocol_stats(self):
        """
        Get protocol-specific statistics.
        
        Returns:
            Dictionary with protocol statistics
        """
        return {
            'protocol_violations': self.protocol_violations,
            'avg_frame_size': (self.total_data_bytes / self.frames_observed) if self.frames_observed > 0 else 0,
            'avg_packets_per_frame': (self.packets_observed / self.frames_observed) if self.frames_observed > 0 else 0,
        }

    def get_bandwidth_stats(self):
        """
        Get bandwidth and throughput statistics.
        
        Returns:
            Dictionary with bandwidth statistics
        """
        # Basic bandwidth calculation would need timing information
        # This is a placeholder for more sophisticated bandwidth analysis
        return {
            'total_bytes': self.total_data_bytes,
            'total_packets': self.packets_observed,
            'total_frames': self.frames_observed,
            'avg_packet_size': (self.total_data_bytes / self.packets_observed) if self.packets_observed > 0 else 0
        }

    def get_stats(self):
        """Get comprehensive statistics."""
        base_stats = self.get_base_stats_unified()
        
        # Add AXIS monitor specific statistics
        axis_stats = {
            'monitor_type': 'slave' if self.is_slave else 'master',
            'packets_observed': self.packets_observed,
            'frames_observed': self.frames_observed,
            'total_data_bytes': self.total_data_bytes,
            'current_frame_info': self.get_current_frame_info(),
            'protocol_stats': self.get_protocol_stats(),
            'bandwidth_stats': self.get_bandwidth_stats()
        }
        
        # Add base monitor statistics
        if hasattr(self, 'stats'):
            axis_stats.update(self.stats.get_stats())
        
        # Merge base stats with AXIS-specific stats
        base_stats.update(axis_stats)
        return base_stats

    async def wait_for_frames(self, frame_count, timeout_cycles=1000):
        """
        Wait for a specific number of frames to be observed.
        
        Args:
            frame_count: Number of frames to wait for
            timeout_cycles: Maximum cycles to wait
        
        Returns:
            True if frames observed, False if timeout
        """
        initial_frame_count = self.frames_observed
        target_frames = initial_frame_count + frame_count
        cycles = 0
        
        while cycles < timeout_cycles:
            if self.frames_observed >= target_frames:
                return True
            
            await RisingEdge(self.clock)
            cycles += 1
        
        return False

    async def wait_for_packets(self, packet_count, timeout_cycles=1000):
        """
        Wait for a specific number of packets to be observed.
        
        Args:
            packet_count: Number of packets to wait for
            timeout_cycles: Maximum cycles to wait
        
        Returns:
            True if packets observed, False if timeout
        """
        initial_packet_count = self.packets_observed
        target_packets = initial_packet_count + packet_count
        cycles = 0
        
        while cycles < timeout_cycles:
            if self.packets_observed >= target_packets:
                return True
            
            await RisingEdge(self.clock)
            cycles += 1
        
        return False

    def __str__(self):
        """String representation."""
        side = "Slave" if self.is_slave else "Master"
        return (f"AXISMonitor '{self.title}' ({side} Side): "
                f"{self.packets_observed} packets observed, "
                f"{self.frames_observed} frames observed, "
                f"{self.protocol_violations} violations")
