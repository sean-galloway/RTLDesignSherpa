# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOMonitorBase
# Purpose: Updated FIFOMonitorBase - Using FIFOComponentBase for unified functionality
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated FIFOMonitorBase - Using FIFOComponentBase for unified functionality

Eliminates duplication while preserving exact APIs and timing.
All existing parameters are maintained and used exactly as before.
"""

from cocotb_bus.monitors import BusMonitor
from cocotb.utils import get_sim_time

from .fifo_component_base import FIFOComponentBase
from ..shared.monitor_statistics import MonitorStatistics
from .fifo_packet import FIFOPacket


class FIFOMonitorBase(FIFOComponentBase, BusMonitor):
    """
    Base class providing common FIFO monitoring functionality using unified infrastructure.

    Inherits common functionality from FIFOComponentBase:
    - Signal resolution and data collection setup
    - Unified field configuration handling
    - Memory model integration using base MemoryModel directly
    - Statistics and logging patterns

    Shared by FIFOMonitor and FIFOSlave to eliminate code duplication
    while preserving exact APIs and timing-critical behavior.
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    mode='fifo_mux',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    protocol_type=None,  # 'fifo_master' or 'fifo_slave' - set by subclass
                    log=None, super_debug=False,
                    signal_map=None, **kwargs):
        """
        Initialize common FIFO monitoring functionality - EXACT SAME API AS BEFORE.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            mode: FIFO mode ('fifo_mux' or 'fifo_flop')
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            protocol_type: Must be set by subclass ('fifo_master' or 'fifo_slave')
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments for BusMonitor
        """
        # Extract parameters that shouldn't go to BusMonitor
        memory_model = kwargs.pop('memory_model', None)
        randomizer = kwargs.pop('randomizer', None)

        # Initialize base class with all parameters preserved
        FIFOComponentBase.__init__(
            self,
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type=protocol_type,
            mode=mode,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=multi_sig,
            memory_model=memory_model,
            randomizer=randomizer,
            log=log,
            super_debug=super_debug,
            signal_map=signal_map,
            **kwargs
        )

        # Remove prefix from kwargs so it doesn't get passed to BusDriver/BusMonitor
        kwargs.pop('prefix', None)

        # Initialize parent BusMonitor - MUST BE CALLED WITH EXACT PATTERN
        # Only pass kwargs that BusMonitor/Bus can handle
        BusMonitor.__init__(self, dut, prefix, clock, callback=None, event=None, **kwargs)
        self.log = log or self._log

        # Complete base class initialization now that bus is available
        self.complete_base_initialization(self.bus)

        # Statistics - unified setup for all FIFO monitoring components
        self.stats = MonitorStatistics()

        side_description = "read" if protocol_type == 'fifo_slave' else "write"
        self.log.info(f"FIFOMonitorBase '{title}' initialized: {side_description} side, "
                        f"mode={mode}, multi_sig={self.use_multi_signal}")

    def _get_data_dict(self):
        """
        UNIFIED: Clean data collection with automatic field unpacking.

        This replaces the messy _get_data_dict() + conditional unpacking logic
        that was duplicated in both FIFOMonitor and FIFOSlave.

        Uses the unified DataCollectionStrategy.collect_and_unpack_data() method
        that eliminates all the conditional mess.

        Returns:
            Dictionary of field values, properly unpacked
        """
        return self.get_data_dict_unified()

    def _finish_packet(self, current_time, packet, data_dict=None):
        """
        UNIFIED: Clean packet finishing without conditional mess.

        This replaces the duplicate _finish_packet logic that was in both
        FIFOMonitor and FIFOSlave with identical functionality.

        Args:
            current_time: Current simulation time
            packet: Packet to finish
            data_dict: Optional field data (if None, will collect fresh data)
        """
        # Get data if not provided
        if data_dict is None:
            data_dict = self._get_data_dict()

        # Use the packet's unpack_from_fifo method for field handling
        if data_dict:
            if hasattr(packet, 'unpack_from_fifo'):
                packet.unpack_from_fifo(data_dict)
                self.log.debug(f"FIFOMonitorBase({self.title}) Transaction at {current_time}ns: unpack from fifo")
            else:
                # Legacy fallback - set fields directly
                self.log.debug(f"FIFOMonitorBase({self.title}) Transaction at {current_time}ns: legacy unpack")
                for field_name, value in data_dict.items():
                    if value != -1:  # Skip X/Z values
                        if hasattr(packet, field_name):
                            setattr(packet, field_name, value)

        # Set end time
        packet.end_time = current_time

        # Update statistics - use fields that exist in MonitorStatistics
        if hasattr(self.stats, 'received_transactions'):
            self.stats.received_transactions += 1
        if hasattr(self.stats, 'transactions_observed'):
            self.stats.transactions_observed += 1

        # Log the transaction
        packet_str = (packet.formatted(compact=True)
                        if hasattr(packet, 'formatted')
                        else str(packet))
        self.log.debug(f"FIFOMonitorBase({self.title}) Transaction at {current_time}ns: {packet_str}")

        # ESSENTIAL: Use cocotb _recv method to add to _recvQ and trigger callbacks
        self._recv(packet)

    def create_packet(self, **field_values):
        """
        UNIFIED: Create a packet with specified field values.

        This was duplicated identically in both FIFOMonitor and FIFOSlave.

        Args:
            **field_values: Initial field values

        Returns:
            FIFOPacket instance with specified field values
        """
        packet = FIFOPacket(self.field_config)
        for field_name, value in field_values.items():
            if hasattr(packet, field_name):
                setattr(packet, field_name, value)
        return packet

    def get_observed_packets(self, count=None):
        """
        Get observed packets from standard cocotb _recvQ.

        Args:
            count: Number of packets to return (None = all)

        Returns:
            List of observed packets
        """
        if count is None:
            return list(self._recvQ)
        return list(self._recvQ)[-count:]

    def clear_queue(self):
        """Clear the observed transactions queue - standard cocotb pattern"""
        self._recvQ.clear()
        self.log.info(f"FIFOMonitorBase ({self.title}): Observed queue cleared")

    # Memory operations using base MemoryModel directly (for slave components)
    def handle_memory_write(self, packet):
        """Handle memory write using unified memory integration"""
        success, error = self.write_to_memory_unified(packet)
        if success:
            self.log.debug(f"FIFOMonitorBase: Memory write successful")
        else:
            self.log.warning(f"FIFOMonitorBase: Memory write failed: {error}")
        return success

    def handle_memory_read(self, packet):
        """Handle memory read using unified memory integration"""
        success, data, error = self.read_from_memory_unified(packet, update_transaction=True)
        if success:
            self.log.debug(f"FIFOMonitorBase: Memory read successful, data=0x{data:X}")
        else:
            self.log.warning(f"FIFOMonitorBase: Memory read failed: {error}")
        return success, data

    def get_base_stats(self):
        """
        Get base statistics that are common to all FIFO monitoring components.

        Subclasses should call this and add their own specific statistics.

        Returns:
            Dictionary containing base statistics
        """
        base_stats = self.get_base_stats_unified()
        base_stats.update({
            'monitor_stats': self.stats.get_stats(),
            'observed_packets': len(self._recvQ)
        })
        return base_stats

    def __str__(self):
        """String representation"""
        side = "Read" if self.protocol_type == 'fifo_slave' else "Write"
        return (f"FIFOMonitorBase '{self.title}' ({side} Side): "
                f"{len(self._recvQ)} packets observed")
