# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIMonitor
# Purpose: Updated GAXIMonitor - Clean implementation using unified GAXIMonitorBase
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated GAXIMonitor - Clean implementation using unified GAXIMonitorBase

Preserves exact timing-critical cocotb methods and external API while
eliminating code duplication through inheritance from unified base classes.

All existing parameters are preserved and used exactly as before.
"""

import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from .gaxi_monitor_base import GAXIMonitorBase
from .gaxi_packet import GAXIPacket


class GAXIMonitor(GAXIMonitorBase):
    """
    GAXI Monitor - Clean implementation using unified base functionality.

    Inherits all common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration using base MemoryModel directly

    Focuses only on monitoring-specific logic:
    - Pure monitoring (no signal driving)
    - Protocol violation detection
    - Handshake tracking
    - Master-side or slave-side monitoring based on is_slave parameter

    FIXED: Always samples data immediately when handshake is detected,
    regardless of DUT internal mode (fifo_flop vs fifo_mux).
    """

    def __init__(self, dut, title, prefix, clock, field_config, is_slave=False,
                    mode='skid',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    log=None, super_debug=False,
                    signal_map=None, protocol_type=None, **kwargs):
        """
        Initialize GAXI Monitor - EXACT SAME API AS BEFORE.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            is_slave: If True, monitor slave side; if False, monitor master side
            mode: GAXI mode ('skid', 'fifo_mux', 'fifo_flop') - for DUT parameter only
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments
        """
        # Monitor-specific attributes
        self.is_slave = is_slave

        # Determine protocol type based on what we're monitoring
        if protocol_type is None:
            protocol_type = 'gaxi_slave' if is_slave else 'gaxi_master'

        # Initialize base class with all common functionality
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            mode=mode,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=multi_sig,
            protocol_type=protocol_type,
            log=log,
            super_debug=super_debug,
            signal_map=signal_map,
            **kwargs
        )

        # Monitor-specific initialization
        self.last_transaction = None       # Last observed transaction

        side = "slave" if is_slave else "master"
        self.log.info(f"GAXIMonitor '{title}' initialized: {side} side, mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _check_protocol_violation(self):
        """
        EXACT PROTOCOL VIOLATION CHECK FROM ORIGINAL
        """
        # Check for valid/ready protocol violations
        if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
            hasattr(self, 'ready_sig') and self.ready_sig is not None):

            if (self.valid_sig.value.is_resolvable and
                self.ready_sig.value.is_resolvable):

                valid_val = int(self.valid_sig.value)
                ready_val = int(self.ready_sig.value)

                # Log any unusual protocol conditions
                if valid_val == 1 and ready_val == 0:
                    # Valid asserted but ready not asserted - normal backpressure
                    pass
                elif valid_val == 0 and ready_val == 1:
                    # Ready asserted but valid not asserted - normal ready ahead
                    pass
                elif valid_val == 1 and ready_val == 1:
                    # Valid handshake - normal operation
                    pass
                # No specific protocol violations to check for GAXI unlike FIFO

        return False

    async def _monitor_recv(self):
        """
        FIXED MONITOR RECV - Correct sampling timing based on mode and side.

        SAMPLING RULES:
        - Master side monitoring: ALWAYS sample immediately (mode irrelevant)
        - Slave side + fifo_mux: Sample immediately
        - Slave side + fifo_flop: Delay capture by one cycle
        - Slave side + skid: Sample immediately

        Uses inherited clean _get_data_dict() and _finish_packet() methods
        that eliminate the conditional mess while preserving exact timing.
        """
        try:
            # Set up pending transaction for delayed capture
            pending_packet = None
            pending_capture = False

            while True:
                # Wait for a falling edge to sample signals - EXACT WORKING TIMING
                await FallingEdge(self.clock)

                # Get current time
                current_time = get_sim_time('ns')

                # Check for protocol violations - EXACT WORKING LOGIC
                self._check_protocol_violation()

                # Handle pending captures for delayed sampling - EXACT WORKING LOGIC
                if pending_capture:
                    # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                    data_dict = self._get_data_dict()
                    # CLEAN: Use inherited _finish_packet() - unified implementation!
                    self._finish_packet(current_time, pending_packet, data_dict)
                    # Trigger coverage hooks for observed transaction
                    direction = 'rx' if self.is_slave else 'tx'
                    self._trigger_coverage_hooks(pending_packet, direction)
                    pending_capture = False
                    pending_packet = None

                # Check for valid/ready handshake - EXACT WORKING LOGIC
                if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
                    hasattr(self, 'ready_sig') and self.ready_sig is not None and
                    self.valid_sig.value.is_resolvable and
                    self.ready_sig.value.is_resolvable and
                    int(self.valid_sig.value) == 1 and   # valid is asserted
                    int(self.ready_sig.value) == 1):     # ready is asserted

                    # Create a packet and capture data immediately or in next cycle
                    # based on CORRECT timing rules
                    packet = GAXIPacket(self.field_config)
                    packet.start_time = current_time

                    # FIXED: Only delay capture for slave side + fifo_flop mode
                    if self.is_slave and self.mode == 'fifo_flop':
                        # Schedule capture for next cycle (slave fifo_flop only)
                        pending_capture = True
                        pending_packet = packet
                        self.log.debug(f"GAXIMonitor({self.title}): Delaying capture for slave fifo_flop mode")
                    else:
                        # Capture data immediately for all other cases:
                        # - Master side (any mode)
                        # - Slave side + fifo_mux mode
                        # - Slave side + skid mode
                        # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                        data_dict = self._get_data_dict()
                        # CLEAN: Use inherited _finish_packet() - unified implementation!
                        self._finish_packet(current_time, packet, data_dict)
                        # Trigger coverage hooks for observed transaction
                        direction = 'rx' if self.is_slave else 'tx'
                        self._trigger_coverage_hooks(packet, direction)

                # Wait a bit to avoid oversampling - EXACT WORKING TIMING
                await Timer(1, units='ps')

        except Exception as e:
            self.log.error(f"GAXIMonitor ({self.title}): Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def get_stats(self):
        """Get comprehensive statistics - ENHANCED with base stats"""
        base_stats = self.get_base_stats()

        # Add monitor-specific statistics
        monitor_specific_stats = {
            'monitor_type': 'slave' if self.is_slave else 'master',
        }

        # Merge base stats with monitor-specific stats
        base_stats.update(monitor_specific_stats)
        return base_stats

    def __str__(self):
        """String representation"""
        side = "Slave" if self.is_slave else "Master"
        return (f"GAXIMonitor '{self.title}' ({side} Side): "
                f"{len(self._recvQ)} packets observed")
