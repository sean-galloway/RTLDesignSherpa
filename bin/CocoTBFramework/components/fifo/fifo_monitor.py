# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOMonitor
# Purpose: Updated FIFOMonitor - Clean implementation using unified FIFOMonitorBase
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated FIFOMonitor - Clean implementation using unified FIFOMonitorBase

Preserves exact timing-critical cocotb methods and external API while
leveraging the unified infrastructure through the updated base classes.

All existing parameters are preserved and used exactly as before.
"""

import cocotb
from cocotb.triggers import FallingEdge, Timer
from cocotb.utils import get_sim_time

from .fifo_monitor_base import FIFOMonitorBase
from .fifo_packet import FIFOPacket


class FIFOMonitor(FIFOMonitorBase):
    """
    FIFO Monitor - Clean implementation using unified base functionality.

    Inherits all common functionality from FIFOMonitorBase (which now inherits from FIFOComponentBase):
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration using base MemoryModel directly
    - Randomizer setup with appropriate defaults

    Focuses only on monitoring-specific logic:
    - Pure monitoring (no signal driving)
    - Protocol violation detection
    - FIFO depth tracking
    - Write-side or read-side monitoring based on is_slave parameter
    """

    def __init__(self, dut, title, prefix, clock, field_config, is_slave=False,
                    mode='fifo_mux',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    fifo_depth=16,
                    log=None, super_debug=False,
                    signal_map=None, **kwargs):
        """
        Initialize FIFO Monitor - EXACT SAME API AS BEFORE.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            is_slave: If True, monitor read side; if False, monitor write side
            mode: FIFO mode ('fifo_mux' or 'fifo_flop')
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            fifo_depth: FIFO depth for tracking
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments
        """
        # Monitor-specific attributes
        self.is_slave = is_slave
        self.fifo_depth = fifo_depth

        # Determine protocol type based on what we're monitoring
        protocol_type = 'fifo_slave' if is_slave else 'fifo_master'

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
        self.fifo_depth_estimate = 0      # Current estimated FIFO depth
        self.fifo_capacity = fifo_depth    # FIFO capacity
        self.last_transaction = None       # Last observed transaction
        self.pending_transaction = None    # For fifo_flop mode

        side = "read" if is_slave else "write"
        self.log.info(f"FIFOMonitor '{title}' initialized: {side} side, mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def set_fifo_capacity(self, capacity):
        """Set the assumed FIFO capacity for depth tracking"""
        self.fifo_capacity = capacity
        self.log.info(f"FIFOMonitor ({self.title}): Set FIFO capacity to {capacity}")

    def _update_fifo_depth(self, is_write):
        """
        Update estimated FIFO depth - EXACT LOGIC FROM ORIGINAL
        """
        current_time = get_sim_time('ns')

        if is_write:
            # Check if FIFO is actually full before warning
            if (hasattr(self, 'full_sig') and self.full_sig is not None and
                self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Write to full FIFO detected at {current_time}ns")
                self.stats.write_while_full += 1
            else:
                # Safe to increment depth
                self.fifo_depth_estimate = min(self.fifo_depth_estimate + 1, self.fifo_capacity)

            # Update full cycles counter
            if self.fifo_depth_estimate >= self.fifo_capacity:
                self.stats.full_cycles += 1
        else:
            # Check for empty FIFO read
            if (hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.empty_sig.value.is_resolvable and int(self.empty_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Read from empty FIFO detected at {current_time}ns")
                self.stats.read_while_empty += 1
            elif self.fifo_depth_estimate > 0:
                self.fifo_depth_estimate = max(0, self.fifo_depth_estimate - 1)

            # Update empty cycles counter
            if self.fifo_depth_estimate == 0:
                self.stats.empty_cycles += 1

        return self.fifo_depth_estimate

    def _check_protocol_violation(self, is_write):
        """
        EXACT PROTOCOL VIOLATION CHECK FROM ORIGINAL
        """
        if is_write:
            # Check for write while full violation
            if (hasattr(self, 'write_sig') and self.write_sig is not None and
                hasattr(self, 'full_sig') and self.full_sig is not None and
                self.write_sig.value.is_resolvable and
                self.full_sig.value.is_resolvable and
                int(self.write_sig.value) == 1 and
                int(self.full_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - write while full at {get_sim_time('ns')}ns")
                self.stats.protocol_violations += 1
                return True
        else:
            # Check for read while empty violation
            if (hasattr(self, 'read_sig') and self.read_sig is not None and
                hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                int(self.read_sig.value) == 1 and
                int(self.empty_sig.value) == 1):
                self.log.warning(f"FIFOMonitor ({self.title}): Protocol violation - read while empty at {get_sim_time('ns')}ns")
                self.stats.protocol_violations += 1
                return True

        return False

    async def _monitor_recv(self):
        """
        EXACT WORKING MONITOR RECV FROM ORIGINAL - DO NOT MODIFY TIMING

        Uses inherited clean _get_data_dict() and _finish_packet() methods
        that eliminate the conditional mess while preserving exact timing.
        """
        try:
            # Set up pending transaction for fifo_flop mode
            pending_packet = None
            pending_capture = False

            while True:
                # Wait for a falling edge to sample signals - EXACT WORKING TIMING
                await FallingEdge(self.clock)

                # Get current time
                current_time = get_sim_time('ns')

                # Check for protocol violations - EXACT WORKING LOGIC
                self._check_protocol_violation(not self.is_slave)

                # Handle pending captures for fifo_flop mode - EXACT WORKING LOGIC
                if pending_capture and self.mode == 'fifo_flop':
                    # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                    data_dict = self._get_data_dict()
                    # CLEAN: Use inherited _finish_packet() - unified implementation!
                    self._finish_packet(current_time, pending_packet, data_dict)
                    pending_capture = False
                    pending_packet = None

                # Check for write/read operations - EXACT WORKING LOGIC
                if self.is_slave:
                    # Monitoring read port - check if read=1 AND empty=0 (valid read)
                    valid_read = (
                        hasattr(self, 'read_sig') and self.read_sig is not None and
                        hasattr(self, 'empty_sig') and self.empty_sig is not None and
                        self.read_sig.value.is_resolvable and
                        int(self.read_sig.value) == 1 and   # read is asserted
                        self.empty_sig.value.is_resolvable and
                        int(self.empty_sig.value) == 0       # not empty
                    )

                    if valid_read:
                        # Create a packet and capture data immediately or in next cycle
                        # depending on the mode
                        packet = FIFOPacket(self.field_config)
                        packet.start_time = current_time

                        # Update FIFO depth
                        self._update_fifo_depth(is_write=False)

                        if self.mode == 'fifo_flop':
                            # Schedule capture for next cycle
                            pending_capture = True
                            pending_packet = packet
                        else:
                            # Capture data immediately from the data signal
                            # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                            data_dict = self._get_data_dict()
                            # CLEAN: Use inherited _finish_packet() - unified implementation!
                            self._finish_packet(current_time, packet, data_dict)

                    elif (hasattr(self, 'read_sig') and self.read_sig is not None and
                            hasattr(self, 'empty_sig') and self.empty_sig is not None and
                            self.read_sig.value.is_resolvable and
                            int(self.read_sig.value) == 1 and
                            self.empty_sig.value.is_resolvable and
                            int(self.empty_sig.value) == 1):  # read while empty
                        # Already logged in _update_fifo_depth, just update stats
                        pass

                    # Update empty cycles counter if applicable
                    if (hasattr(self, 'empty_sig') and self.empty_sig is not None and
                        self.empty_sig.value.is_resolvable and int(self.empty_sig.value) == 1):
                        self.stats.empty_cycles += 1
                else:
                    # Monitoring write port - check if write=1 (valid write)
                    if (hasattr(self, 'write_sig') and self.write_sig is not None and
                        self.write_sig.value.is_resolvable and int(self.write_sig.value) == 1):

                        if (not hasattr(self, 'full_sig') or self.full_sig is None or
                            not self.full_sig.value.is_resolvable or
                            int(self.full_sig.value) == 0):  # write and not full

                            # Create new packet
                            packet = FIFOPacket(self.field_config)
                            packet.start_time = current_time

                            # Update FIFO depth
                            self._update_fifo_depth(is_write=True)

                            # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                            data_dict = self._get_data_dict()
                            # CLEAN: Use inherited _finish_packet() - unified implementation!
                            self._finish_packet(current_time, packet, data_dict)
                        elif (hasattr(self, 'full_sig') and self.full_sig is not None and
                                self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):  # write while full
                            # Already logged in _update_fifo_depth, just update stats
                            pass

                    # Update full cycles counter if applicable
                    if (hasattr(self, 'full_sig') and self.full_sig is not None and
                        self.full_sig.value.is_resolvable and int(self.full_sig.value) == 1):
                        self.stats.full_cycles += 1

                # Wait a bit to avoid oversampling - EXACT WORKING TIMING
                await Timer(1, units='ps')

        except Exception as e:
            self.log.error(f"FIFOMonitor ({self.title}): Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    def get_stats(self):
        """Get comprehensive statistics - ENHANCED with unified base stats"""
        base_stats = self.get_base_stats()

        # Add monitor-specific statistics
        monitor_specific_stats = {
            'monitor_type': 'read' if self.is_slave else 'write',
            'fifo_depth_estimate': self.fifo_depth_estimate,
            'fifo_capacity': self.fifo_capacity,
            'utilization_percentage': (
                (self.fifo_depth_estimate / self.fifo_capacity * 100)
                if self.fifo_capacity > 0 else 0
            )
        }

        # Merge base stats with monitor-specific stats
        base_stats.update(monitor_specific_stats)
        return base_stats

    def __str__(self):
        """String representation"""
        side = "Read" if self.is_slave else "Write"
        return (f"FIFOMonitor '{self.title}' ({side} Side): "
                f"{len(self._recvQ)} packets observed, "
                f"depth: {self.fifo_depth_estimate}/{self.fifo_capacity}")
