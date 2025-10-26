# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOSlave
# Purpose: Updated FIFOSlave - Clean implementation using unified FIFOMonitorBase
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated FIFOSlave - Clean implementation using unified FIFOMonitorBase

Preserves exact timing-critical cocotb methods and external API while
leveraging the unified infrastructure through the updated base classes.

All existing parameters are preserved and used exactly as before.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from .fifo_monitor_base import FIFOMonitorBase
from ..shared.monitor_statistics import MonitorStatistics
from .fifo_packet import FIFOPacket


class FIFOSlave(FIFOMonitorBase):
    """
    FIFO Slave - Clean implementation using unified base functionality.

    Inherits all common functionality from FIFOMonitorBase (which now inherits from FIFOComponentBase):
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration using base MemoryModel directly
    - Randomizer setup with appropriate defaults

    Adds slave-specific functionality:
    - Active read signal driving (_set_rd_ready)
    - Phase-based receive logic with delays
    - Read timing control with randomization
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='fifo_mux',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None, log=None, super_debug=False,
                    signal_map=None, **kwargs):
        """
        Initialize FIFO Slave - EXACT SAME API AS BEFORE.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            timeout_cycles: Timeout for operations
            mode: FIFO mode ('fifo_mux' or 'fifo_flop')
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for read delays
            log: Logger instance
            super_debug: Enable detailed debugging
            **kwargs: Additional arguments
        """
        # Initialize base class with slave protocol type and pass randomizer through
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
            protocol_type='fifo_slave',  # Slave monitors read side
            randomizer=randomizer,  # Pass through to FIFOComponentBase
            log=log,
            super_debug=super_debug,
            signal_map=signal_map,
            **kwargs
        )

        # Slave-specific attributes
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False

        # Note: Statistics, randomizer, and most initialization now handled by base classes

        # Slave-specific initialization - callbacks for compatibility
        self.callbacks = []

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"FIFOSlave '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize read signal using inherited signal resolver
            if hasattr(self, 'read_sig') and self.read_sig is not None:
                self.read_sig.setimmediatevalue(0)

        except Exception as e:
            self.log.error(f"FIFOSlave '{self.title}': Error initializing signals: {e}")

    async def reset_bus(self):
        """Reset bus - EXACT WORKING PATTERN FROM ORIGINAL"""
        self.log.debug(f"FIFOSlave({self.title}): resetting the bus")
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Deassert read signal
        self._set_rd_ready(0)

        # Clear any queued transactions - EXACT WORKING PATTERN
        # Note: Use inherited _recvQ from BusMonitor, not custom queue
        self._recvQ.clear()

    def _set_rd_ready(self, value):
        """Set read signal - EXACT WORKING PATTERN"""
        if hasattr(self, 'read_sig') and self.read_sig is not None:
            self.read_sig.value = value

    async def _recv_phase1(self, last_packet, last_xfer):
        """EXACT WORKING PHASE 1 - uses inherited clean _get_data_dict()"""
        # Wait a brief moment for signal stability
        await Timer(200, units='ps')

        current_time = get_sim_time('ns')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            packet = last_packet

            # CLEAN: Use inherited _get_data_dict() - no conditional mess!
            data_dict = self._get_data_dict()
            # CLEAN: Use inherited _finish_packet() - unified implementation!
            self._finish_packet(current_time, packet, data_dict)

        return current_time

    async def _recv_phase2(self):
        """EXACT WORKING PHASE 2 - DO NOT MODIFY TIMING"""
        # Check if FIFO is empty
        if hasattr(self, 'empty_sig') and self.empty_sig is not None and self.empty_sig.value:
            # FIFO is empty, keep read deasserted and update stats
            self._set_rd_ready(0)
            # Note: empty_cycles tracking moved to enhanced stats
            return

        # Check if valid on this cycle, if so we can't drop read
        if not (not self.empty_sig.value.is_resolvable or
                not self.read_sig.value.is_resolvable or
                self.empty_sig.value.integer != 0 or
                self.read_sig.value.integer != 1):
            # Previous read in progress, no delay
            return

        # Determine read delay for this cycle - using inherited randomizer
        delay_cfg = self.randomizer.next()
        read_delay = delay_cfg.get('read_delay', 0)
        if read_delay > 0:
            # Deassert read during delay
            self._set_rd_ready(0)
            await self.wait_cycles(read_delay)

        # FIFO is not empty, assert read
        self._set_rd_ready(1)

        # Wait for a falling edge to sample signals
        await FallingEdge(self.clock)

    async def _recv_phase3(self, current_time):
        """EXACT WORKING PHASE 3 - uses inherited clean data collection and stats"""
        # Check if reading and FIFO is not empty (valid read)
        if (hasattr(self, 'read_sig') and self.read_sig is not None and
            hasattr(self, 'empty_sig') and self.empty_sig is not None and
            self.read_sig.value.is_resolvable and
            self.empty_sig.value.is_resolvable and
            self.read_sig.value.integer == 1 and
            self.empty_sig.value.integer == 0):

            # Create a new packet
            packet = FIFOPacket(self.field_config)
            packet.start_time = current_time

            # Record transaction received for monitoring statistics
            # Note: Can add SlaveStatistics separately for performance tracking if needed

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note read time, defer data capture to next cycle
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                await Timer(self.tick_delay, units=self.tick_units)
                return last_packet, last_xfer
            else:
                # In fifo_mux mode, capture data in the same cycle
                # CLEAN: Use inherited _get_data_dict() - no conditional mess!
                data_dict = self._get_data_dict()
                # CLEAN: Use inherited _finish_packet() - unified implementation!
                self._finish_packet(current_time, packet, data_dict)

                # Handle memory operations if memory model available - UNIFIED
                if self.memory_model:
                    self.handle_memory_write(packet)

        elif (hasattr(self, 'read_sig') and self.read_sig is not None and
                hasattr(self, 'empty_sig') and self.empty_sig is not None and
                self.read_sig.value.is_resolvable and
                self.empty_sig.value.is_resolvable and
                self.read_sig.value.integer == 1 and
                self.empty_sig.value.integer == 1):
            # Use monitoring statistics for read while empty
            if hasattr(self.stats, 'read_while_empty'):
                self.stats.read_while_empty += 1
            self.log.warning(f"FIFOSlave({self.title}) Read while empty detected at {current_time}ns")

        # Deassert read on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        self._set_rd_ready(0)

        # Default return values
        return None, False

    async def _monitor_recv(self):
        """
        EXACT WORKING MONITOR RECV - DO NOT MODIFY TIMING/LOGIC

        Uses inherited clean _get_data_dict() and _finish_packet() methods
        that eliminate the conditional mess while preserving exact timing.
        """
        try:
            last_packet = None
            last_xfer = False

            while True:
                # recv phase 1: Handle pending transactions
                current_time = await self._recv_phase1(last_packet, last_xfer)

                # Always clear the last transfer here
                last_xfer = False

                # recv phase 2: Handle read delays and assert read if not empty
                await self._recv_phase2()

                # recv phase 3: Check for valid read and process transaction
                last_packet, last_xfer = await self._recv_phase3(current_time)

        except Exception as e:
            self.log.error(f"FIFOSlave({self.title}) Exception in _monitor_recv: {e}")
            import traceback
            self.log.error(traceback.format_exc())
            raise

    async def wait_cycles(self, cycles):
        """EXACT WORKING WAIT METHOD - DO NOT MODIFY"""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            if self.reset_occurring:
                break

        await Timer(self.tick_delay, units=self.tick_units)

    def get_stats(self):
        """Get comprehensive statistics - ENHANCED with unified base stats"""
        base_stats = self.get_base_stats()

        # Add any slave-specific statistics here if needed in the future
        # For now, all statistics are handled by the base classes

        return base_stats

    def __str__(self):
        """String representation"""
        return f"FIFOSlave '{self.title}': {self.stats.received_transactions} transactions"
