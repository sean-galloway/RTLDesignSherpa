# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: FIFOMaster
# Purpose: Updated FIFOMaster - Using FIFOComponentBase for unified functionality
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Updated FIFOMaster - Using FIFOComponentBase for unified functionality

Preserves exact API and timing while leveraging shared infrastructure.
All existing parameters are maintained and used exactly as before.
"""

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from .fifo_component_base import FIFOComponentBase
from ..shared.master_statistics import MasterStatistics
from .fifo_packet import FIFOPacket


class FIFOMaster(FIFOComponentBase, BusDriver):
    """
    FIFO Master using unified base functionality while preserving exact API.

    Inherits common functionality from FIFOComponentBase:
    - Signal resolution and data driving setup
    - Unified field configuration handling
    - Memory model integration using base MemoryModel directly
    - Statistics and logging patterns

    Preserves all timing-critical cocotb methods exactly as before.
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='fifo_mux',
                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None, log=None, super_debug=False,
                    signal_map=None, **kwargs):
        """
        Initialize FIFO Master - EXACT SAME API AS BEFORE.
        """
        # Initialize base class with all parameters preserved
        FIFOComponentBase.__init__(
            self,
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='fifo_master',
            mode=mode,
            bus_name=bus_name,
            pkt_prefix=pkt_prefix,
            multi_sig=multi_sig,
            randomizer=randomizer,
            log=log,
            super_debug=super_debug,
            signal_map=signal_map,
            **kwargs
        )

        # Master-specific attributes - keeping original working setup
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False

        # Remove prefix from kwargs so it doesn't get passed to BusDriver/BusMonitor
        kwargs.pop('prefix', None)

        # Initialize parent BusDriver - MUST BE CALLED WITH EXACT PATTERN
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        self.log = log or self._log

        # Complete base class initialization now that bus is available
        self.complete_base_initialization(self.bus)

        # Master-specific statistics
        self.stats = MasterStatistics()

        # EXACT WORKING COCOTB PATTERN - DO NOT MODIFY
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"FIFOMaster '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize write signal using modern signal resolver
            if hasattr(self, 'write_sig') and self.write_sig is not None:
                self.write_sig.setimmediatevalue(0)

            # Clear data signals using unified data driver
            self.clear_signals_unified()

        except Exception as e:
            self.log.error(f"FIFOMaster '{self.title}': Error initializing signals: {e}")

    async def reset_bus(self):
        """Reset bus - EXACT WORKING PATTERN FROM ORIGINAL"""
        self.log.debug(f"Master({self.title}): resetting the bus")

        # Reset write signal
        self._assign_write_value(value=0)

        # Reset field signals using unified data driver
        self.clear_signals_unified()

        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Clear queues - EXACT WORKING PATTERN
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        """
        EXACT WORKING COCOTB DRIVER METHOD - DO NOT MODIFY TIMING/LOGIC
        Only replace infrastructure calls (signal mapping, data driving, stats)
        """
        # Add transaction to queue - EXACT WORKING PATTERN
        self.transmit_queue.append(transaction)

        # Start transmission pipeline if not already running - EXACT WORKING PATTERN
        if not hold and not self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Starting new transmit pipeline, queue length: {len(self.transmit_queue)}')
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())

    def _drive_signals(self, transaction):
        """
        Drive signals using unified data driving strategy.
        REPLACES original _drive_signals logic but keeps exact interface.
        """
        try:
            # Use unified data driving strategy instead of manual signal driving
            return self.drive_transaction_unified(transaction)
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _assign_write_value(self, value):
        """Set write signal - EXACT WORKING PATTERN"""
        if hasattr(self, 'write_sig') and self.write_sig is not None:
            self.write_sig.value = value

    def _clear_data_bus(self):
        """Clear data signals - UNIFIED"""
        self.clear_signals_unified()

    async def _xmit_phase1(self):
        """Phase 1: Apply delay - EXACT WORKING TIMING"""
        # Apply any configured delay before asserting write - EXACT WORKING PATTERN
        delay_dict = self.randomizer.next()
        write_delay = delay_dict.get('write_delay', 0)
        if write_delay > 0:
            # Deassert write
            self._assign_write_value(value=0)
            # Clear the data bus
            self._clear_data_bus()
            # write delay - EXACT WORKING TIMING
            await self.wait_cycles(write_delay)

    async def _xmit_phase2(self, transaction):
        """Phase 2: Drive signals and wait for not full - EXACT WORKING LOGIC"""
        # Drive signals for this transaction - UNIFIED CALL
        if not self._drive_signals(transaction):
            self.log.error(f"Failed to drive signals for transaction: {transaction.formatted(compact=True)}")
            self.transfer_busy = False
            return False

        # Wait for FIFO to not be full - EXACT WORKING PATTERN
        timeout_counter = 0

        # Check if full signal is high
        while hasattr(self, 'full_sig') and self.full_sig is not None and self.full_sig.value:
            await self.wait_cycles(1)

            # Keep write deasserted while full
            self._assign_write_value(value=0)

            # Update stats - UNIFIED
            self.stats.record_flow_control_stall(1)

            timeout_counter += 1
            if timeout_counter >= self.timeout_cycles:
                self.log.error(f"Master({self.title}) TIMEOUT waiting for FIFO not full after {self.timeout_cycles} cycles")

                # Stop driving if timeout (prevent hang)
                self._assign_write_value(value=0)
                self._clear_data_bus()

                # Update stats - UNIFIED
                self.stats.record_timeout()

                self.transfer_busy = False
                return False

        # Assert write for this transaction since FIFO is not full
        self._assign_write_value(value=1)

        # Check for write while full error - EXACT WORKING PATTERN
        if (hasattr(self, 'full_sig') and self.full_sig is not None and
            hasattr(self, 'write_sig') and self.write_sig is not None and
            self.full_sig.value and self.write_sig.value):
            current_time_ns = get_sim_time('ns')
            self.log.error(f"Master({self.title}) Error: {self.title} write while fifo full at {current_time_ns}ns")
            # Update stats - UNIFIED
            self.stats.record_protocol_violation("write_while_full")

        # Wait a cycle for the write to take effect - EXACT WORKING TIMING
        await self.wait_cycles(1)

        return True

    async def _xmit_phase3(self, transaction):
        """Phase 3: Complete transfer - EXACT WORKING PATTERN"""
        # Write has been completed – capture completion time
        current_time_ns = get_sim_time('ns')
        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                        f"{transaction.formatted(compact=True)}")
        transaction.end_time = current_time_ns
        self.sent_queue.append(transaction)

        # Update stats - UNIFIED
        bytes_transferred = self._calculate_bytes_transferred(transaction)

        # Deassert write
        self._assign_write_value(value=0)

        # Clear the data bus
        self._clear_data_bus()

    async def _transmit_pipeline(self):
        """
        EXACT WORKING TRANSMISSION PIPELINE - DO NOT MODIFY TIMING
        Only modernize infrastructure calls
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self.transfer_busy = True
        await self.wait_cycles(1)

        while len(self.transmit_queue):
            # Get next transaction from the queue
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')

            # Record transaction start - UNIFIED
            start_time = self.stats.record_transaction_start()

            # xmit phase 1 - apply delay
            await self._xmit_phase1()

            # xmit phase 2 - drive signals and check if FIFO is full
            if not await self._xmit_phase2(transaction):
                # Error occurred in phase 2
                self.stats.record_transaction_failed("xmit_phase2_error", "Phase 2 failed")
                continue

            # xmit phase 3 - handle transfer completion
            await self._xmit_phase3(transaction)

            # Complete stats recording - UNIFIED
            bytes_transferred = self._calculate_bytes_transferred(transaction)
            self.stats.record_transaction_complete(start_time, bytes_transferred)

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end - EXACT WORKING PATTERN
        self._assign_write_value(value=0)
        self._clear_data_bus()

    async def wait_cycles(self, cycles):
        """EXACT WORKING WAIT METHOD - DO NOT MODIFY"""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            await Timer(200, units='ps')
            if self.reset_occurring:
                break

    def _calculate_bytes_transferred(self, packet):
        """Calculate bytes for statistics - UNIFIED"""
        total_bits = packet.get_total_bits()
        return (total_bits + 7) // 8

    # Modern convenience methods
    async def send(self, packet):
        """Modern send interface"""
        await self._driver_send(packet, sync=True)
        # Wait for completion
        while self.transmit_coroutine is not None:
            await RisingEdge(self.clock)
        return True

    async def busy_send(self, transaction):
        """
        Send a transaction and wait for completion.

        Args:
            transaction: The transaction to send
        """
        await self.send(transaction)
        while self.transfer_busy:
            await self.wait_cycles(1)

    def create_packet(self, **field_values):
        """Create a packet with specified field values"""
        packet = FIFOPacket(self.field_config)
        for field_name, value in field_values.items():
            if hasattr(packet, field_name):
                setattr(packet, field_name, value)
        return packet

    # Memory operations using base MemoryModel directly
    async def write_to_memory(self, packet):
        """Write packet to memory using unified memory integration"""
        success, error = self.write_to_memory_unified(packet)
        if not success:
            self.log.error(f"FIFOMaster: Memory write failed: {error}")
            self.stats.record_transaction_failed("memory_write_error", error)
        return success

    async def read_from_memory(self, packet):
        """Read data from memory using unified memory integration"""
        success, data, error = self.read_from_memory_unified(packet, update_transaction=True)
        if not success:
            self.log.error(f"FIFOMaster: Memory read failed: {error}")
            self.stats.record_transaction_failed("memory_read_error", error)
        return success, data

    def get_stats(self):
        """Get comprehensive statistics - UNIFIED"""
        stats = self.get_base_stats_unified()
        stats.update({
            'master_stats': self.stats.get_stats(),
            'transfer_busy': self.transfer_busy,
            'queue_depth': len(self.transmit_queue)
        })
        return stats

    def __str__(self):
        """String representation"""
        return f"FIFOMaster '{self.title}': {self.stats}"
