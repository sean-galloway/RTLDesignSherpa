# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXIMaster
# Purpose: GAXIMaster with Integrated Structured Pipeline
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXIMaster with Integrated Structured Pipeline

Maintains all existing functionality and timing while adding better
debugging and error recovery through structured pipeline phases.
"""

import cocotb
from collections import deque
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge, Timer
from cocotb.utils import get_sim_time

from ..shared.master_statistics import MasterStatistics
from .gaxi_component_base import GAXIComponentBase
from .gaxi_packet import GAXIPacket


class GAXIMaster(GAXIComponentBase, BusDriver):
    """
    GAXI Master with integrated structured pipeline for better debugging and error recovery.

    Inherits common functionality from GAXIComponentBase:
    - Signal resolution and data driving setup
    - Unified field configuration handling
    - Memory model integration using base MemoryModel directly
    - Statistics and logging patterns

    Enhanced pipeline features:
    - Structured phase transitions with debugging
    - Better error recovery and timeout handling
    - Optional pipeline debugging for troubleshooting
    - Maintains exact timing compatibility with existing code
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                timeout_cycles=1000, mode='skid',
                bus_name='', pkt_prefix='', multi_sig=False,
                randomizer=None, memory_model=None, log=None,
                super_debug=False, pipeline_debug=False,
                signal_map=None, protocol_type='gaxi_master', **kwargs):
        """
        Initialize GAXI Master with structured pipeline support.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            timeout_cycles: Maximum cycles to wait for responses
            mode: Protocol mode ('skid', 'blocking', etc.)
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: FlexRandomizer instance for delays
            memory_model: Memory model for testing
            log: Logger instance
            super_debug: Enable detailed debugging
            pipeline_debug: Enable pipeline-specific debugging
            signal_map: Optional manual signal mapping
            **kwargs: Additional arguments for BusDriver
        """
        # Initialize base class with all parameters preserved
        GAXIComponentBase.__init__(
            self,
            dut=dut,
            title=title,
            prefix=prefix,  # Keep for our internal signal discovery
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

        self.timeout_cycles = timeout_cycles

        # Pipeline logging and state tracking
        self.pipeline_debug = pipeline_debug or super_debug
        self.pipeline_state = "idle"
        self.reset_occurring = False  # Track reset state
        self.phase_timings = {}
        self.phase_statistics = {
            'phase1_count': 0,
            'phase2_count': 0,
            'phase3_count': 0,
            'timeout_count': 0,
            'error_count': 0
        }

        # Remove custom parameters that shouldn't go to BusDriver
        custom_params = ['bus_name', 'pkt_prefix', 'memory_model', 'randomizer',
                        'signal_map', 'super_debug', 'pipeline_debug']
        for param in custom_params:
            kwargs.pop(param, None)

        # Remove prefix from kwargs so it doesn't get passed to BusDriver/BusMonitor
        kwargs.pop('prefix', None)

        # CLEAN APPROACH: Explicitly pass empty prefix to cocotb
        # Our signal lists already contain full signal names
        BusDriver.__init__(self, dut, '', clock, **kwargs)
        self.log = log or self._log

        # Complete base class initialization now that bus is available
        self.complete_base_initialization(self.bus)

        # Master-specific statistics
        self.stats = MasterStatistics()

        # Pipeline queues - exact working cocotb pattern
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"GAXIMaster '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}, "
                        f"pipeline_debug={self.pipeline_debug}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize valid signal using modern signal resolver
            if hasattr(self, 'valid_sig') and self.valid_sig is not None:
                self.valid_sig.setimmediatevalue(0)

            # Clear data signals using unified data driver
            self.clear_signals_unified()

        except Exception as e:
            self.log.error(f"GAXIMaster '{self.title}': Error initializing signals: {e}")

    def _log_pipeline_transition(self, from_state: str, to_state: str, reason: str = "", **context):
        """Log pipeline state transitions with timing"""
        if self.pipeline_debug:
            current_time = get_sim_time('ns')
            self.pipeline_state = to_state
            self.phase_timings[to_state] = current_time

            context_str = ", ".join(f"{k}={v}" for k, v in context.items()) if context else ""
            reason_str = f" ({reason})" if reason else ""
            context_suffix = f" [{context_str}]" if context_str else ""

            self.log.debug(f"Master({self.title}) Pipeline: {from_state} -> {to_state}{reason_str}{context_suffix} @ {current_time}ns")

    async def reset_bus(self):
        """Reset bus with enhanced pipeline state management"""
        self.log.debug(f"Master({self.title}): resetting the bus")
        self._log_pipeline_transition("any", "reset", "bus reset requested")

        # Reset valid signal
        self._assign_valid_value(value=0)

        # Reset field signals using unified data driver
        self.clear_signals_unified()

        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Clear queues and reset pipeline state
        self.transmit_queue = deque()
        self.sent_queue = deque()
        self.transmit_coroutine = None
        self.transfer_busy = False

        self._log_pipeline_transition("reset", "idle", "reset complete")

    async def _driver_send(self, transaction, sync=True, hold=False, **kwargs):
        """
        Enhanced driver send with pipeline state tracking.
        Maintains exact cocotb driver interface and timing.
        """
        # Add transaction to queue
        self.log.debug(f'Master({self.title}): Adding transaction to queue: {transaction.formatted(compact=True)}')
        self.transmit_queue.append(transaction)

        self._log_pipeline_transition("idle", "queued", "transaction added",
                                    queue_length=len(self.transmit_queue))

        # Start transmission pipeline if not already running
        if not hold and not self.transmit_coroutine:
            self.log.debug(f'Master({self.title}): Starting new transmit pipeline, queue length: {len(self.transmit_queue)}')
            self.transmit_coroutine = cocotb.start_soon(self._transmit_pipeline())

    def _drive_signals(self, transaction):
        """Drive signals using unified data driving strategy"""
        try:
            return self.drive_transaction_unified(transaction)
        except Exception as e:
            self.log.error(f"Error driving signals: {e}")
            return False

    def _assign_valid_value(self, value):
        """Set valid signal with pipeline state awareness"""
        if hasattr(self, 'valid_sig') and self.valid_sig is not None:
            self.valid_sig.value = value
            if self.pipeline_debug:
                self.log.debug(f"Master({self.title}): valid <= {value}")

    def _clear_data_bus(self):
        """Clear data signals"""
        self.clear_signals_unified()

    async def _transmit_pipeline(self):
        """
        Enhanced transmission pipeline with structured phases and debugging.

        Maintains exact timing behavior while adding structured phases,
        better error recovery, and optional debugging.
        """
        self.log.debug(f'Master({self.title}): Transmit pipeline started, queue length: {len(self.transmit_queue)}')
        self._log_pipeline_transition("queued", "pipeline_active", "starting transmission pipeline")

        self.transfer_busy = True
        await self.wait_cycles(1)  # Exact original timing

        while len(self.transmit_queue):
            transaction = self.transmit_queue.popleft()
            transaction.start_time = get_sim_time('ns')

            self._log_pipeline_transition("pipeline_active", "transaction_start", "processing transaction",
                                        transaction_id=id(transaction))

            # Record transaction start for statistics
            start_time = self.stats.record_transaction_start()

            try:
                # Phase 1: Apply delay with structured error handling
                self._log_pipeline_transition("transaction_start", "phase1", "applying delays")
                await self._xmit_phase1()

                # Phase 2: Drive signals and wait for handshake
                self._log_pipeline_transition("phase1", "phase2", "driving signals and waiting for handshake")
                success = await self._xmit_phase2(transaction)

                if not success:
                    self._log_pipeline_transition("phase2", "error_recovery", "handshake failed or timeout")
                    continue  # Skip to next transaction

                # Phase 3: Complete transfer
                self._log_pipeline_transition("phase2", "phase3", "completing transfer")
                await self._xmit_phase3(transaction)

                # Complete statistics recording
                bytes_transferred = self._calculate_bytes_transferred(transaction)
                self.stats.record_transaction_complete(start_time, bytes_transferred)

                self._log_pipeline_transition("phase3", "transaction_complete", "transaction successful")

            except Exception as e:
                self.log.error(f"Master({self.title}) Pipeline exception: {e}")
                self._log_pipeline_transition("any", "error_recovery", f"exception: {e}")

                # Error recovery - ensure signals are clean
                self._assign_valid_value(0)
                self._clear_data_bus()
                self.stats.record_transaction_failed("pipeline_exception", str(e))
                self.phase_statistics['error_count'] += 1

        self.log.debug(f"Master({self.title}) Transmit pipeline completed")
        self._log_pipeline_transition("pipeline_active", "idle", "queue empty")

        self.transfer_busy = False
        self.transmit_coroutine = None

        # Ensure signals are deasserted at the end
        self._assign_valid_value(0)
        self._clear_data_bus()

    async def _xmit_phase1(self):
        """
        Phase 1: Apply delay with enhanced debugging and statistics.
        Maintains exact original timing and logic.
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase1_count'] += 1

        # Get delay from randomizer - exact original logic
        delay_dict = self.randomizer.next()
        valid_delay = delay_dict.get('valid_delay', 0)

        if self.pipeline_debug:
            self.log.debug(f"Master({self.title}) Phase1: applying delay {valid_delay} cycles")

        if valid_delay > 0:
            # Deassert valid and clear data - exact original logic
            self._assign_valid_value(0)
            self._clear_data_bus()
            await self.wait_cycles(valid_delay)

        if self.pipeline_debug:
            phase_duration = get_sim_time('ns') - phase_start
            self.log.debug(f"Master({self.title}) Phase1: completed in {phase_duration}ns")

    async def _xmit_phase2(self, transaction):
        """
        Phase 2: Drive signals and wait for handshake with enhanced error handling.
        Maintains exact original timing and logic.

        Returns:
            bool: True if handshake successful, False if timeout or error
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase2_count'] += 1

        # Drive signals for this transaction
        if not self._drive_signals(transaction):
            self.log.error(f"Failed to drive signals for transaction: {transaction.formatted(compact=True)}")
            self.phase_statistics['error_count'] += 1
            return False

        # Assert valid for this transaction
        self._assign_valid_value(1)

        if self.pipeline_debug:
            self.log.debug(f"Master({self.title}) Phase2: signals driven, waiting for handshake")

        # Wait for handshake - exact original pattern
        timeout_counter = 0
        while timeout_counter < self.timeout_cycles:
            # Wait for rising edge first
            await RisingEdge(self.clock)
            timeout_counter += 1

            # Check if ready is asserted at this clock edge
            if hasattr(self, 'ready_sig') and self.ready_sig is not None:
                if self.ready_sig.value:
                    if self.pipeline_debug:
                        phase_duration = get_sim_time('ns') - phase_start
                        self.log.debug(f"Master({self.title}) Phase2: handshake detected at cycle {timeout_counter}, "
                                     f"duration {phase_duration}ns")
                    return True
            else:
                # No ready signal - single cycle transfer
                if self.pipeline_debug:
                    self.log.debug(f"Master({self.title}) Phase2: no ready signal, single cycle transfer")
                return True

        # Timeout occurred
        self.log.error(f"Master({self.title}) Phase2: TIMEOUT waiting for ready after {self.timeout_cycles} cycles")
        self.phase_statistics['timeout_count'] += 1

        # Stop driving if timeout (prevent hang)
        self._assign_valid_value(0)
        self._clear_data_bus()

        # Update stats
        self.stats.record_timeout()

        return False

    async def _xmit_phase3(self, transaction):
        """
        Phase 3: Complete transfer with enhanced logging and statistics.
        Maintains exact original timing and logic.
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase3_count'] += 1

        # Handshake completed – capture completion time
        current_time_ns = get_sim_time('ns')
        transaction.end_time = current_time_ns

        if self.pipeline_debug:
            transaction_duration = current_time_ns - transaction.start_time
            self.log.debug(f"Master({self.title}) Phase3: transaction completed in {transaction_duration}ns")

        self.log.debug(f"Master({self.title}) Transaction completed at {current_time_ns}ns: "
                      f"{transaction.formatted(compact=True)}")

        self.sent_queue.append(transaction)

        # Deassert valid
        self._assign_valid_value(0)

        # Clear the data bus
        self._clear_data_bus()

        if self.pipeline_debug:
            phase_duration = get_sim_time('ns') - phase_start
            self.log.debug(f"Master({self.title}) Phase3: cleanup completed in {phase_duration}ns")

    async def wait_cycles(self, cycles):
        """Enhanced wait method with reset awareness"""
        for _ in range(cycles):
            await RisingEdge(self.clock)
            await Timer(200, units='ps')
            if self.reset_occurring:
                if self.pipeline_debug:
                    self.log.debug(f"Master({self.title}): wait_cycles interrupted by reset")
                break

    def _calculate_bytes_transferred(self, packet):
        """Calculate bytes for statistics"""
        total_bits = packet.get_total_bits()
        return (total_bits + 7) // 8

    # Enhanced convenience methods
    async def send(self, packet):
        """Send a packet and wait for completion"""
        await self._driver_send(packet, sync=True)
        # Wait for completion
        while self.transmit_coroutine is not None:
            await RisingEdge(self.clock)
        return True

    async def busy_send(self, transaction):
        """Send a transaction and wait for completion"""
        await self.send(transaction)
        while self.transfer_busy:
            await self.wait_cycles(1)

    def create_packet(self, **field_values):
        """Create a packet with specified field values"""
        packet = GAXIPacket(self.field_config)
        for field_name, value in field_values.items():
            if hasattr(packet, field_name):
                setattr(packet, field_name, value)
        return packet

    # Memory operations using base MemoryModel directly
    async def write_to_memory(self, packet):
        """Write packet to memory using unified memory integration"""
        success, error = self.write_to_memory_unified(packet)
        if not success:
            self.log.error(f"GAXIMaster: Memory write failed: {error}")
            self.stats.record_transaction_failed("memory_write_error", error)
        return success

    async def read_from_memory(self, packet):
        """Read data from memory using unified memory integration"""
        success, data, error = self.read_from_memory_unified(packet, update_transaction=True)
        if not success:
            self.log.error(f"GAXIMaster: Memory read failed: {error}")
            self.stats.record_transaction_failed("memory_read_error", error)
        return success, data

    def get_pipeline_stats(self):
        """Get pipeline-specific statistics"""
        stats = self.phase_statistics.copy()
        stats.update({
            'current_state': self.pipeline_state,
            'queue_depth': len(self.transmit_queue),
            'transfer_busy': self.transfer_busy,
            'pipeline_debug_enabled': self.pipeline_debug
        })
        return stats

    def get_stats(self):
        """Get comprehensive statistics including pipeline stats"""
        stats = self.get_base_stats_unified()
        stats.update({
            'master_stats': self.stats.get_stats(),
            'pipeline_stats': self.get_pipeline_stats()
        })
        return stats

    def enable_pipeline_debug(self, enable=True):
        """Enable or disable pipeline debugging at runtime"""
        self.pipeline_debug = enable
        if enable:
            self.log.info(f"Master({self.title}): Pipeline debugging enabled")
        else:
            self.log.info(f"Master({self.title}): Pipeline debugging disabled")

    def get_pipeline_debug_info(self):
        """Get detailed pipeline debug information"""
        return {
            'current_state': self.pipeline_state,
            'phase_timings': self.phase_timings.copy(),
            'phase_statistics': self.phase_statistics.copy(),
            'queue_length': len(self.transmit_queue),
            'sent_count': len(self.sent_queue),
            'debug_enabled': self.pipeline_debug
        }

    def __str__(self):
        """String representation with pipeline state"""
        base_str = f"GAXIMaster '{self.title}': {self.stats}"
        if self.pipeline_debug:
            base_str += f" [Pipeline: {self.pipeline_state}]"
        return base_str
