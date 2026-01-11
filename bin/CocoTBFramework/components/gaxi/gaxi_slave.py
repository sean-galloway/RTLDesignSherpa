# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: GAXISlave
# Purpose: GAXISlave with Integrated Structured Pipeline
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
GAXISlave with Integrated Structured Pipeline

Maintains all existing functionality and timing while adding better
debugging and error recovery through structured pipeline phases.

FIXED: Removed double initialization and fixed attribute access issues.
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.utils import get_sim_time

from .gaxi_monitor_base import GAXIMonitorBase
from ..shared.monitor_statistics import MonitorStatistics
from .gaxi_packet import GAXIPacket


class GAXISlave(GAXIMonitorBase):
    """
    GAXI Slave with integrated structured pipeline for better debugging and error recovery.

    Inherits all common functionality from GAXIMonitorBase:
    - Signal resolution and data collection setup
    - Clean _get_data_dict() with automatic field unpacking
    - Unified _finish_packet() without conditional mess
    - Packet creation and statistics
    - Memory model integration using base MemoryModel directly

    Enhanced pipeline features:
    - Structured receive phase transitions with debugging
    - Better error recovery and timeout handling
    - Optional pipeline debugging for troubleshooting
    - Active ready signal driving with timing control
    - Maintains exact timing compatibility with existing code

    FIXED: Removed double initialization and attribute access issues.
    """

    def __init__(self, dut, title, prefix, clock, field_config,
                    timeout_cycles=1000, mode='skid',

                    bus_name='',
                    pkt_prefix='',
                    multi_sig=False,
                    randomizer=None, memory_model=None, log=None,
                    super_debug=False, pipeline_debug=False,
                    signal_map=None, protocol_type='gaxi_slave', **kwargs):
        """
        Initialize GAXI Slave with structured pipeline support.

        Args:
            dut: Device under test
            title: Component title/name
            prefix: Bus prefix
            clock: Clock signal
            field_config: Field configuration
            timeout_cycles: Timeout for operations
            mode: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
            bus_name: Bus/channel name
            pkt_prefix: Packet field prefix
            multi_sig: Whether using multi-signal mode
            randomizer: Optional randomizer for ready delays
            memory_model: Optional memory model for transactions
            log: Logger instance
            super_debug: Enable detailed debugging
            pipeline_debug: Enable pipeline phase debugging
            **kwargs: Additional arguments
        """
        # CRITICAL: Set pipeline attributes FIRST before any method calls
        # This prevents "pipeline_debug does not exist" errors in _log_pipeline_transition
        self.pipeline_debug = pipeline_debug or super_debug
        self.receive_state = "idle"
        self.phase_timings = {}
        self.phase_statistics = {
            'phase1_count': 0,
            'phase2_count': 0,
            'phase3_count': 0,
            'handshake_count': 0,
            'deferred_captures': 0,
            'immediate_captures': 0,
            'memory_operations': 0,
            'error_count': 0
        }

        # FIXED: Only call parent initialization once
        # GAXIMonitorBase already handles BusMonitor.__init__ and complete_base_initialization
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
            protocol_type=protocol_type,  # Use the provided protocol type
            memory_model=memory_model,
            randomizer=randomizer,
            log=log,
            super_debug=super_debug,
            signal_map=signal_map,
            **kwargs
        )

        # REMOVED: Double initialization calls that were breaking the slave
        # These were already handled by GAXIMonitorBase:
        # - BusMonitor.__init__() 
        # - self.complete_base_initialization()
        # - self.log setup

        # Slave-specific attributes
        self.tick_delay = 100
        self.tick_units = 'ps'
        self.timeout_cycles = timeout_cycles
        self.reset_occurring = False

        # Override statistics with monitor statistics (same as before)
        self.stats = MonitorStatistics()

        # Slave-specific initialization - callbacks for compatibility
        self.callbacks = []

        # Initialize signals safely without async
        self._initialize_signals()

        self.log.info(f"GAXISlave '{title}' initialized: mode={mode}, "
                        f"multi_sig={self.use_multi_signal}, "
                        f"pipeline_debug={self.pipeline_debug}")

    def _initialize_signals(self):
        """Initialize signals to safe values - NO ASYNC"""
        try:
            # Initialize ready signal using inherited signal resolver
            if hasattr(self, 'ready_sig') and self.ready_sig is not None:
                self.ready_sig.setimmediatevalue(0)

        except Exception as e:
            self.log.error(f"GAXISlave '{self.title}': Error initializing signals: {e}")

    def _log_pipeline_transition(self, from_state: str, to_state: str, reason: str = "", **context):
        """Log pipeline state transitions with timing"""
        # FIXED: Safe attribute access - pipeline_debug is now guaranteed to exist
        if self.pipeline_debug:
            current_time = get_sim_time('ns')
            self.receive_state = to_state
            self.phase_timings[to_state] = current_time
            
            context_str = ", ".join(f"{k}={v}" for k, v in context.items()) if context else ""
            reason_str = f" ({reason})" if reason else ""
            context_suffix = f" [{context_str}]" if context_str else ""
            
            self.log.debug(f"Slave({self.title}) Pipeline: {from_state} -> {to_state}{reason_str}{context_suffix} @ {current_time}ns")

    async def reset_bus(self):
        """Reset bus with enhanced pipeline state management"""
        self.log.debug(f"GAXISlave({self.title}): resetting the bus")
        self._log_pipeline_transition("any", "reset", "bus reset requested")
        
        self.reset_occurring = True
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        await RisingEdge(self.clock)
        self.reset_occurring = False

        # Deassert ready signal
        self._set_ready(0)

        # Clear any queued transactions
        self._recvQ.clear()
        
        self._log_pipeline_transition("reset", "idle", "reset complete")

    def _set_ready(self, value):
        """Set ready signal with pipeline state awareness"""
        if hasattr(self, 'ready_sig') and self.ready_sig is not None:
            self.ready_sig.value = value
            if self.pipeline_debug:
                self.log.debug(f"Slave({self.title}): ready <= {value}")

    async def _monitor_recv(self):
        """
        Enhanced monitoring receive with structured phases and better debugging.
        
        Maintains exact timing behavior while adding structured phases,
        better error recovery, and optional debugging.
        """
        try:
            self._log_pipeline_transition("idle", "monitor_start", "starting receive monitoring")
            
            last_packet = None
            last_xfer = False

            while True:
                # Enhanced recv phase 1: Handle pending transactions
                self._log_pipeline_transition("cycle_start", "phase1", "handle pending transactions")
                current_time = await self._recv_phase1(last_packet, last_xfer)
                
                # Always clear the last transfer here
                last_xfer = False

                # Enhanced recv phase 2: Handle ready delays and assert ready if valid
                self._log_pipeline_transition("phase1", "phase2", "handle ready timing")
                await self._recv_phase2()

                # Enhanced recv phase 3: Check for valid handshake and process transaction
                self._log_pipeline_transition("phase2", "phase3", "check handshake and process")
                last_packet, last_xfer = await self._recv_phase3(current_time)
                
                self._log_pipeline_transition("phase3", "cycle_end", "cycle complete", 
                                            last_xfer=last_xfer, has_pending=last_packet is not None)

        except Exception as e:
            self.log.error(f"Slave({self.title}) Exception in _monitor_recv: {e}")
            self._log_pipeline_transition("any", "error_recovery", f"exception: {e}")
            self.phase_statistics['error_count'] += 1
            import traceback
            self.log.error(traceback.format_exc())
            raise

    async def _recv_phase1(self, last_packet, last_xfer):
        """
        Enhanced Phase 1: Handle pending transactions with better debugging.
        Maintains exact original timing and logic.
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase1_count'] += 1
        
        # Wait a brief moment for signal stability - exact original logic
        await Timer(200, units='ps')
        current_time = get_sim_time('ns')

        # Check if last transfer is pending (fifo_flop mode)
        if last_xfer:
            if self.pipeline_debug:
                self.log.debug(f"Slave({self.title}) Phase1: processing deferred capture from fifo_flop mode")
            
            self.phase_statistics['deferred_captures'] += 1
            packet = last_packet

            # Use inherited clean _get_data_dict() and _finish_packet()
            data_dict = self._get_data_dict()
            self._finish_packet(current_time, packet, data_dict)
            
            if self.pipeline_debug:
                self.log.debug(f"Slave({self.title}) Phase1: deferred capture completed")

        if self.pipeline_debug:
            phase_duration = get_sim_time('ns') - phase_start
            self.log.debug(f"Slave({self.title}) Phase1: completed in {phase_duration}ns")

        return current_time

    async def _recv_phase2(self):
        """
        Enhanced Phase 2: Handle ready timing with better debugging.
        Maintains exact original timing and logic.
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase2_count'] += 1
        
        # Check if valid on this cycle, if so we can't drop ready - exact original logic
        if not (hasattr(self, 'valid_sig') and self.valid_sig is not None and
                hasattr(self, 'ready_sig') and self.ready_sig is not None and
                self.valid_sig.value.is_resolvable and
                self.ready_sig.value.is_resolvable and
                self.valid_sig.value.integer == 1 and
                self.ready_sig.value.integer == 1):

            # Wait for valid to assert to decide to delay the ready
            if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
                self.valid_sig.value.is_resolvable):
                
                wait_cycles = 0
                while self.valid_sig.value.integer == 0:
                    await self.wait_cycles(1)
                    wait_cycles += 1
                    if self.pipeline_debug and wait_cycles == 1:
                        self.log.debug(f"Slave({self.title}) Phase2: waiting for valid assertion")

            # Determine ready delay for this cycle - using inherited randomizer
            delay_cfg = self.randomizer.next()
            ready_delay = delay_cfg.get('ready_delay', 0)
            
            if self.pipeline_debug and ready_delay > 0:
                self.log.debug(f"Slave({self.title}) Phase2: applying ready delay {ready_delay} cycles")
            
            if ready_delay > 0:
                # Deassert ready during delay
                self._set_ready(0)
                await self.wait_cycles(ready_delay)

        # Assert ready to accept data
        self._set_ready(1)
        
        if self.pipeline_debug:
            self.log.debug(f"Slave({self.title}) Phase2: ready asserted, waiting for falling edge")

        # Wait for a falling edge to sample signals
        await FallingEdge(self.clock)
        
        if self.pipeline_debug:
            phase_duration = get_sim_time('ns') - phase_start
            self.log.debug(f"Slave({self.title}) Phase2: completed in {phase_duration}ns")

    async def _recv_phase3(self, current_time):
        """
        Enhanced Phase 3: Transaction processing with better debugging.
        Maintains exact original timing and logic.
        
        Returns:
            Tuple of (last_packet, last_xfer) for deferred processing
        """
        phase_start = get_sim_time('ns')
        self.phase_statistics['phase3_count'] += 1
        
        # Check for valid handshake (valid=1 and ready=1) - exact original logic
        if (hasattr(self, 'valid_sig') and self.valid_sig is not None and
            hasattr(self, 'ready_sig') and self.ready_sig is not None and
            self.valid_sig.value.is_resolvable and
            self.ready_sig.value.is_resolvable and
            self.valid_sig.value.integer == 1 and
            self.ready_sig.value.integer == 1):

            if self.pipeline_debug:
                self.log.debug(f"Slave({self.title}) Phase3: handshake detected, processing transaction")

            self.phase_statistics['handshake_count'] += 1

            # Create a new packet
            packet = GAXIPacket(self.field_config)
            packet.start_time = current_time

            # Record transaction received (using MonitorStatistics interface)
            received_time = get_sim_time('ns')

            if self.mode == 'fifo_flop':
                # 'fifo_flop' mode: note handshake time, defer data capture to next cycle
                if self.pipeline_debug:
                    self.log.debug(f"Slave({self.title}) Phase3: fifo_flop mode - deferring data capture")
                
                last_xfer = True
                last_packet = packet
                await RisingEdge(self.clock)
                await Timer(self.tick_delay, units=self.tick_units)
                
                if self.pipeline_debug:
                    phase_duration = get_sim_time('ns') - phase_start
                    self.log.debug(f"Slave({self.title}) Phase3: deferred setup completed in {phase_duration}ns")
                
                return last_packet, last_xfer
            else:
                # In skid/fifo_mux mode, capture data in the same cycle
                if self.pipeline_debug:
                    self.log.debug(f"Slave({self.title}) Phase3: {self.mode} mode - immediate capture")
                
                self.phase_statistics['immediate_captures'] += 1
                
                # Use inherited clean _get_data_dict() and _finish_packet()
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)

                # Record transaction processed (using MonitorStatistics interface)
                self.stats.transactions_observed += 1

                # Trigger coverage hooks for received transaction
                self._trigger_coverage_hooks(packet, 'rx')

                # Handle memory operations if memory model available
                if self.memory_model:
                    if self.pipeline_debug:
                        self.log.debug(f"Slave({self.title}) Phase3: performing memory operation")
                    
                    # Use unified memory integration
                    success = self.handle_memory_write(packet)
                    if success:
                        self.phase_statistics['memory_operations'] += 1

        # Deassert ready on the rising edge (prepare for next cycle or delay)
        await RisingEdge(self.clock)
        await Timer(self.tick_delay, units=self.tick_units)
        self._set_ready(0)
        
        if self.pipeline_debug:
            phase_duration = get_sim_time('ns') - phase_start
            self.log.debug(f"Slave({self.title}) Phase3: completed in {phase_duration}ns")

        # Default return values
        return None, False

    async def wait_cycles(self, cycles):
        """Enhanced wait method with reset awareness and debugging"""
        if self.pipeline_debug and cycles > 1:
            self.log.debug(f"Slave({self.title}): waiting {cycles} cycles")
        
        for cycle in range(cycles):
            await RisingEdge(self.clock)
            if self.reset_occurring:
                if self.pipeline_debug:
                    self.log.debug(f"Slave({self.title}): wait_cycles interrupted by reset at cycle {cycle}")
                break

        await Timer(self.tick_delay, units=self.tick_units)

    def get_pipeline_stats(self):
        """Get pipeline-specific statistics"""
        stats = self.phase_statistics.copy()
        stats.update({
            'current_state': self.receive_state,
            'pipeline_debug_enabled': self.pipeline_debug,
            'observed_packets': len(self._recvQ),
            'mode': self.mode
        })
        
        # Calculate derived statistics
        if stats['handshake_count'] > 0:
            stats['deferred_capture_rate'] = stats['deferred_captures'] / stats['handshake_count']
            stats['immediate_capture_rate'] = stats['immediate_captures'] / stats['handshake_count']
        else:
            stats['deferred_capture_rate'] = 0.0
            stats['immediate_capture_rate'] = 0.0
            
        return stats

    def get_stats(self):
        """Get comprehensive statistics including pipeline stats"""
        base_stats = self.get_base_stats()
        base_stats.update({
            'slave_stats': self.stats.get_stats(),
            'pipeline_stats': self.get_pipeline_stats()
        })
        return base_stats

    def enable_pipeline_debug(self, enable=True):
        """Enable or disable pipeline debugging at runtime"""
        self.pipeline_debug = enable
        if enable:
            self.log.info(f"Slave({self.title}): Pipeline debugging enabled")
        else:
            self.log.info(f"Slave({self.title}): Pipeline debugging disabled")

    def get_pipeline_debug_info(self):
        """Get detailed pipeline debug information"""
        return {
            'current_state': self.receive_state,
            'phase_timings': self.phase_timings.copy(),
            'phase_statistics': self.phase_statistics.copy(),
            'observed_packets': len(self._recvQ),
            'mode': self.mode,
            'debug_enabled': self.pipeline_debug
        }

    def add_callback(self, callback):
        """Add callback for received transactions (compatibility)"""
        if callback not in self.callbacks:
            self.callbacks.append(callback)
            # Also add to inherited BusMonitor callback system
            super().add_callback(callback)

    def remove_callback(self, callback):
        """Remove callback (compatibility)"""
        if callback in self.callbacks:
            self.callbacks.remove(callback)

    def clear_observed_packets(self):
        """Clear observed packets queue"""
        self._recvQ.clear()
        if self.pipeline_debug:
            self.log.debug(f"Slave({self.title}): Observed packets queue cleared")

    def get_observed_packets(self, count=None):
        """Get observed packets"""
        if count is None:
            return list(self._recvQ)
        return list(self._recvQ)[-count:]

    def __str__(self):
        """String representation with pipeline state"""
        base_str = f"GAXISlave '{self.title}': {self.stats.received_transactions} transactions"
        if self.pipeline_debug:
            base_str += f" [Pipeline: {self.receive_state}]"
        return base_str