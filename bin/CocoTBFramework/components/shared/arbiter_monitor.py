# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: ArbiterMonitor
# Purpose: Unified Arbiter Monitor supporting both weighted and non-weighted arbiters
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Unified Arbiter Monitor supporting both weighted and non-weighted arbiters
Automatically adapts based on is_weighted parameter with cycle-level grant reporting
"""

import cocotb
from collections import deque, namedtuple
from cocotb.triggers import FallingEdge, RisingEdge, Timer
from cocotb.utils import get_sim_time
from cocotb.log import SimLog
from cocotb_bus.monitors import BusMonitor
# Import the compliance checker
from .arbiter_compliance import ArbiterCompliance


# Define Transaction type for arbiters
ArbiterTransaction = namedtuple('ArbiterTransaction', [
    'req_vector',      # Request vector from clients (current at time of grant)
    'last_req_vector', # Request vector from previous cycle (for compliance checking)
    'gnt_vector',      # Grant vector indicating which client was selected
    'gnt_id',          # ID of the granted client
    'cycle_count',     # Number of cycles between request and grant
    'timestamp',       # Timestamp when grant was issued
    'weights',         # Current weights at time of grant (None for non-weighted)
    'metadata'         # Dictionary for any additional metadata
])

# Signal state container for cleaner code
SignalState = namedtuple('SignalState', [
    'current_time',
    'req_vector', 'prev_req_vector', 'request_changed',
    'gnt_valid', 'gnt_vector', 'gnt_id', 'grant_changed',
    'ack_vector', 'prev_ack_vector', 'ack_detected',
    'block_arb', 'prev_block_arb', 'block_arb_changed',
    'weights', 'prev_weights', 'weights_changed'
])


class ArbiterMonitor(BusMonitor):
    """
    Unified Arbiter Monitor supporting both weighted and non-weighted arbiters.

    Automatically adapts to weighted mode based on is_weighted parameter.
    Maintains backward compatibility - existing non-weighted testbenches work unchanged.
    """

    # Define signals required by cocotb BusMonitor
    _signals = [
        "request",          # Request input signal (bus)
        "grant_valid",      # Grant valid output signal
        "grant",           # Grant output signal (bus)
        "grant_id",        # Grant ID output signal
    ]

    _optional_signals = [
        "grant_ack",       # Grant acknowledge input signal (bus), optional
        "block_arb",       # Signal to block arbitration, optional
        "max_thresh",      # Maximum threshold signal for weighted arbiters, optional
        "last_grant"       # Last grant signal for debugging, optional
    ]

    def __init__(self, entity, name, clock, reset_n,
                clients=None, is_weighted=False, ack_mode=False, log=None,
                clock_period_ns=10, callback=None, event=None, **kwargs):
        """
        Initialize Unified Arbiter Monitor supporting both weighted and non-weighted arbiters.

        Args:
            entity: Device under test
            name: Component name (for bus signal resolution)
            clock: Clock signal
            reset_n: Reset signal (active low)
            clients: Number of clients (derived from signal width if None)
            is_weighted: True for weighted arbiters, False for regular (defaults to False for compatibility)
            ack_mode: True if arbiter uses ACK protocol, False otherwise
            log: Logger instance (creates new if None)
            clock_period_ns: Clock period in nanoseconds
            callback: Callback to be called with each transaction (cocotb pattern)
            event: Event that will be called when transaction received (cocotb pattern)
            **kwargs: Additional arguments for BusMonitor
        """

        # Initialize parent BusMonitor first
        super().__init__(entity, name, clock, reset=None, reset_n=reset_n,
                        callback=callback, event=event, **kwargs)

        # Store title for consistent logging
        self.title = name
        self.is_weighted = is_weighted  # NEW: Auto-detect weighted vs non-weighted
        self.ack_mode = ack_mode
        self.clock_period_ns = clock_period_ns
        self.reset_cycles = 2

        # Override logger if provided (maintaining cocotb BusMonitor's logger setup)
        if log:
            self.log = log

        # Determine number of clients from signal width if not specified
        if clients is None:
            try:
                if hasattr(self.bus, 'request'):
                    req_signal = self.bus.request
                    if hasattr(req_signal, '_range'):
                        self.clients = len(req_signal._range)
                    else:
                        val = req_signal.value
                        if hasattr(val, 'binstr'):
                            self.clients = len(val.binstr)
                        else:
                            self.clients = val.n_bits
                else:
                    raise AttributeError("No request signal found")
            except (AttributeError, TypeError):
                self.log.warning(f"ArbiterMonitor({name}): Could not determine number of clients from request signal width, using default of 4")
                self.clients = 4
        else:
            self.clients = int(clients)

        # Initialize compliance checker with weight support
        compliance_type = 'wrr' if is_weighted else 'rr'
        self.compliance = ArbiterCompliance(
            name=f"{name}_compliance",
            clients=self.clients,
            arbiter_type=compliance_type,
            ack_mode=ack_mode,
            log=self.log,
            clock_period_ns=clock_period_ns
        )

        # Transaction tracking (in addition to cocotb's _recvQ)
        self.transactions = deque(maxlen=1000)
        self.pending_requests = {}
        self.total_transactions = 0
        self.active_request_vector = 0

        # Block arbitration history tracking
        self.block_arb_history = deque(maxlen=50)
        self.current_block_state = False
        self.last_block_transition_time = 0

        # Signal state tracking (sampled on falling edge only)
        self.blocked = False
        self.current_weights = 0  # NEW: Current weight configuration
        self.weight_history = deque(maxlen=100)  # NEW: Track weight changes

        # Basic counters and statistics
        self.arbiter_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'avg_wait_time': 0,
            'wait_time_per_client': [0] * self.clients,
            'total_cycles': 0,
            'grant_sequences': [],
        }

        # NEW: Weight-specific statistics (only used if is_weighted=True)
        if self.is_weighted:
            self.weight_stats = {
                'weight_changes': 0,
                'weight_distribution_windows': {},  # Track distribution over different windows
                'weight_compliance_history': deque(maxlen=1000),
                'static_period_active': False,
                'static_period_start': 0,
                'static_period_stats': {
                    'grants_per_client': [0] * self.clients,
                    'expected_weights': [1] * self.clients
                }
            }

        # Compatibility tracking
        self.grant_history = []

        # Control flags
        self.monitoring_enabled = True
        self.debug_enabled = True

        # Previous state tracking for change detection
        self._prev_state = {
            'req_vector': 0,
            'gnt_valid': False,
            'gnt_vector': 0,
            'gnt_id': 0,
            'ack_vector': 0,
            'block_arb': False,
            'weights': 0  # NEW: Track weight changes
        }

        # Grant tracking for transaction creation
        self._last_grant_info = {'gnt_vec': 0, 'gnt_id': 0, 'gnt_valid': False}

        # Cycle-level reporting configuration
        self.cycle_level_reporting = True

        # ACK mode state tracking for cycle-level reporting
        self._ack_mode_state = {}
        if self.ack_mode:
            for i in range(self.clients):
                self._ack_mode_state[i] = {
                    'grant_active': False,
                    'grant_start_time': 0,
                    'waiting_for_ack': False,
                    'last_grant_reported': 0
                }

        # Log initialization with weight support indication
        weight_indicator = "weighted" if self.is_weighted else "standard"
        self.log.info(f"ArbiterMonitor({self.title}): Unified monitor initialized - {weight_indicator} mode, "
                    f"{self.clients} clients, ack_mode={self.ack_mode}, "
                    f"cycle_level_reporting={self.cycle_level_reporting}{self.get_time_ns_str()}")

    @staticmethod
    def get_time_ns_str():
        """Get current simulation time as a formatted string"""
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    def enable_debug(self, enable=True):
        """Enable or disable debug logging"""
        self.debug_enabled = enable
        self.compliance.enable_debug(enable)
        self.log.info(f"ArbiterMonitor({self.title}): Debug logging {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    def enable_protocol_checking(self, enable=True):
        """Enable or disable protocol compliance checking"""
        self.compliance.enable_protocol_checking(enable)
        self.log.info(f"ArbiterMonitor({self.title}): Protocol checking {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    def enable_monitoring(self, enable=True):
        """Enable or disable monitoring"""
        self.monitoring_enabled = enable
        self.log.info(f"ArbiterMonitor({self.title}): Monitoring {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    def enable_cycle_level_reporting(self, enable=True):
        """Enable or disable cycle-level reporting"""
        self.cycle_level_reporting = enable
        self.log.info(f"ArbiterMonitor({self.title}): Cycle-level reporting {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    # =============================================================================
    # NEW: Weight-specific methods (only active if is_weighted=True)
    # =============================================================================

    def start_static_weight_period(self, expected_weights: list = None):
        """NEW: Start tracking a static weight period for compliance analysis"""
        if not self.is_weighted:
            self.log.warning(f"ArbiterMonitor({self.title}): Static weight period ignored - not a weighted arbiter")
            return

        # Start static period in compliance checker
        self.compliance.start_static_period(expected_weights)

        # Reset weight-specific stats
        self.weight_stats['static_period_active'] = True
        self.weight_stats['static_period_start'] = get_sim_time('ns')
        self.weight_stats['static_period_stats'] = {
            'grants_per_client': [0] * self.clients,
            'expected_weights': expected_weights or [1] * self.clients
        }

        self.log.info(f"ArbiterMonitor({self.title}): Static weight period started with weights {expected_weights or 'equal'}{self.get_time_ns_str()}")

    def end_static_weight_period(self):
        """NEW: End static weight period tracking"""
        if not self.is_weighted or not self.weight_stats['static_period_active']:
            return

        # End static period in compliance checker
        self.compliance.end_static_period()

        # Calculate final compliance
        duration = get_sim_time('ns') - self.weight_stats['static_period_start']
        total_grants = sum(self.weight_stats['static_period_stats']['grants_per_client'])

        self.weight_stats['static_period_active'] = False

        self.log.info(f"ArbiterMonitor({self.title}): Static weight period ended - "
                    f"{total_grants} grants over {duration:.1f}ns{self.get_time_ns_str()}")

    def analyze_current_weight_compliance(self, observation_window: int = 500):
        """NEW: Analyze weight compliance over recent observation window"""
        if not self.is_weighted:
            return {'status': 'not_weighted'}

        if observation_window not in self.weight_stats['weight_distribution_windows']:
            return {'status': 'no_data', 'message': f'No data for window size {observation_window}'}

        window_data = self.weight_stats['weight_distribution_windows'][observation_window]
        return self._calculate_weight_compliance(window_data)

    def _calculate_weight_compliance(self, window_data):
        """NEW: Calculate weight compliance metrics for a data window"""
        if not window_data['grants'] or not window_data['weights']:
            return {'status': 'insufficient_data'}

        total_grants = sum(window_data['grants'])
        if total_grants == 0:
            return {'status': 'no_grants'}

        # Use most recent weights
        current_weights = window_data['weights'][-1]
        total_weight = sum(current_weights)

        if total_weight == 0:
            return {'status': 'zero_weights'}

        # Calculate expected vs actual distribution
        expected_dist = [w / total_weight for w in current_weights]
        actual_dist = [g / total_grants for g in window_data['grants']]

        # Calculate compliance score
        compliance_scores = []
        for i in range(len(expected_dist)):
            if expected_dist[i] > 0:
                error = abs(actual_dist[i] - expected_dist[i])
                relative_error = error / expected_dist[i]
                score = max(0, 1.0 - relative_error)
            else:
                score = 1.0 if window_data['grants'][i] == 0 else 0.0
            compliance_scores.append(score)

        overall_compliance = sum(compliance_scores) / len(compliance_scores)

        return {
            'status': 'analyzed',
            'total_grants': total_grants,
            'expected_distribution': expected_dist,
            'actual_distribution': actual_dist,
            'compliance_scores': compliance_scores,
            'overall_compliance': overall_compliance,
            'compliant': overall_compliance > 0.8
        }

    def start_monitoring(self):
        """Start monitoring - compatibility method (cocotb BusMonitor starts automatically)"""
        self.enable_monitoring(True)
        self.log.info(f"ArbiterMonitor({self.title}): Monitoring started{self.get_time_ns_str()}")

    def add_transaction_callback(self, callback):
        """Add transaction callback using cocotb BusMonitor pattern"""
        self.add_callback(callback)
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Added transaction callback: {callback.__name__}{self.get_time_ns_str()}")

    def add_reset_callback(self, callback):
        """Register a callback function for reset events."""
        self.reset_callback = callback
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Added reset callback: {callback.__name__}{self.get_time_ns_str()}")

    # =============================================================================
    # MAIN MONITORING IMPLEMENTATION - Extended for weight support
    # =============================================================================

    # Override cocotb BusMonitor's _monitor_recv method
    async def _monitor_recv(self):
        """
        Main monitoring coroutine following cocotb BusMonitor paradigm.
        Extended to support weight monitoring for weighted arbiters.
        """
        # Wait for reset to be released
        while self.in_reset:
            await RisingEdge(self.clock)

        monitor_type = "weighted" if self.is_weighted else "standard"
        self.log.info(f"ArbiterMonitor({self.title}): Starting {monitor_type} monitoring with cycle-level reporting")

        # Start the unified signal monitoring coroutine
        cocotb.start_soon(self._unified_signal_monitor())

        # Start reset monitoring
        cocotb.start_soon(self._monitor_reset())

        # Start fence monitoring
        cocotb.start_soon(self._monitor_fence_conditions())

        # NEW: Start weight monitoring for weighted arbiters
        if self.is_weighted:
            cocotb.start_soon(self._weight_monitor())

        # Keep the main monitoring coroutine alive
        try:
            while True:
                await RisingEdge(self.clock)
                # Periodic housekeeping can go here if needed
        except Exception as e:
            self.log.error(f"ArbiterMonitor({self.title}): Main monitoring loop error: {e}")
            raise

    async def _unified_signal_monitor(self):
        """
        Unified signal monitoring with cycle-level grant reporting and weight support
        """
        if not self.monitoring_enabled:
            return

        sample_count = 0
        monitor_type = "weighted" if self.is_weighted else "standard"
        self.log.info(f"ArbiterMonitor({self.title}): Starting {monitor_type} signal monitor with cycle-level reporting")

        while True:
            await FallingEdge(self.clock)
            sample_count += 1

            try:
                # Sample all signals into clean state object
                signal_state = self._sample_all_signals()

                # Process each type of change with focused functions
                if signal_state.request_changed:
                    self._process_request_changes(signal_state)

                # Process grants with cycle-level reporting
                self._process_grant_changes(signal_state)

                if signal_state.ack_detected:
                    self._process_ack_changes(signal_state)

                if signal_state.block_arb_changed:
                    self._process_block_changes(signal_state)

                # NEW: Process weight changes for weighted arbiters
                if signal_state.weights_changed and self.is_weighted:
                    self._process_weight_changes(signal_state)

                # Update previous state for next cycle
                self._update_previous_state(signal_state)

                # Periodic debug logging
                if self.debug_enabled and (sample_count % 200 == 0 or signal_state.grant_changed):
                    self._log_periodic_status(signal_state, sample_count)

            except Exception as e:
                self.log.error(f"ArbiterMonitor({self.title}): Error in signal monitoring: {e}")

    def _sample_all_signals(self):
        """
        Sample all signals and return clean state object with change detection
        Extended to support weight signals for weighted arbiters
        """
        current_time = get_sim_time('ns')

        # Sample request signals
        req_vec = 0
        if hasattr(self.bus, 'request') and self.bus.request.value.is_resolvable:
            req_vec = int(self.bus.request.value)

        # Sample grant signals
        gnt_valid = False
        gnt_vec = 0
        gnt_id = 0
        if (hasattr(self.bus, 'grant_valid') and hasattr(self.bus, 'grant') and
            hasattr(self.bus, 'grant_id')):
            if (self.bus.grant_valid.value.is_resolvable and
                self.bus.grant.value.is_resolvable and
                self.bus.grant_id.value.is_resolvable):
                gnt_valid = int(self.bus.grant_valid.value) == 1
                if gnt_valid:
                    gnt_vec = int(self.bus.grant.value)
                    gnt_id = int(self.bus.grant_id.value)

        # Sample ACK signals
        ack_vec = 0
        if (self.ack_mode and hasattr(self.bus, 'grant_ack') and
            self.bus.grant_ack.value.is_resolvable):
            ack_vec = int(self.bus.grant_ack.value)

        # Sample block_arb
        block_arb = False
        if hasattr(self.bus, 'block_arb') and self.bus.block_arb.value.is_resolvable:
            block_arb = bool(int(self.bus.block_arb.value))

        # NEW: Sample weights for weighted arbiters
        weights = 0
        if (self.is_weighted and hasattr(self.bus, 'max_thresh') and
            self.bus.max_thresh.value.is_resolvable):
            weights = int(self.bus.max_thresh.value)

        # Detect changes
        prev = self._prev_state
        request_changed = (req_vec != prev['req_vector'])
        grant_changed = (gnt_valid != prev['gnt_valid'] or
                        gnt_vec != prev['gnt_vector'] or
                        gnt_id != prev['gnt_id'])
        ack_detected = (ack_vec != prev['ack_vector'] and ack_vec != 0)
        block_arb_changed = (block_arb != prev['block_arb'])
        weights_changed = (weights != prev['weights']) and self.is_weighted

        return SignalState(
            current_time=current_time,
            req_vector=req_vec, prev_req_vector=prev['req_vector'],
            request_changed=request_changed,
            gnt_valid=gnt_valid, gnt_vector=gnt_vec, gnt_id=gnt_id,
            grant_changed=grant_changed,
            ack_vector=ack_vec, prev_ack_vector=prev['ack_vector'],
            ack_detected=ack_detected,
            block_arb=block_arb, prev_block_arb=prev['block_arb'],
            block_arb_changed=block_arb_changed,
            weights=weights, prev_weights=prev['weights'],
            weights_changed=weights_changed
        )

    def _process_request_changes(self, signal_state):
        """
        Process request signal changes with compliance integration
        """
        if not signal_state.request_changed:
            return

        # Update compliance checker with request timeline
        self.compliance.update_request_timeline(
            signal_state.current_time,
            signal_state.req_vector,
            signal_state.prev_req_vector
        )

        # Update active requests
        old_requests = self.active_request_vector
        self.active_request_vector = signal_state.req_vector

        # Find new requests
        new_requests = signal_state.req_vector & ~old_requests
        if new_requests:
            for i in range(self.clients):
                if new_requests & (1 << i):
                    self.pending_requests[i] = signal_state.current_time
                    if self.debug_enabled:
                        self.log.debug(f"ArbiterMonitor({self.title}): NEW REQUEST from client {i} @ {signal_state.current_time}ns")

        # Log request changes
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): REQUEST CHANGE @ {signal_state.current_time}ns: "
                        f"0x{signal_state.prev_req_vector:x} -> 0x{signal_state.req_vector:x}")

    def _process_grant_changes(self, signal_state):
        """
        Process grant changes with cycle-level reporting
        Extended to include weight information for weighted arbiters
        """
        # Handle grant ending first
        if not signal_state.gnt_valid and self._last_grant_info['gnt_valid']:
            # Grant just ended
            if self.ack_mode:
                # Clear ACK mode states for all clients
                for i in range(self.clients):
                    if self._ack_mode_state[i]['grant_active']:
                        if self.debug_enabled:
                            self.log.debug(f"ArbiterMonitor({self.title}): ACK MODE GRANT END for client {i} @ {signal_state.current_time}ns")
                        self._ack_mode_state[i]['grant_active'] = False
                        self._ack_mode_state[i]['waiting_for_ack'] = False

            self._last_grant_info = {'gnt_vec': 0, 'gnt_id': 0, 'gnt_valid': False}
            if self.debug_enabled:
                self.log.debug(f"ArbiterMonitor({self.title}): Grant released @ {signal_state.current_time}ns")
            return

        # No grant activity if grant not valid
        if not signal_state.gnt_valid or signal_state.gnt_vector == 0:
            return

        # Get ACK information for this cycle
        ack_received_this_cycle = (signal_state.ack_detected and
                                (signal_state.ack_vector & signal_state.gnt_vector))

        if not self.ack_mode:
            # NO-ACK MODE: Report grant every cycle when grant_valid=1
            if self.debug_enabled:
                self.log.debug(f"ArbiterMonitor({self.title}): NO-ACK CYCLE GRANT to client {signal_state.gnt_id} @ {signal_state.current_time}ns")

            self._create_grant_transaction(signal_state, transaction_type="cycle_grant")

        else:
            # ACK MODE: More sophisticated grant reporting
            self._process_ack_mode_grants(signal_state, ack_received_this_cycle)

        # Update last grant info
        self._last_grant_info = {
            'gnt_vec': signal_state.gnt_vector,
            'gnt_id': signal_state.gnt_id,
            'gnt_valid': True
        }

    def _process_ack_mode_grants(self, signal_state, ack_received_this_cycle):
        """
        Process grants in ACK mode with proper cycle-level reporting
        """
        current_time = signal_state.current_time
        gnt_id = signal_state.gnt_id

        client_state = self._ack_mode_state[gnt_id]

        # Check if this is a new grant (rising edge of grant_valid for this client)
        grant_rising_edge = not client_state['grant_active']

        if grant_rising_edge:
            # NEW GRANT: First cycle of grant_valid assertion
            client_state['grant_active'] = True
            client_state['grant_start_time'] = current_time
            client_state['waiting_for_ack'] = True
            client_state['last_grant_reported'] = current_time

            if self.debug_enabled:
                self.log.debug(f"ArbiterMonitor({self.title}): ACK MODE NEW GRANT to client {gnt_id} @ {current_time}ns")

            self._create_grant_transaction(signal_state, transaction_type="new_grant")

        elif client_state['grant_active'] and ack_received_this_cycle:
            # ACK RECEIVED: Mark that ACK was received
            if client_state['waiting_for_ack']:
                client_state['waiting_for_ack'] = False

                if self.debug_enabled:
                    self.log.debug(f"ArbiterMonitor({self.title}): ACK MODE ACK RECEIVED for client {gnt_id} @ {current_time}ns")

        elif client_state['grant_active'] and not client_state['waiting_for_ack']:
            # GRANT CONTINUATION: Grant is active and ACK was already received
            time_since_last_report = current_time - client_state['last_grant_reported']

            if time_since_last_report >= self.clock_period_ns:
                client_state['last_grant_reported'] = current_time

                if self.debug_enabled:
                    self.log.debug(f"ArbiterMonitor({self.title}): ACK MODE GRANT CONTINUATION for client {gnt_id} @ {current_time}ns")

                self._create_grant_transaction(signal_state, transaction_type="grant_continuation")

    def _process_ack_changes(self, signal_state):
        """
        Process ACK signal changes
        """
        if not signal_state.ack_detected:
            return

        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): ACK DETECTED: 0x{signal_state.ack_vector:x} @ {signal_state.current_time}ns")

        # Process ACK through compliance checker
        ack_warnings = self.compliance.process_ack_received(signal_state.ack_vector, signal_state.current_time)
        if ack_warnings and self.debug_enabled:
            self.log.debug(f"ACK processing generated {len(ack_warnings)} warnings")

    def _process_block_changes(self, signal_state):
        """
        Process block_arb signal changes with history tracking
        """
        if not signal_state.block_arb_changed:
            return

        # Update block_arb history
        self.block_arb_history.append((signal_state.current_time, signal_state.block_arb))
        self.last_block_transition_time = signal_state.current_time
        self.blocked = signal_state.block_arb

        if self.debug_enabled:
            transition_type = "ASSERTED" if signal_state.block_arb else "DEASSERTED"
            self.log.debug(f"ArbiterMonitor({self.title}): block_arb {transition_type} @ {signal_state.current_time}ns")

    def _process_weight_changes(self, signal_state):
        """
        NEW: Process weight signal changes for weighted arbiters
        """
        if not signal_state.weights_changed or not self.is_weighted:
            return

        old_weights = self.current_weights
        self.current_weights = signal_state.weights

        # Decode packed weights
        decoded_weights = self._decode_weights(signal_state.weights)

        # Track weight change
        weight_change_record = {
            'timestamp': signal_state.current_time,
            'old_weights': old_weights,
            'new_weights': signal_state.weights,
            'decoded_weights': decoded_weights
        }
        self.weight_history.append(weight_change_record)

        # Update weight stats
        self.weight_stats['weight_changes'] += 1

        # Notify compliance checker
        if hasattr(self.compliance, 'track_weight_change'):
            self.compliance.track_weight_change(decoded_weights, signal_state.current_time)

        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Weight change: 0x{old_weights:x} -> 0x{signal_state.weights:x} "
                        f"(decoded: {decoded_weights}) @ {signal_state.current_time}ns")

    def _decode_weights(self, packed_weights):
        """NEW: Decode packed weight signal into individual client weights"""
        # Assume 4 bits per weight (MAX_LEVELS_WIDTH = 4)
        max_levels_width = 4
        weights = []

        for i in range(self.clients):
            weight = (packed_weights >> (i * max_levels_width)) & ((1 << max_levels_width) - 1)
            weights.append(weight)

        return weights

    def _create_grant_transaction(self, signal_state, transaction_type="standard"):
        """
        Create transaction with type information for cycle-level reporting
        Extended to include weight information for weighted arbiters
        """
        # Calculate wait time
        request_time = self.pending_requests.get(signal_state.gnt_id, signal_state.current_time)
        wait_time = signal_state.current_time - request_time
        cycle_count = int(wait_time / self.clock_period_ns) if self.clock_period_ns > 0 else 0

        # Create transaction metadata
        metadata = {
            'blocked': self.blocked,
            'ack_mode': self.ack_mode,
            'is_weighted': self.is_weighted,
            'block_transition_time': self.last_block_transition_time,
            'block_history_size': len(self.block_arb_history),
            'transaction_type': transaction_type,
            'reporting_mode': 'cycle_level'
        }

        # NEW: Add weight information for weighted arbiters
        if self.is_weighted:
            decoded_weights = self._decode_weights(signal_state.weights)
            metadata.update({
                'max_thresh': signal_state.weights,
                'current_weights': decoded_weights,
                'weight_changes_count': self.weight_stats['weight_changes']
            })

        # Create transaction with weight information
        weights = self._decode_weights(signal_state.weights) if self.is_weighted else None

        transaction = ArbiterTransaction(
            req_vector=signal_state.req_vector,
            last_req_vector=signal_state.prev_req_vector,
            gnt_vector=signal_state.gnt_vector,
            gnt_id=signal_state.gnt_id,
            cycle_count=cycle_count,
            timestamp=signal_state.current_time,
            weights=weights,  # NEW: Include decoded weights
            metadata=metadata
        )

        # Update tracking
        self.transactions.append(transaction)
        self.total_transactions += 1

        # Clean up pending request for cycle-level reporting
        if transaction_type == "new_grant" or (not self.ack_mode):
            if signal_state.gnt_id in self.pending_requests:
                del self.pending_requests[signal_state.gnt_id]

        # Update statistics
        self._update_grant_statistics(signal_state, wait_time, cycle_count)

        # NEW: Update weight-specific statistics
        if self.is_weighted:
            self._update_weight_statistics(signal_state)

        # Queue for compliance checking
        if transaction_type in ["new_grant", "cycle_grant"]:
            recent_block_history = list(self.block_arb_history)[-10:]
            self.compliance.queue_transaction(
                transaction,
                blocked_state=self.blocked,
                active_requests=signal_state.prev_req_vector,
                block_arb_history=recent_block_history
            )

        # Use cocotb BusMonitor's _recv() method
        self._recv(transaction)

        if self.debug_enabled:
            weight_info = f", weights={weights}" if self.is_weighted else ""
            self.log.debug(f"ArbiterMonitor({self.title}): COMPLETED {transaction_type} processing for client {signal_state.gnt_id}{weight_info}")

    def _update_grant_statistics(self, signal_state, wait_time, cycle_count):
        """
        Update monitor statistics
        """
        self.arbiter_stats['total_grants'] += 1
        self.arbiter_stats['grants_per_client'][signal_state.gnt_id] += 1
        self.arbiter_stats['wait_time_per_client'][signal_state.gnt_id] += wait_time
        self.arbiter_stats['total_cycles'] += cycle_count
        self.arbiter_stats['grant_sequences'].append(signal_state.gnt_id)

        # Keep only recent sequences
        if len(self.arbiter_stats['grant_sequences']) > 100:
            self.arbiter_stats['grant_sequences'] = self.arbiter_stats['grant_sequences'][-50:]

        if self.arbiter_stats['total_grants'] > 0:
            self.arbiter_stats['avg_wait_time'] = self.arbiter_stats['total_cycles'] / self.arbiter_stats['total_grants']

        # Update grant history for compatibility
        self.grant_history.append(signal_state.gnt_id)
        if len(self.grant_history) > 100:
            self.grant_history = self.grant_history[-50:]

    def _update_weight_statistics(self, signal_state):
        """NEW: Update weight-specific statistics"""
        if not self.is_weighted:
            return

        # Update static period stats if active
        if self.weight_stats['static_period_active']:
            self.weight_stats['static_period_stats']['grants_per_client'][signal_state.gnt_id] += 1

        # Update weight distribution windows
        decoded_weights = self._decode_weights(signal_state.weights)

        for window_size in [100, 500, 2000]:  # Standard observation windows
            if window_size not in self.weight_stats['weight_distribution_windows']:
                self.weight_stats['weight_distribution_windows'][window_size] = {
                    'grants': [0] * self.clients,
                    'weights': deque(maxlen=window_size // 10),  # Store weight samples
                    'timestamps': deque(maxlen=window_size)
                }

            window_data = self.weight_stats['weight_distribution_windows'][window_size]
            window_data['grants'][signal_state.gnt_id] += 1
            window_data['weights'].append(decoded_weights)
            window_data['timestamps'].append(signal_state.current_time)

    def _update_previous_state(self, signal_state):
        """
        Update previous state for next cycle change detection
        """
        self._prev_state.update({
            'req_vector': signal_state.req_vector,
            'gnt_valid': signal_state.gnt_valid,
            'gnt_vector': signal_state.gnt_vector,
            'gnt_id': signal_state.gnt_id,
            'ack_vector': signal_state.ack_vector,
            'block_arb': signal_state.block_arb,
            'weights': signal_state.weights
        })

    def _log_periodic_status(self, signal_state, sample_count):
        """
        Log periodic status - includes weight information for weighted arbiters
        """
        weight_info = f", weights=0x{signal_state.weights:x}" if self.is_weighted else ""
        self.log.debug(f"ArbiterMonitor({self.title}): SAMPLE#{sample_count} @ {signal_state.current_time}ns: "
                    f"req=0x{signal_state.req_vector:x}, gnt_valid={signal_state.gnt_valid}, "
                    f"gnt=0x{signal_state.gnt_vector:x}, gnt_id={signal_state.gnt_id}, "
                    f"blocked={signal_state.block_arb}{weight_info}")

    # =============================================================================
    # WEIGHT MONITORING COROUTINE (NEW)
    # =============================================================================

    async def _weight_monitor(self):
        """NEW: Background weight monitoring for weighted arbiters"""
        if not self.is_weighted:
            return

        self.log.info(f"ArbiterMonitor({self.title}): Starting weight monitoring")

        while self.monitoring_enabled:
            await RisingEdge(self.clock)

            # Periodic weight compliance analysis
            if self.weight_stats['static_period_active']:
                # Check compliance every 100 cycles during static periods
                if (get_sim_time('ns') - self.weight_stats['static_period_start']) % (100 * self.clock_period_ns) < self.clock_period_ns:
                    self._analyze_current_weight_compliance_internal()

    def _analyze_current_weight_compliance_internal(self):
        """NEW: Internal method for periodic weight compliance checking"""
        if not self.weight_stats['static_period_active']:
            return

        try:
            current_stats = self.weight_stats['static_period_stats']
            expected_weights = current_stats['expected_weights']
            actual_grants = current_stats['grants_per_client']

            total_grants = sum(actual_grants)
            if total_grants < 10:  # Need minimum data
                return

            # Simple compliance check
            compliance_result = self.compliance.analyze_weight_compliance(expected_weights)
            if compliance_result.get('status') == 'analyzed':
                compliance_score = compliance_result.get('overall_compliance', 0)

                # Store compliance history
                self.weight_stats['weight_compliance_history'].append({
                    'timestamp': get_sim_time('ns'),
                    'compliance_score': compliance_score,
                    'total_grants': total_grants
                })

                if self.debug_enabled and compliance_score < 0.7:
                    self.log.debug(f"ArbiterMonitor({self.title}): Weight compliance below threshold: {compliance_score:.3f}")

        except Exception as e:
            if self.debug_enabled:
                self.log.debug(f"ArbiterMonitor({self.title}): Error in weight compliance analysis: {e}")

    # =============================================================================
    # RESET AND FENCE MONITORING - Same as before
    # =============================================================================

    async def _monitor_fence_conditions(self):
        """Monitor for fence conditions AND detect RTL reset conditions"""
        if not self.monitoring_enabled:
            return

        consecutive_idle_cycles = 0
        reset_flag_set = False

        self.log.info(f"ArbiterMonitor({self.title}): Starting fence monitoring with RTL reset detection")

        while True:
            await FallingEdge(self.clock)

            try:
                # Sample signals at falling edge for stability
                all_requests_low = True
                grant_valid_low = True

                if hasattr(self.bus, 'request') and self.bus.request.value.is_resolvable:
                    request_value = int(self.bus.request.value)
                    all_requests_low = (request_value == 0)

                if hasattr(self.bus, 'grant_valid') and self.bus.grant_valid.value.is_resolvable:
                    grant_valid_value = int(self.bus.grant_valid.value)
                    grant_valid_low = (grant_valid_value == 0)

                # RTL Reset Detection Logic
                if all_requests_low:
                    consecutive_idle_cycles += 1

                    if consecutive_idle_cycles >= self.reset_cycles and not reset_flag_set:
                        self.compliance.set_reset_flag()
                        reset_flag_set = True

                        if self.debug_enabled:
                            current_time = get_sim_time('ns')
                            self.log.debug(f"ArbiterMonitor({self.title}): RTL reset condition detected after {consecutive_idle_cycles} idle cycles @ {current_time}ns")

                else:
                    consecutive_idle_cycles = 0
                    reset_flag_set = False

                # Fence Condition Logic
                if all_requests_low and grant_valid_low and len(self.compliance.transaction_queue) > 0:
                    current_time = get_sim_time('ns')

                    if self.debug_enabled:
                        self.log.info(f"ArbiterMonitor({self.title}): Fence condition detected - running compliance analysis @ {current_time}ns")

                    analysis_results = self.compliance.run_compliance_analysis()

                    if self.debug_enabled and analysis_results.get('warnings_found', 0) > 0:
                        self.log.debug(f"ArbiterMonitor({self.title}): Fence analysis found {analysis_results['warnings_found']} warnings")

            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"ArbiterMonitor({self.title}): Error in fence monitoring: {e}{self.get_time_ns_str()}")

    async def _monitor_reset(self):
        """Monitor reset signal and handle reset events"""
        while True:
            await FallingEdge(self._reset_n)

            # Reset detected
            current_time = get_sim_time('ns')
            self.log.info(f"ArbiterMonitor({self.title}): Reset detected @ {current_time}ns")

            # Reset compliance checker
            self.compliance.reset_analysis()

            # Clear local state
            self.pending_requests.clear()
            self.active_request_vector = 0
            self.blocked = False
            self.current_weights = 0
            self.grant_history.clear()

            # Clear block_arb history
            self.block_arb_history.clear()
            self.current_block_state = False
            self.last_block_transition_time = 0

            # Reset tracking state
            self._prev_state = {
                'req_vector': 0,
                'gnt_valid': False,
                'gnt_vector': 0,
                'gnt_id': 0,
                'ack_vector': 0,
                'block_arb': False,
                'weights': 0
            }
            self._last_grant_info = {'gnt_vec': 0, 'gnt_id': 0, 'gnt_valid': False}

            # Reset ACK mode state
            if self.ack_mode:
                for i in range(self.clients):
                    self._ack_mode_state[i] = {
                        'grant_active': False,
                        'grant_start_time': 0,
                        'waiting_for_ack': False,
                        'last_grant_reported': 0
                    }

            # NEW: Reset weight-specific state
            if self.is_weighted:
                self.weight_history.clear()
                self.weight_stats['weight_changes'] = 0
                self.weight_stats['static_period_active'] = False
                for window_size in self.weight_stats['weight_distribution_windows']:
                    window_data = self.weight_stats['weight_distribution_windows'][window_size]
                    window_data['grants'] = [0] * self.clients
                    window_data['weights'].clear()
                    window_data['timestamps'].clear()

            # Call reset callback if registered
            if hasattr(self, 'reset_callback') and self.reset_callback:
                try:
                    self.reset_callback("hardware_reset")
                except Exception as e:
                    self.log.error(f"ArbiterMonitor({self.title}): Error in reset callback: {e}{self.get_time_ns_str()}")

            # Wait for reset to deassert
            await RisingEdge(self._reset_n)
            release_time = get_sim_time('ns')
            self.log.info(f"ArbiterMonitor({self.title}): Reset released @ {release_time}ns")

    # =============================================================================
    # CYCLE-LEVEL GRANT COUNTING AND ANALYSIS
    # =============================================================================

    def get_cycle_level_grant_count(self, client_id=None):
        """Get count of cycle-level grants (useful for tests)"""
        if client_id is None:
            return len([t for t in self.transactions
                    if t.metadata.get('reporting_mode') == 'cycle_level'])
        else:
            return len([t for t in self.transactions
                    if (t.gnt_id == client_id and
                        t.metadata.get('reporting_mode') == 'cycle_level')])

    def get_grant_type_summary(self):
        """Get summary of different grant types reported"""
        type_counts = {}
        for transaction in self.transactions:
            trans_type = transaction.metadata.get('transaction_type', 'unknown')
            type_counts[trans_type] = type_counts.get(trans_type, 0) + 1

        return type_counts

    def get_detailed_grant_stats(self, client_id=None):
        """Get detailed grant statistics including cycle-level information"""
        if client_id is not None:
            client_transactions = [t for t in self.transactions if t.gnt_id == client_id]

            stats = {
                'client_id': client_id,
                'total_grants': len(client_transactions),
                'cycle_level_grants': len([t for t in client_transactions
                                        if t.metadata.get('reporting_mode') == 'cycle_level']),
                'grant_types': {}
            }

            for transaction in client_transactions:
                trans_type = transaction.metadata.get('transaction_type', 'unknown')
                stats['grant_types'][trans_type] = stats['grant_types'].get(trans_type, 0) + 1

            return stats
        else:
            all_stats = {
                'total_transactions': len(self.transactions),
                'cycle_level_transactions': len([t for t in self.transactions
                                            if t.metadata.get('reporting_mode') == 'cycle_level']),
                'grant_type_summary': self.get_grant_type_summary(),
                'per_client': {}
            }

            for i in range(self.clients):
                all_stats['per_client'][i] = self.get_detailed_grant_stats(i)

            return all_stats

    # =============================================================================
    # COMPATIBILITY AND ANALYSIS METHODS - Extended for weight support
    # =============================================================================

    def force_compliance_analysis(self, reason="manual"):
        """Force immediate compliance analysis on queued transactions"""
        return self.compliance.force_fence(reason)

    def get_queue_status(self):
        """Get compliance queue status with block_arb and weight info"""
        base_status = self.compliance.get_queue_status()
        base_status.update({
            'monitor_block_history_size': len(self.block_arb_history),
            'current_block_state': self.current_block_state,
            'last_block_transition_time': self.last_block_transition_time,
            'cycle_level_reporting': self.cycle_level_reporting,
            'is_weighted': self.is_weighted
        })

        # NEW: Add weight-specific status
        if self.is_weighted:
            base_status.update({
                'weight_changes_tracked': len(self.weight_history),
                'static_weight_period_active': self.weight_stats['static_period_active'],
                'weight_compliance_windows': list(self.weight_stats['weight_distribution_windows'].keys())
            })

        return base_status

    def set_static_period(self, is_static, expected_weights=None):
        """Set whether we're in a static test period for weight compliance checking"""
        if is_static:
            if self.is_weighted:
                self.start_static_weight_period(expected_weights)
            else:
                self.compliance.start_static_period()
        else:
            if self.is_weighted:
                self.end_static_weight_period()
            else:
                self.compliance.end_static_period()

        if self.debug_enabled:
            period_type = "static weight" if self.is_weighted else "static"
            self.log.debug(f"ArbiterMonitor({self.title}): {period_type} period {'started' if is_static else 'ended'}{self.get_time_ns_str()}")

    def get_compliance_warnings(self):
        """Get protocol compliance warnings from compliance checker"""
        return self.compliance.get_warning_summary()

    def get_protocol_warnings(self):
        """Get detailed protocol warnings (for compatibility)"""
        return self.compliance.protocol_warnings

    def print_compliance_report(self):
        """Print comprehensive compliance report"""
        self.compliance.print_compliance_report()

    def analyze_static_weight_compliance(self, expected_weights, requesting_clients=None):
        """Analyze weight compliance using compliance checker"""
        if self.is_weighted:
            return self.compliance.analyze_weight_compliance(expected_weights, requesting_clients)
        else:
            return {'status': 'not_weighted'}

    def get_fairness_index(self):
        """Calculate Jain's fairness index using compliance checker"""
        return self.compliance.analyze_fairness()

    def check_starvation(self, recent_window=50):
        """Check for client starvation using compliance checker"""
        return self.compliance.check_starvation(recent_window)

    def detect_burst_behavior(self, max_consecutive=3):
        """Detect burst behavior using compliance checker"""
        return self.compliance.detect_burst_behavior(max_consecutive)

    def get_client_stats(self, client_id):
        """Get statistics for a specific client."""
        if client_id >= self.clients:
            self.log.error(f"ArbiterMonitor({self.title}): Invalid client ID: {client_id}, max is {self.clients-1}{self.get_time_ns_str()}")
            return None

        grants = self.arbiter_stats['grants_per_client'][client_id]
        return {
            'grants': grants,
            'avg_wait_time': (self.arbiter_stats['wait_time_per_client'][client_id] / grants) if grants > 0 else 0
        }

    def get_stats_summary(self):
        """Get a comprehensive statistics summary"""
        total_grants = self.arbiter_stats['total_grants']

        summary = {
            'total_transactions': self.total_transactions,
            'total_grants': total_grants,
            'avg_wait_time': self.arbiter_stats['avg_wait_time'],
            'fairness_index': self.get_fairness_index(),
            'is_weighted': self.is_weighted,
            'client_stats': []
        }

        for i in range(self.clients):
            client_grants = self.arbiter_stats['grants_per_client'][i]
            percentage = (client_grants / total_grants * 100) if total_grants > 0 else 0

            summary['client_stats'].append({
                'client_id': i,
                'grants': client_grants,
                'percentage': percentage,
                'avg_wait_time': (self.arbiter_stats['wait_time_per_client'][i] / client_grants) if client_grants > 0 else 0
            })

        return summary

    def get_comprehensive_stats(self):
        """Get comprehensive statistics including compliance analysis and weight info"""
        # Get basic stats from arbiter_stats
        base_stats = self.get_stats_summary()

        # Get comprehensive analysis from compliance checker
        compliance_analysis = self.compliance.get_comprehensive_analysis()

        # Combine for backward compatibility
        comprehensive_stats = {
            **base_stats,
            'compliance_analysis': compliance_analysis,
            'burst_analysis': compliance_analysis['fairness_analysis']['burst_analysis'],
            'starvation_analysis': compliance_analysis['fairness_analysis']['starvation_check'],
            'protocol_warnings': self.get_compliance_warnings(),
            'monitoring_metadata': {
                'cycles_monitored': compliance_analysis['basic_stats']['cycles_monitored'],
                'debug_enabled': self.debug_enabled,
                'clients': self.clients,
                'ack_mode': self.ack_mode,
                'is_weighted': self.is_weighted,
                'falling_edge_sampling': True,
                'block_history_tracking': True,
                'block_history_size': len(self.block_arb_history),
                'pipeline_delay_cycles': self.compliance.pipeline_delay_cycles,
                'cycle_level_reporting': self.cycle_level_reporting,
                'unified_version': True
            }
        }

        # NEW: Add weight-specific statistics
        if self.is_weighted:
            comprehensive_stats['weight_analysis'] = {
                'weight_changes_tracked': len(self.weight_history),
                'static_period_active': self.weight_stats['static_period_active'],
                'weight_distribution_windows': {
                    size: {
                        'grants': data['grants'].copy(),
                        'sample_count': len(data['timestamps'])
                    }
                    for size, data in self.weight_stats['weight_distribution_windows'].items()
                },
                'compliance_history_size': len(self.weight_stats['weight_compliance_history'])
            }

            # Add current weight compliance if in static period
            if self.weight_stats['static_period_active']:
                expected_weights = self.weight_stats['static_period_stats']['expected_weights']
                compliance_result = self.analyze_static_weight_compliance(expected_weights)
                comprehensive_stats['current_weight_compliance'] = compliance_result

        return comprehensive_stats

    def get_transaction_count(self):
        """Return the total number of observed transactions (cocotb compatibility)"""
        return self.total_transactions

    def get_observed_packets(self, count=None):
        """Get observed packets from cocotb _recvQ (cocotb compatibility)"""
        if count is None:
            return list(self._recvQ)
        return list(self._recvQ)[-count:]

    def print_comprehensive_stats(self):
        """Print comprehensive statistics in human-readable format to the monitor's log"""
        lines = []
        lines.append("=" * 80)
        monitor_type = "WEIGHTED" if self.is_weighted else "STANDARD"
        lines.append(f"COMPREHENSIVE {monitor_type} ARBITER STATISTICS REPORT")
        lines.append("=" * 80)
        lines.append(f"Report Generated: {self.get_time_ns_str()}")
        lines.append(f"Monitor Type: {monitor_type} Arbiter Monitor")
        lines.append(f"Sampling Method: FallingEdge(clock) - signals stable when captured")
        lines.append(f"Block History Tracking: ENABLED - {len(self.block_arb_history)} entries")
        lines.append(f"Pipeline Delay Cycles: {self.compliance.pipeline_delay_cycles}")
        lines.append(f"Cycle-Level Reporting: {'ENABLED' if self.cycle_level_reporting else 'DISABLED'}")
        lines.append("")

        stats = self.get_comprehensive_stats()

        # Basic Statistics
        lines.append("BASIC STATISTICS:")
        lines.append("-" * 40)
        lines.append(f"  Total Transactions:     {stats['total_transactions']:,}")
        lines.append(f"  Total Grants:          {stats['total_grants']:,}")
        lines.append(f"  Average Wait Time:     {stats['avg_wait_time']:.2f} ns")
        lines.append(f"  Fairness Index:        {stats['fairness_index']:.3f}")
        lines.append(f"  ACK Mode:              {stats['monitoring_metadata']['ack_mode']}")
        lines.append(f"  Weighted Mode:         {stats['monitoring_metadata']['is_weighted']}")
        lines.append(f"  Cycle-Level Reporting: {stats['monitoring_metadata']['cycle_level_reporting']}")
        lines.append("")

        # Cycle-Level Grant Statistics
        lines.append("CYCLE-LEVEL GRANT STATISTICS:")
        lines.append("-" * 40)
        grant_type_summary = self.get_grant_type_summary()
        for grant_type, count in grant_type_summary.items():
            lines.append(f"  {grant_type.replace('_', ' ').title()}: {count:,}")
        lines.append("")

        # NEW: Weight-specific statistics
        if self.is_weighted and 'weight_analysis' in stats:
            weight_analysis = stats['weight_analysis']
            lines.append("WEIGHT ANALYSIS:")
            lines.append("-" * 40)
            lines.append(f"  Weight Changes Tracked: {weight_analysis['weight_changes_tracked']}")
            lines.append(f"  Static Period Active:   {weight_analysis['static_period_active']}")
            lines.append(f"  Compliance History:     {weight_analysis['compliance_history_size']} entries")

            # Weight distribution windows
            for window_size, window_data in weight_analysis['weight_distribution_windows'].items():
                lines.append(f"  Window {window_size}: {window_data['sample_count']} samples")

            # Current compliance if available
            if 'current_weight_compliance' in stats:
                compliance = stats['current_weight_compliance']
                if compliance.get('status') == 'analyzed':
                    lines.append(f"  Current Compliance:     {compliance['overall_compliance']:.3f}")
                    lines.append(f"  Weight Efficiency:      {compliance.get('weight_efficiency', 0):.3f}")
            lines.append("")

        # Monitoring Statistics
        lines.append("MONITORING STATISTICS:")
        lines.append("-" * 40)
        lines.append(f"  Block History Entries:  {stats['monitoring_metadata']['block_history_size']}")
        lines.append(f"  Pipeline Delay Cycles:  {stats['monitoring_metadata']['pipeline_delay_cycles']}")
        lines.append(f"  Current Block State:    {self.current_block_state}")
        lines.append(f"  Last Block Transition:  {self.last_block_transition_time:.1f}ns")
        lines.append("")

        # Per-Client Statistics
        lines.append("PER-CLIENT STATISTICS:")
        lines.append("-" * 40)
        lines.append(f"{'Client':<8} {'Grants':<10} {'Percentage':<12} {'Avg Wait (ns)':<15}")
        lines.append("-" * 50)
        for client_stats in stats['client_stats']:
            lines.append(f"{client_stats['client_id']:<8} "
                        f"{client_stats['grants']:<10} "
                        f"{client_stats['percentage']:<11.1f}% "
                        f"{client_stats['avg_wait_time']:<15.2f}")
        lines.append("")
        lines.append("=" * 80)

        # Print all lines to the monitor's log
        for line in lines:
            self.log.info(line)


class RoundRobinArbiterMonitor(ArbiterMonitor):
    """Monitor specifically tailored for Round Robin Arbiters using unified architecture."""

    def __init__(self, dut, title, clock, reset_n,
                req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                gnt_ack_signal=None, block_arb_signal=None, clients=None,
                ack_mode=False, log=None, clock_period_ns=10, **kwargs):
        """Initialize a Round Robin Arbiter Monitor"""

        # Map individual signals to a bus-like interface for cocotb BusMonitor
        self._signal_map = {
            'request': req_signal,
            'grant_valid': gnt_valid_signal,
            'grant': gnt_signal,
            'grant_id': gnt_id_signal,
            'grant_ack': gnt_ack_signal,
            'block_arb': block_arb_signal
        }

        super().__init__(
            entity=dut,
            name=title,
            clock=clock,
            reset_n=reset_n,
            clients=clients,
            is_weighted=False,  # Round-robin is not weighted
            ack_mode=ack_mode,
            log=log,
            clock_period_ns=clock_period_ns,
            **kwargs
        )

        # Override bus signal resolution to use individual signals
        self._override_bus_signals()

    def _override_bus_signals(self):
        """Override bus signal resolution to use the provided individual signals"""
        for signal_name, signal_ref in self._signal_map.items():
            if signal_ref is not None:
                setattr(self.bus, signal_name, signal_ref)

    def analyze_round_robin_pattern(self):
        """Analyze if the grant pattern follows round-robin behavior"""
        return self.compliance.analyze_round_robin_compliance()


class WeightedRoundRobinArbiterMonitor(ArbiterMonitor):
    """Monitor specifically tailored for Weighted Round Robin Arbiters using unified architecture."""

    def __init__(self, dut, title, clock, reset_n,
                req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                gnt_ack_signal=None, block_arb_signal=None,
                max_thresh_signal=None, clients=None, ack_mode=False,
                log=None, clock_period_ns=10, **kwargs):
        """Initialize a Weighted Round Robin Arbiter Monitor"""

        # Map individual signals to a bus-like interface for cocotb BusMonitor
        self._signal_map = {
            'request': req_signal,
            'grant_valid': gnt_valid_signal,
            'grant': gnt_signal,
            'grant_id': gnt_id_signal,
            'grant_ack': gnt_ack_signal,
            'block_arb': block_arb_signal,
            'max_thresh': max_thresh_signal  # NEW: Weight signal
        }

        super().__init__(
            entity=dut,
            name=title,
            clock=clock,
            reset_n=reset_n,
            clients=clients,
            is_weighted=True,  # Weighted round-robin
            ack_mode=ack_mode,
            log=log,
            clock_period_ns=clock_period_ns,
            **kwargs
        )

        # Override bus signal resolution to use individual signals
        self._override_bus_signals()

    def _override_bus_signals(self):
        """Override bus signal resolution to use the provided individual signals"""
        for signal_name, signal_ref in self._signal_map.items():
            if signal_ref is not None:
                setattr(self.bus, signal_name, signal_ref)

    def analyze_weight_compliance(self, expected_weights=None):
        """Analyze if grant distribution matches expected weights"""
        return self.compliance.analyze_weight_compliance(expected_weights)

    def get_current_weight_distribution(self, window_size=500):
        """Get current weight distribution analysis"""
        return self.analyze_current_weight_compliance(window_size)
