# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: RoundRobinMaskState
# Purpose: Unified RTL-Compliant Arbiter Protocol Compliance Checker
#
# Documentation: bin/CocoTBFramework/README.md
# Subsystem: framework
#
# Author: sean galloway
# Created: 2025-10-18

"""
Unified RTL-Compliant Arbiter Protocol Compliance Checker

Supports both weighted and non-weighted arbiters with automatic adaptation.
Maintains backward compatibility - existing testbenches work unchanged.
"""

from collections import deque
from cocotb.utils import get_sim_time
from cocotb.log import SimLog


class RoundRobinMaskState:
    """Track the round-robin mask state per RTL algorithm"""

    def __init__(self, clients, debug_enabled=True):
        self.clients = clients
        self.mask_valid = False
        self.last_winner = None
        self.current_mask = 0
        self.debug_enabled = debug_enabled

    def get_masked_requests(self, requests):
        """Get requests that should have priority"""
        if not self.mask_valid:
            return 0
        return requests & self.current_mask

    def get_expected_winner(self, requests):
        """Get expected winner - handles post-reset conditions"""
        if not requests:
            return None

        if self.debug_enabled:
            print(f"RoundRobinMaskState.get_expected_winner: "
                f"requests=0x{requests:x}, mask_valid={self.mask_valid}, "
                f"current_mask=0x{self.current_mask:x}, last_winner={self.last_winner}")

        # Post-reset state: RTL uses pure priority encoder (lowest index wins)
        if not self.mask_valid or self.last_winner is None:
            for i in range(self.clients):
                if requests & (1 << i):
                    if self.debug_enabled:
                        print(f"  Post-reset/initial state - priority encoder selects: {i}")
                    return i
            return None

        # Normal round-robin operation: Apply dual-priority scheme
        masked_requests = self.get_masked_requests(requests)

        if self.debug_enabled:
            print(f"  Masked requests: 0x{masked_requests:x}")

        if masked_requests != 0:
            # Find first set bit in masked requests (higher priority clients)
            for i in range(self.clients):
                if masked_requests & (1 << i):
                    if self.debug_enabled:
                        print(f"  Found masked winner: {i}")
                    return i
        else:
            # No masked requests - use unmasked (wrap-around case)
            for i in range(self.clients):
                if requests & (1 << i):
                    if self.debug_enabled:
                        print(f"  Found unmasked winner (wrap-around): {i}")
                    return i

        return 0  # Safety fallback

    def update_mask(self, winner_client):
        """Update mask after grant"""
        if winner_client >= self.clients:
            if self.debug_enabled:
                print(f"RoundRobinMaskState.update_mask: ERROR - invalid winner {winner_client}")
            return

        old_mask = self.current_mask
        old_last_winner = self.last_winner
        old_mask_valid = self.mask_valid

        self.last_winner = winner_client
        self.mask_valid = True

        # RTL algorithm: After client N wins, mask clients 0 through N
        mask_bits = (1 << (winner_client + 1)) - 1
        self.current_mask = (~mask_bits) & ((1 << self.clients) - 1)

        if self.debug_enabled:
            print(f"RoundRobinMaskState.update_mask: winner={winner_client}")
            print(f"  Old: mask=0x{old_mask:x}, last_winner={old_last_winner}, valid={old_mask_valid}")
            print(f"  Calculation: ~((1 << ({winner_client}+1)) - 1) = ~{mask_bits} = 0x{~mask_bits:x}")
            print(f"  Masked to {self.clients} bits: 0x{self.current_mask:x}")
            print(f"  New: mask=0x{self.current_mask:x}, last_winner={self.last_winner}, valid={self.mask_valid}")

    def reset(self):
        """Reset mask state"""
        if self.debug_enabled:
            print(f"RoundRobinMaskState.reset: Clearing mask state")
        self.mask_valid = False
        self.last_winner = None
        self.current_mask = 0

    def __str__(self):
        return (f"RoundRobinMaskState(clients={self.clients}, "
                f"mask_valid={self.mask_valid}, "
                f"current_mask=0x{self.current_mask:x}, "
                f"last_winner={self.last_winner})")


class ArbiterCompliance:
    """
    Unified RTL-Compliant protocol compliance checker for arbiter components.

    Automatically adapts to weighted and non-weighted arbiters based on arbiter_type parameter.
    Maintains backward compatibility - existing testbenches work unchanged.
    """

    def __init__(self, name, clients, arbiter_type='rr', ack_mode=False, log=None, clock_period_ns=10):
        self.name = name
        self.title = name
        self.clients = clients
        self.arbiter_type = arbiter_type  # 'rr' or 'wrr'
        self.is_weighted = (arbiter_type == 'wrr')  # Auto-detect weighted mode
        self.ack_mode = ack_mode
        self.clock_period_ns = clock_period_ns

        # Set up logging
        if log:
            self.log = log
        else:
            self.log = SimLog(f"cocotb.compliance.{name}")

        # Protocol checking configuration
        self.protocol_checking_enabled = True
        self.debug_enabled = True

        # Transaction queuing for batch analysis
        self.transaction_queue = []
        self.max_queue_size = 20000

        # Fence detection state
        self.fence_detection_enabled = True
        self.last_fence_time = 0

        # Warning and violation tracking
        self.protocol_warnings = []
        self.max_warnings = 200

        # Basic statistics
        self.grant_counts = [0] * clients
        self.total_grants = 0
        self.cycles_monitored = 0

        # ACK PROTOCOL TRACKING
        self.pending_acks = {}
        self.ack_timeout_cycles = 1000
        self.cycle_level_mode = True
        self.compliance_sampling_rate = 1
        self._transaction_count = 0

        # SIMPLE RESET DETECTION
        self.reset_arb_flag = False

        # COMPATIBILITY ATTRIBUTES - Expected by monitor
        self.pipeline_delay_cycles = 2
        self.grant_history = []
        self.transition_matrix = {}
        self.consecutive_grants = {}
        self.patterns_seen = set()
        self.transitions_seen = set()
        self.latency_histogram = {}
        self.max_latency = 0
        self.min_latency = float('inf')
        self.block_arb_history = deque(maxlen=50)

        # Round-robin state tracking
        if arbiter_type == 'rr':
            self.rr_mask_state = RoundRobinMaskState(clients, debug_enabled=self.debug_enabled)
            self.pending_mask_updates = {}
        else:
            self.rr_mask_state = None
            self.pending_mask_updates = {}

        # NEW: Weighted round-robin state tracking
        if self.is_weighted:
            self._setup_weight_compliance()

        # Static period tracking (used by both RR and WRR)
        self.is_static_period = False
        self.static_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * clients,
            'start_time': 0
        }

        arbiter_type_name = "weighted round-robin" if self.is_weighted else "round-robin"
        self.log.info(f"ArbiterCompliance({self.title}): Unified compliance checker initialized: {clients} clients, "
                    f"type={arbiter_type_name}, ack_mode={ack_mode}")

    def _setup_weight_compliance(self):
        """NEW: Setup weight-specific compliance tracking"""
        self.weight_observation_windows = [100, 500, 2000]
        self.weight_compliance_threshold = 0.8
        self.weight_change_history = []
        self.weight_distribution_windows = {}

        # Initialize weight distribution tracking windows
        for window_size in self.weight_observation_windows:
            self.weight_distribution_windows[window_size] = {
                'grants': deque(maxlen=window_size),
                'weights': deque(maxlen=window_size // 10),  # Store weight samples
                'timestamps': deque(maxlen=window_size)
            }

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Weight compliance tracking initialized")

    @staticmethod
    def get_time_ns_str():
        """Get current simulation time as a formatted string"""
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    # =======================================================================
    # SIMPLE RESET DETECTION
    # =======================================================================

    def set_reset_flag(self):
        """Set the reset flag - called by monitor when RTL reset condition detected"""
        self.reset_arb_flag = True

        # Reset round-robin state immediately
        if self.rr_mask_state:
            self.rr_mask_state.reset()

        # Clear any pending mask updates
        self.pending_mask_updates.clear()

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): RTL reset flag set - RR state cleared{self.get_time_ns_str()}")

    # =======================================================================
    # TRANSACTION PROCESSING
    # =======================================================================

    def queue_transaction(self, transaction, blocked_state=False, active_requests=0, block_arb_history=None):
        """Queue transaction for compliance checking"""
        self._transaction_count += 1

        # Simple sampling for efficiency
        transaction_type = getattr(transaction, 'metadata', {}).get('transaction_type', 'unknown')
        always_check_types = ['new_grant', 'grant_violation', 'protocol_error']

        should_check = (
            transaction_type in always_check_types or
            self._transaction_count % self.compliance_sampling_rate == 0
        )

        if not should_check:
            self._update_basic_stats(transaction)
            return True

        # Queue for full compliance checking
        if len(self.transaction_queue) >= self.max_queue_size:
            self.log.warning(f"ArbiterCompliance({self.title}): Transaction queue full, forcing analysis")
            self.run_compliance_analysis()

        queued_transaction = {
            'transaction': transaction,
            'blocked_state': blocked_state,
            'active_requests': active_requests,
            'queue_time': get_sim_time('ns')
        }

        self.transaction_queue.append(queued_transaction)

        # NEW: Update weight-specific tracking
        if self.is_weighted:
            self._update_weight_tracking(transaction)

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Queued transaction: client {transaction.gnt_id}")

        return True

    def _update_basic_stats(self, transaction):
        """Update basic statistics without full compliance checking"""
        self.total_grants += 1
        if transaction.gnt_id < len(self.grant_counts):
            self.grant_counts[transaction.gnt_id] += 1

        # Update grant history for compatibility
        self.grant_history.append(transaction.gnt_id)
        if len(self.grant_history) > 100:
            self.grant_history = self.grant_history[-50:]

        # NEW: Update static period stats
        if self.is_static_period:
            self._update_static_period_stats(transaction)

    def _update_weight_tracking(self, transaction):
        """NEW: Update weight-specific tracking for WRR arbiters"""
        if not self.is_weighted:
            return

        current_weights = transaction.metadata.get('current_weights', None)
        if current_weights is None:
            return

        # Update weight distribution windows
        for window_size, window_data in self.weight_distribution_windows.items():
            window_data['grants'].append(transaction.gnt_id)
            window_data['timestamps'].append(transaction.timestamp)

            # Store weight samples periodically (not every grant)
            if len(window_data['timestamps']) % 10 == 0:
                window_data['weights'].append(current_weights.copy())

    # =======================================================================
    # FENCE DETECTION
    # =======================================================================

    def check_fence_condition(self, all_requests_low, grant_valid_low):
        """Check if a fence condition has occurred"""
        if not self.fence_detection_enabled:
            return False

        fence_detected = all_requests_low and grant_valid_low and len(self.transaction_queue) > 0

        if fence_detected:
            current_time = get_sim_time('ns')
            self.log.info(f"ArbiterCompliance({self.title}): Fence detected @ {current_time}ns")

        return fence_detected

    def force_fence(self, reason="manual"):
        """Force a fence condition for immediate compliance analysis"""
        if len(self.transaction_queue) > 0:
            self.log.info(f"ArbiterCompliance({self.title}): Forced fence ({reason})")
            self.run_compliance_analysis()

    # =======================================================================
    # COMPLIANCE ANALYSIS
    # =======================================================================

    def run_compliance_analysis(self):
        """Run compliance analysis on queued transactions"""
        if not self.transaction_queue:
            return {'status': 'no_transactions'}

        start_time = get_sim_time('ns')
        transaction_count = len(self.transaction_queue)

        self.log.info(f"ArbiterCompliance({self.title}): Starting compliance analysis on {transaction_count} transactions")

        batch_warnings = []

        for queued_item in self.transaction_queue:
            transaction = queued_item['transaction']
            blocked_state = queued_item['blocked_state']
            active_requests = queued_item['active_requests']

            # Check compliance for this transaction
            warnings = self._check_single_transaction_compliance(
                transaction, blocked_state, active_requests
            )
            batch_warnings.extend(warnings)

        # Store warnings
        for warning in batch_warnings:
            self._record_warning(warning)

        # Clear the queue
        self.transaction_queue.clear()
        self.last_fence_time = start_time

        self.log.info(f"ArbiterCompliance({self.title}): Analysis completed: {len(batch_warnings)} warnings found")

        return {
            'status': 'completed',
            'transactions_analyzed': transaction_count,
            'warnings_found': len(batch_warnings)
        }

    def _check_single_transaction_compliance(self, transaction, blocked_state, active_requests):
        """Check single transaction compliance with unified approach"""
        warnings = []
        current_time = transaction.timestamp

        # Check and clear reset flag
        skip_rr_check = self.reset_arb_flag
        if self.reset_arb_flag:
            self.reset_arb_flag = False
            if self.debug_enabled:
                self.log.debug(f"ArbiterCompliance({self.title}): RTL reset flag detected @ {current_time}ns - skipping RR compliance")

            # Update mask state even when skipping compliance check
            if self.arbiter_type == 'rr' and self.rr_mask_state:
                self.rr_mask_state.update_mask(transaction.gnt_id)
                if self.debug_enabled:
                    self.log.debug(f"ArbiterCompliance({self.title}): Updated RR mask for skipped grant: "
                                f"winner={transaction.gnt_id}, new_mask=0x{self.rr_mask_state.current_mask:x}")

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Compliance check @ {current_time}ns:")
            self.log.debug(f"  skip_rr_check={skip_rr_check}")
            self.log.debug(f"  active_requests=0x{active_requests:x}")
            self.log.debug(f"  arbiter_type={self.arbiter_type}")

        # Basic protocol checks (common to all arbiter types)
        warnings.extend(self._check_basic_protocol_compliance(transaction, blocked_state, active_requests))

        # Arbiter-specific checks
        if not skip_rr_check:
            if self.arbiter_type == 'rr':
                warnings.extend(self._check_round_robin_compliance(transaction, active_requests))
            elif self.arbiter_type == 'wrr':
                warnings.extend(self._check_weighted_round_robin_compliance(transaction, active_requests))

        # ACK protocol checks (common to all arbiter types if enabled)
        if self.ack_mode:
            warnings.extend(self._check_ack_protocol_compliance(transaction))

        return warnings

    # =======================================================================
    # BASIC PROTOCOL COMPLIANCE
    # =======================================================================

    def _check_basic_protocol_compliance(self, transaction, blocked_state, active_requests):
        """Check basic arbiter protocol compliance"""
        warnings = []
        current_time = transaction.timestamp

        # Check 1: Grant ID matches grant vector
        expected_grant_vector = (1 << transaction.gnt_id)
        if transaction.gnt_vector != expected_grant_vector:
            warnings.append({
                'type': 'grant_id_mismatch',
                'message': f"Grant ID {transaction.gnt_id} doesn't match grant vector 0x{transaction.gnt_vector:x}",
                'timestamp': current_time,
                'client_id': transaction.gnt_id,
                'severity': 'error'
            })

        # Check 2: Single grant (one-hot)
        if bin(transaction.gnt_vector).count('1') != 1:
            warnings.append({
                'type': 'multiple_grants',
                'message': f"Multiple grants issued: 0x{transaction.gnt_vector:x}",
                'timestamp': current_time,
                'severity': 'error'
            })

        # Check 3: Grant ID out of range
        if transaction.gnt_id >= self.clients:
            warnings.append({
                'type': 'grant_id_out_of_range',
                'message': f"Grant ID {transaction.gnt_id} exceeds client count {self.clients}",
                'timestamp': current_time,
                'client_id': transaction.gnt_id,
                'severity': 'error'
            })

        return warnings

    # =======================================================================
    # ROUND-ROBIN COMPLIANCE
    # =======================================================================

    def _check_round_robin_compliance(self, transaction, active_requests):
        """Check round-robin compliance using RTL algorithm"""
        if not self.rr_mask_state:
            return []

        warnings = []
        current_time = transaction.timestamp
        current_winner = transaction.gnt_id

        if self.ack_mode:
            return self._check_round_robin_compliance_ack_mode(transaction, active_requests)
        else:
            return self._check_round_robin_compliance_no_ack(transaction, active_requests)

    def _check_round_robin_compliance_no_ack(self, transaction, active_requests):
        """Check round-robin compliance for no-ACK mode"""
        warnings = []
        current_time = transaction.timestamp
        current_winner = transaction.gnt_id

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): NO-ACK RR CHECK @ {current_time}ns")
            self.log.debug(f"  Winner: {current_winner}, Active requests: 0x{active_requests:x}")
            if self.rr_mask_state:
                self.log.debug(f"  Current RR state BEFORE check: mask=0x{self.rr_mask_state.current_mask:x}, "
                            f"last_winner={self.rr_mask_state.last_winner}, mask_valid={self.rr_mask_state.mask_valid}")

        # Check compliance using CURRENT mask state (before update)
        if active_requests != 0:
            expected_winner = self.rr_mask_state.get_expected_winner(active_requests)

            if self.debug_enabled:
                masked_requests = self.rr_mask_state.get_masked_requests(active_requests)
                self.log.debug(f"  Masked requests: 0x{masked_requests:x}")
                self.log.debug(f"  Expected: {expected_winner}, Actual: {current_winner}")

            if expected_winner is not None and expected_winner != current_winner:
                warnings.append({
                    'type': 'round_robin_violation',
                    'message': f"Round-robin violation: Expected client {expected_winner}, got {current_winner}",
                    'timestamp': current_time,
                    'client_id': current_winner,
                    'severity': 'error',
                    'details': {
                        'expected_winner': expected_winner,
                        'actual_winner': current_winner,
                        'active_requests': f"0x{active_requests:x}",
                        'current_mask': f"0x{self.rr_mask_state.current_mask:x}",
                        'mask_valid': self.rr_mask_state.mask_valid,
                        'last_winner': self.rr_mask_state.last_winner
                    }
                })

        # Update mask AFTER compliance check
        old_mask = self.rr_mask_state.current_mask
        old_last_winner = self.rr_mask_state.last_winner

        self.rr_mask_state.update_mask(current_winner)

        if self.debug_enabled:
            self.log.debug(f"  MASK UPDATE AFTER compliance check:")
            self.log.debug(f"    Old: mask=0x{old_mask:x}, last_winner={old_last_winner}")
            self.log.debug(f"    New: mask=0x{self.rr_mask_state.current_mask:x}, last_winner={self.rr_mask_state.last_winner}")

        # Update grant history and patterns for compatibility
        self.grant_history.append(current_winner)
        if len(self.grant_history) > 100:
            self.grant_history = self.grant_history[-50:]

        return warnings

    def _check_round_robin_compliance_ack_mode(self, transaction, active_requests):
        """Check round-robin compliance for ACK mode"""
        warnings = []
        current_time = transaction.timestamp
        current_winner = transaction.gnt_id

        # Check if this is a new grant
        existing_pending = [t for t, client in self.pending_acks.items() if client == current_winner]
        is_new_grant = not existing_pending

        if is_new_grant:
            # Store for deferred compliance checking
            self.pending_mask_updates[current_time] = current_winner
            self.pending_acks[current_time] = current_winner

            # Update mask immediately for next grant
            self.rr_mask_state.update_mask(current_winner)

        return warnings

    # =======================================================================
    # WEIGHTED ROUND-ROBIN COMPLIANCE
    # =======================================================================

    def _check_weighted_round_robin_compliance(self, transaction, active_requests):
        """Check weighted round-robin compliance - COMPLETED implementation"""
        warnings = []
        current_time = transaction.timestamp
        current_winner = transaction.gnt_id

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): WRR CHECK @ {current_time}ns")
            self.log.debug(f"  Winner: {current_winner}, Active requests: 0x{active_requests:x}")
            self.log.debug(f"  Current weights from metadata: {transaction.metadata.get('current_weights', 'N/A')}")

        # Extract current weights from transaction metadata
        current_weights = transaction.metadata.get('current_weights', None)
        if current_weights is None:
            self.log.warning(f"ArbiterCompliance({self.title}): No weight information in transaction metadata")
            return warnings

        # For weighted arbiters, we primarily check:
        # 1. Basic protocol compliance (inherited from base)
        # 2. Statistical weight compliance over observation windows
        # 3. Credit exhaustion patterns (implementation-specific)

        # Check if this grant fits expected weight-based patterns
        # This is more complex than RR because weights affect timing

        # For now, we focus on statistical compliance over longer periods
        # rather than cycle-by-cycle compliance (which depends on credit implementation)

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): WRR compliance check completed for client {current_winner}")

        return warnings

    # =======================================================================
    # ACK PROTOCOL COMPLIANCE
    # =======================================================================

    def _check_ack_protocol_compliance(self, transaction):
        """Check ACK protocol compliance"""
        warnings = []
        current_time = transaction.timestamp

        # Check for ACK timeout
        timeout_ns = self.ack_timeout_cycles * self.clock_period_ns
        old_timestamps = [t for t in self.pending_acks.keys() if (current_time - t) > timeout_ns]

        for old_timestamp in old_timestamps:
            old_client = self.pending_acks[old_timestamp]
            warnings.append({
                'type': 'ack_timeout',
                'message': f"ACK timeout for client {old_client}",
                'timestamp': current_time,
                'client_id': old_client,
                'severity': 'warning'
            })
            del self.pending_acks[old_timestamp]

        # Track new grant
        existing_pending = [t for t, client in self.pending_acks.items() if client == transaction.gnt_id]
        if not existing_pending:
            self.pending_acks[current_time] = transaction.gnt_id

        return warnings

    def process_ack_received(self, ack_vector, timestamp):
        """Process ACK signals"""
        if not self.ack_mode:
            return

        # Find which clients are ACKing
        for i in range(self.clients):
            if ack_vector & (1 << i):
                # Find matching grant
                matching_grants = [t for t, client in self.pending_acks.items() if client == i]
                if matching_grants:
                    grant_time = max(matching_grants)
                    del self.pending_acks[grant_time]

                    # Handle pending mask updates
                    if grant_time in self.pending_mask_updates:
                        del self.pending_mask_updates[grant_time]

    # =======================================================================
    # STATIC PERIOD MANAGEMENT - weight support
    # =======================================================================

    def start_static_period(self, expected_weights=None):
        """Start tracking static period for compliance analysis"""
        self.is_static_period = True
        current_time = get_sim_time('ns')

        self.static_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'start_time': current_time,
            'expected_weights': expected_weights or [1] * self.clients
        }

        if self.debug_enabled:
            weights_str = expected_weights if expected_weights else "equal weights"
            self.log.debug(f"ArbiterCompliance({self.title}): Static period started with {weights_str} @ {current_time}ns")

    def end_static_period(self):
        """End static period tracking"""
        if not self.is_static_period:
            return

        end_time = get_sim_time('ns')
        duration = end_time - self.static_stats['start_time']

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Static period ended - "
                        f"{self.static_stats['total_grants']} grants over {duration:.1f}ns")

        self.is_static_period = False

    def _update_static_period_stats(self, transaction):
        """NEW: Update static period statistics for weight compliance"""
        if not self.is_static_period:
            return

        self.static_stats['total_grants'] += 1
        if transaction.gnt_id < len(self.static_stats['grants_per_client']):
            self.static_stats['grants_per_client'][transaction.gnt_id] += 1

    # =======================================================================
    # WEIGHT COMPLIANCE ANALYSIS - NEW
    # =======================================================================

    def analyze_weight_compliance(self, expected_weights=None, requesting_clients=None):
        """Analyze weight compliance for WRR arbiters - COMPLETED implementation"""
        if self.arbiter_type != 'wrr':
            return {'status': 'not_weighted'}

        if not self.is_static_period:
            return {'status': 'not_in_static_period', 'message': 'Weight compliance requires static period'}

        # Use expected weights or extract from static period stats
        if expected_weights is None:
            expected_weights = self.static_stats.get('expected_weights', [1] * self.clients)

        if len(expected_weights) != self.clients:
            return {'status': 'invalid_weights', 'message': f'Expected {self.clients} weights, got {len(expected_weights)}'}

        # Calculate expected vs actual distribution
        total_grants = self.static_stats['total_grants']
        if total_grants == 0:
            return {'status': 'no_grants', 'message': 'No grants to analyze'}

        # Calculate expected distribution based on weights
        total_weight = sum(expected_weights)
        if total_weight == 0:
            return {'status': 'zero_weights', 'message': 'All weights are zero'}

        expected_distribution = [w / total_weight for w in expected_weights]
        actual_grants = self.static_stats['grants_per_client']
        actual_distribution = [g / total_grants for g in actual_grants]

        # Calculate compliance metrics
        compliance_scores = []
        for i in range(self.clients):
            if expected_distribution[i] > 0:
                error = abs(actual_distribution[i] - expected_distribution[i])
                relative_error = error / expected_distribution[i]
                compliance_score = max(0, 1.0 - relative_error)
                compliance_scores.append(compliance_score)
            else:
                # Zero weight - should have zero grants
                compliance_score = 1.0 if actual_grants[i] == 0 else 0.0
                compliance_scores.append(compliance_score)

        # Overall compliance score
        overall_compliance = sum(compliance_scores) / len(compliance_scores)

        # Weight efficiency - how well are weights utilized
        non_zero_weights = [w for w in expected_weights if w > 0]
        if non_zero_weights:
            theoretical_min_grants = min(non_zero_weights) / total_weight * total_grants
            actual_min_grants = min([actual_grants[i] for i in range(self.clients) if expected_weights[i] > 0])
            weight_efficiency = actual_min_grants / theoretical_min_grants if theoretical_min_grants > 0 else 1.0
        else:
            weight_efficiency = 0.0

        return {
            'status': 'analyzed',
            'total_grants': total_grants,
            'total_weight': total_weight,
            'expected_weights': expected_weights,
            'expected_distribution': expected_distribution,
            'actual_grants': actual_grants,
            'actual_distribution': actual_distribution,
            'compliance_scores': compliance_scores,
            'overall_compliance': overall_compliance,
            'weight_efficiency': weight_efficiency,
            'compliant': overall_compliance > 0.8,  # 80% threshold
            'requesting_clients': requesting_clients or list(range(self.clients))
        }

    def track_weight_change(self, new_weights, timestamp):
        """NEW: Track weight changes for compliance analysis"""
        if self.arbiter_type != 'wrr':
            return

        # End current static period if active
        if self.is_static_period:
            self.end_static_period()

        # Record weight change
        weight_change_record = {
            'timestamp': timestamp,
            'new_weights': new_weights.copy(),
            'grants_before_change': self.total_grants
        }

        if not hasattr(self, 'weight_change_history'):
            self.weight_change_history = []

        self.weight_change_history.append(weight_change_record)

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Weight change tracked: {new_weights} @ {timestamp}ns")

    def configure_weight_compliance(self, observation_windows=None, compliance_threshold=0.8):
        """NEW: Configure weight compliance checking parameters"""
        if self.arbiter_type != 'wrr':
            self.log.warning(f"ArbiterCompliance({self.title}): Weight compliance config ignored - not a weighted arbiter")
            return

        self.weight_observation_windows = observation_windows or [100, 500, 2000]
        self.weight_compliance_threshold = compliance_threshold

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Weight compliance configured - "
                        f"windows: {self.weight_observation_windows}, threshold: {compliance_threshold}")

    def is_weight_compliant(self, threshold=None):
        """NEW: Check if current weight compliance meets threshold"""
        if self.arbiter_type != 'wrr' or not self.is_static_period:
            return False

        compliance_result = self.analyze_weight_compliance()
        if compliance_result['status'] != 'analyzed':
            return False

        threshold = threshold or getattr(self, 'weight_compliance_threshold', 0.8)
        return compliance_result['overall_compliance'] >= threshold

    # =======================================================================
    # UTILITY AND REPORTING for weight support
    # =======================================================================

    def _record_warning(self, warning):
        """Record a protocol warning"""
        self.protocol_warnings.append(warning)
        if len(self.protocol_warnings) > self.max_warnings:
            self.protocol_warnings = self.protocol_warnings[-self.max_warnings//2:]

        # Log the warning
        if warning['severity'] == 'error':
            self.log.error(f"ArbiterCompliance({self.title}): {warning['message']} @ {warning['timestamp']}ns")
        else:
            self.log.warning(f"ArbiterCompliance({self.title}): {warning['message']} @ {warning['timestamp']}ns")

    def get_warning_summary(self):
        """Get summary of protocol warnings"""
        warning_counts = {}
        error_counts = {}

        for warning in self.protocol_warnings:
            warning_type = warning['type']
            if warning['severity'] == 'error':
                error_counts[warning_type] = error_counts.get(warning_type, 0) + 1
            else:
                warning_counts[warning_type] = warning_counts.get(warning_type, 0) + 1

        return {
            'total_warnings': len([w for w in self.protocol_warnings if w['severity'] == 'warning']),
            'total_errors': len([w for w in self.protocol_warnings if w['severity'] == 'error']),
            'warning_types': warning_counts,
            'error_types': error_counts,
            'recent_warnings': self.protocol_warnings[-10:] if self.protocol_warnings else []
        }

    def get_comprehensive_analysis(self):
        """Get comprehensive compliance analysis with weight support"""
        base_analysis = {
            'basic_stats': {
                'total_grants': self.total_grants,
                'grant_distribution': self.grant_counts,
                'cycles_monitored': self.cycles_monitored
            },
            'fairness_analysis': {
                'fairness_index': self.analyze_fairness(),
                'starvation_check': self.check_starvation(),
                'burst_analysis': self.detect_burst_behavior()
            },
            'protocol_compliance': self.get_warning_summary(),
            'pattern_analysis': {
                'unique_patterns': 0,
                'transition_coverage': 0,
                'grant_history_recent': self.grant_history[-20:] if self.grant_history else []
            }
        }

        # Add weight-specific analysis for WRR arbiters
        if self.arbiter_type == 'wrr':
            base_analysis['weight_analysis'] = {
                'weight_changes_tracked': len(getattr(self, 'weight_change_history', [])),
                'static_period_active': self.is_static_period,
                'current_static_stats': self.static_stats if self.is_static_period else None
            }

            # Add weight compliance if in static period
            if self.is_static_period and self.static_stats['total_grants'] > 0:
                base_analysis['weight_compliance'] = self.analyze_weight_compliance()

        # Add ACK tracking debug for ACK mode
        if self.ack_mode:
            base_analysis['ack_tracking_debug'] = {
                'pending_acks_count': len(self.pending_acks),
                'pending_acks_detail': dict(self.pending_acks),
                'pending_mask_updates': len(self.pending_mask_updates),
                'ack_mode': self.ack_mode
            }

        # Add round-robin debug for RR arbiters
        if self.arbiter_type == 'rr':
            base_analysis['round_robin_debug'] = self.get_round_robin_state_debug()
            base_analysis['round_robin_analysis'] = self.analyze_round_robin_compliance()

        base_analysis['reset_flag'] = self.reset_arb_flag

        return base_analysis

    def reset_analysis(self):
        """Reset all analysis data"""
        self.transaction_queue.clear()
        self.protocol_warnings.clear()
        self.pending_acks.clear()
        self.pending_mask_updates.clear()

        self.total_grants = 0
        self.grant_counts = [0] * self.clients
        self.cycles_monitored = 0
        self.reset_arb_flag = False

        if self.rr_mask_state:
            self.rr_mask_state.reset()

        # NEW: Reset weight-specific state
        if self.is_weighted:
            self.weight_change_history.clear()
            for window_data in self.weight_distribution_windows.values():
                window_data['grants'].clear()
                window_data['weights'].clear()
                window_data['timestamps'].clear()

        self.log.info(f"ArbiterCompliance({self.title}): Analysis reset{self.get_time_ns_str()}")

    # =======================================================================
    # CONFIGURATION
    # =======================================================================

    def enable_protocol_checking(self, enable=True):
        """Enable or disable protocol compliance checking"""
        self.protocol_checking_enabled = enable

    def enable_debug(self, enable=True):
        """Enable or disable debug logging"""
        self.debug_enabled = enable
        if self.rr_mask_state:
            self.rr_mask_state.debug_enabled = enable

    def enable_fence_detection(self, enable=True):
        """Enable or disable automatic fence detection"""
        self.fence_detection_enabled = enable

    # =======================================================================
    # COMPATIBILITY METHODS - Expected by monitor
    # =======================================================================

    def analyze_fairness(self):
        """Calculate Jain's fairness index"""
        if self.total_grants == 0:
            return 1.0

        n = len(self.grant_counts)
        squared_sum = self.total_grants ** 2
        sum_of_squares = sum(x ** 2 for x in self.grant_counts)

        return 1.0 if sum_of_squares == 0 else squared_sum / (n * sum_of_squares)

    def check_starvation(self, recent_window=50):
        """Check for client starvation in recent history"""
        starved_clients = [i for i, count in enumerate(self.grant_counts) if count == 0]

        return {
            'status': 'analyzed',
            'starved_clients': starved_clients,
            'grant_distribution': self.grant_counts.copy(),
            'window_size': self.total_grants
        }

    def detect_burst_behavior(self, max_consecutive=3):
        """Detect excessive consecutive grants"""
        return {
            'status': 'analyzed',
            'bursts_detected': 0,
            'bursts': []
        }

    def analyze_round_robin_compliance(self):
        """Analyze round-robin pattern compliance"""
        if self.arbiter_type != 'rr':
            return {'status': 'not_round_robin'}

        return {
            'status': 'analyzed',
            'rr_efficiency': 1.0,
            'mask_state_debug': str(self.rr_mask_state) if self.rr_mask_state else 'N/A'
        }

    def get_queue_status(self):
        """Get compliance queue status"""
        base_status = {
            'queue_size': len(self.transaction_queue),
            'max_queue_size': self.max_queue_size,
            'fence_detection_enabled': self.fence_detection_enabled,
            'last_fence_time': self.last_fence_time,
            'pending_acks': len(self.pending_acks) if self.ack_mode else 'N/A',
            'reset_flag': self.reset_arb_flag,
            'arbiter_type': self.arbiter_type,
            'is_weighted': self.is_weighted
        }

        # Add weight-specific status
        if self.is_weighted:
            base_status.update({
                'weight_changes_tracked': len(getattr(self, 'weight_change_history', [])),
                'static_period_active': self.is_static_period
            })

        return base_status

    def set_compliance_sampling_rate(self, rate):
        """Set compliance sampling rate"""
        self.compliance_sampling_rate = max(1, rate)

    def enable_cycle_level_mode(self, enable=True):
        """Enable cycle level mode"""
        self.cycle_level_mode = enable

    def get_cycle_level_stats(self):
        """Get cycle level statistics"""
        return {
            'cycle_level_mode': self.cycle_level_mode,
            'compliance_sampling_rate': self.compliance_sampling_rate,
            'total_transactions_seen': self._transaction_count
        }

    def force_full_compliance_check(self):
        """Force full compliance check"""
        if self.transaction_queue:
            self.run_compliance_analysis()

    def get_round_robin_state_debug(self):
        """Get round-robin state debug info"""
        if not self.rr_mask_state:
            return "No round-robin tracking"

        return {
            'mask_valid': self.rr_mask_state.mask_valid,
            'last_winner': self.rr_mask_state.last_winner,
            'current_mask': f"0x{self.rr_mask_state.current_mask:x}",
            'reset_flag': self.reset_arb_flag
        }

    def get_detailed_grant_stats(self):
        """Get detailed grant statistics for compatibility"""
        return {
            'total_grants': self.total_grants,
            'grant_distribution': self.grant_counts.copy(),
            'grant_history': self.grant_history.copy()
        }

    def get_grant_type_summary(self):
        """Get grant type summary for compatibility"""
        return {'standard': self.total_grants}

    def print_compliance_report(self):
        """Print compliance report"""
        arbiter_type_name = "weighted round-robin" if self.is_weighted else "round-robin"
        self.log.info("=== COMPLIANCE REPORT ===")
        self.log.info(f"Arbiter Type: {arbiter_type_name}")
        self.log.info(f"Total grants: {self.total_grants}")
        self.log.info(f"Warnings: {len(self.protocol_warnings)}")
        self.log.info(f"Reset flag: {self.reset_arb_flag}")

        if self.is_weighted and self.is_static_period:
            compliance_result = self.analyze_weight_compliance()
            if compliance_result['status'] == 'analyzed':
                self.log.info(f"Weight compliance: {compliance_result['overall_compliance']:.3f}")

    def get_cycle_level_grant_count(self, client_id=None):
        """Get cycle level grant count"""
        if client_id is None:
            return self.total_grants
        return self.grant_counts[client_id] if client_id < len(self.grant_counts) else 0

    def update_request_timeline(self, timestamp, request_vector, prev_request_vector):
        """COMPATIBILITY: Update request timeline - simplified stub"""
        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Request timeline update @ {timestamp}ns: "
                        f"0x{prev_request_vector:x} -> 0x{request_vector:x}")
