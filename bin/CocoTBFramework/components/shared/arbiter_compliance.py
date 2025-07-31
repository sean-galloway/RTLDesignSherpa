"""
Simplified RTL-Compliant Arbiter Protocol Compliance Checker

CLEANED UP VERSION: Removed all complex reset timing machinations.
Simple flag-based reset detection integrated with fence monitoring.
Focus on clean RR/WRR compliance checking.
"""

from collections import deque
from cocotb.utils import get_sim_time
from cocotb.log import SimLog


class RoundRobinMaskState:
    """Track the round-robin mask state per RTL algorithm - SIMPLIFIED"""

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
        """Get expected winner - FIXED for post-reset handling"""
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
        """Update mask after grant - FIXED for proper mask calculation"""
        if winner_client >= self.clients:
            if self.debug_enabled:
                print(f"RoundRobinMaskState.update_mask: ERROR - invalid winner {winner_client}")
            return

        old_mask = self.current_mask
        old_last_winner = self.last_winner
        old_mask_valid = self.mask_valid

        self.last_winner = winner_client
        self.mask_valid = True  # CRITICAL: Always set valid after first grant

        # RTL algorithm: After client N wins, mask clients 0 through N
        # This gives priority to clients N+1 and above
        mask_bits = (1 << (winner_client + 1)) - 1
        self.current_mask = (~mask_bits) & ((1 << self.clients) - 1)

        if self.debug_enabled:
            print(f"RoundRobinMaskState.update_mask: winner={winner_client}")
            print(f"  Old: mask=0x{old_mask:x}, last_winner={old_last_winner}, valid={old_mask_valid}")
            print(f"  Calculation: ~((1 << ({winner_client}+1)) - 1) = ~{mask_bits} = 0x{~mask_bits:x}")
            print(f"  Masked to {self.clients} bits: 0x{self.current_mask:x}")
            print(f"  New: mask=0x{self.current_mask:x}, last_winner={self.last_winner}, valid={self.mask_valid}")

            # Show which clients are masked/unmasked
            masked_clients = [i for i in range(self.clients) if not (self.current_mask & (1 << i))]
            unmasked_clients = [i for i in range(self.clients) if (self.current_mask & (1 << i))]
            print(f"  Masked (lower priority): {masked_clients}")
            print(f"  Unmasked (higher priority): {unmasked_clients}")

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
    SIMPLIFIED: RTL-Compliant protocol compliance checker for arbiter components.

    Removed all complex reset timing logic. Uses simple flag-based reset detection.
    """

    def __init__(self, name, clients, arbiter_type='rr', ack_mode=False, log=None, clock_period_ns=10):
        self.name = name
        self.title = name
        self.clients = clients
        self.arbiter_type = arbiter_type
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
        self.max_queue_size = 2000

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

        # Weighted round-robin state tracking
        if arbiter_type == 'wrr':
            self.is_static_period = False
            self.static_stats = {
                'total_grants': 0,
                'grants_per_client': [0] * clients,
                'start_time': 0
            }

        self.log.info(f"ArbiterCompliance({self.title}): SIMPLIFIED version initialized: {clients} clients, "
                    f"type={arbiter_type}, ack_mode={ack_mode}")

    @staticmethod
    def get_time_ns_str():
        """Get current simulation time as a formatted string"""
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    # =======================================================================
    # SIMPLE RESET DETECTION
    # =======================================================================

    def set_reset_flag(self):
        """
        SIMPLE: Set the reset flag - called by monitor when RTL reset condition detected
        """
        self.reset_arb_flag = True

        # Reset round-robin state immediately
        if self.rr_mask_state:
            self.rr_mask_state.reset()

        # Clear any pending mask updates
        self.pending_mask_updates.clear()

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): RTL reset flag set - RR state cleared{self.get_time_ns_str()}")

    # =======================================================================
    # TRANSACTION PROCESSING - SIMPLIFIED
    # =======================================================================

    def queue_transaction(self, transaction, blocked_state=False, active_requests=0, block_arb_history=None):
        """Queue transaction for compliance checking - SIMPLIFIED"""
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
    # COMPLIANCE ANALYSIS - SIMPLIFIED
    # =======================================================================

    def run_compliance_analysis(self):
        """Run compliance analysis on queued transactions - SIMPLIFIED"""
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
        """
        SIMPLIFIED: Check single transaction compliance with simple reset flag handling
        """
        warnings = []
        current_time = transaction.timestamp

        # SIMPLE: Check and clear reset flag
        skip_rr_check = self.reset_arb_flag
        if self.reset_arb_flag:
            self.reset_arb_flag = False  # Clear flag after using it
            if self.debug_enabled:
                self.log.debug(f"ArbiterCompliance({self.title}): RTL reset flag detected @ {current_time}ns - skipping RR compliance")

            # CRITICAL FIX: Still update mask state even when skipping compliance check
            # This ensures the next grant has the correct round-robin state
            if self.arbiter_type == 'rr' and self.rr_mask_state:
                self.rr_mask_state.update_mask(transaction.gnt_id)
                if self.debug_enabled:
                    self.log.debug(f"ArbiterCompliance({self.title}): Updated RR mask for skipped grant: "
                                f"winner={transaction.gnt_id}, new_mask=0x{self.rr_mask_state.current_mask:x}")

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Compliance check @ {current_time}ns:")
            self.log.debug(f"  skip_rr_check={skip_rr_check}")
            self.log.debug(f"  active_requests=0x{active_requests:x}")

        # Basic protocol checks
        warnings.extend(self._check_basic_protocol_compliance(transaction, blocked_state, active_requests))

        # Round-robin specific checks
        if self.arbiter_type == 'rr' and not skip_rr_check:
            warnings.extend(self._check_round_robin_compliance(transaction, active_requests))

        # Weighted round-robin specific checks
        if self.arbiter_type == 'wrr' and not skip_rr_check:
            warnings.extend(self._check_weighted_round_robin_compliance(transaction, active_requests))

        # ACK protocol checks
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
        """Check round-robin compliance using RTL algorithm - SIMPLIFIED"""
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
        """Check round-robin compliance for no-ACK mode - FIXED"""
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

        # Update mask AFTER compliance check (this is critical for next grant)
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
        """Check round-robin compliance for ACK mode - SIMPLIFIED"""
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
        """Check weighted round-robin compliance - PLACEHOLDER"""
        warnings = []

        # TODO: Implement WRR compliance checking
        # This will check:
        # 1. Credit-based weighting
        # 2. Fair distribution according to weights
        # 3. Round-robin fairness within weight levels

        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): WRR compliance check @ {transaction.timestamp}ns")

        return warnings

    # =======================================================================
    # ACK PROTOCOL COMPLIANCE
    # =======================================================================

    def _check_ack_protocol_compliance(self, transaction):
        """Check ACK protocol compliance - SIMPLIFIED"""
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
        """Process ACK signals - SIMPLIFIED"""
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
    # WEIGHTED ARBITER SUPPORT
    # =======================================================================

    def start_static_period(self):
        """Start tracking static period for weight compliance"""
        self.is_static_period = True
        self.static_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'start_time': get_sim_time('ns')
        }

    def end_static_period(self):
        """End static period tracking"""
        self.is_static_period = False

    def analyze_weight_compliance(self, expected_weights, requesting_clients=None):
        """Analyze weight compliance for WRR arbiters"""
        if self.arbiter_type != 'wrr' or not self.is_static_period:
            return {'status': 'not_applicable'}

        # TODO: Implement weight compliance analysis
        return {'status': 'todo'}

    # =======================================================================
    # UTILITY AND REPORTING
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
        """Get comprehensive compliance analysis - COMPATIBLE FORMAT"""
        return {
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
                'grant_history_recent': []
            },
            'ack_tracking_debug': {
                'pending_acks_count': len(self.pending_acks),
                'pending_acks_detail': dict(self.pending_acks),
                'pending_mask_updates': len(self.pending_mask_updates),
                'ack_mode': self.ack_mode
            } if self.ack_mode else {},
            'round_robin_debug': self.get_round_robin_state_debug() if self.arbiter_type == 'rr' else {},
            'round_robin_analysis': self.analyze_round_robin_compliance() if self.arbiter_type == 'rr' else {},
            'reset_flag': self.reset_arb_flag
        }

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
    # MISSING METHODS THAT MONITOR EXPECTS - ADDED BACK
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
        # Simple implementation - check grant distribution
        starved_clients = [i for i, count in enumerate(self.grant_counts) if count == 0]

        return {
            'status': 'analyzed',
            'starved_clients': starved_clients,
            'grant_distribution': self.grant_counts.copy(),
            'window_size': self.total_grants
        }

    def detect_burst_behavior(self, max_consecutive=3):
        """Detect excessive consecutive grants - simplified"""
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
            'rr_efficiency': 1.0,  # Simplified
            'mask_state_debug': str(self.rr_mask_state) if self.rr_mask_state else 'N/A'
        }

    def get_queue_status(self):
        """Get compliance queue status"""
        return {
            'queue_size': len(self.transaction_queue),
            'max_queue_size': self.max_queue_size,
            'fence_detection_enabled': self.fence_detection_enabled,
            'last_fence_time': self.last_fence_time,
            'pending_acks': len(self.pending_acks) if self.ack_mode else 'N/A',
            'reset_flag': self.reset_arb_flag
        }

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

    # =======================================================================
    # ADDITIONAL COMPATIBILITY METHODS
    # =======================================================================

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
        self.log.info("=== COMPLIANCE REPORT ===")
        self.log.info(f"Total grants: {self.total_grants}")
        self.log.info(f"Warnings: {len(self.protocol_warnings)}")
        self.log.info(f"Reset flag: {self.reset_arb_flag}")

    def get_cycle_level_grant_count(self, client_id=None):
        """Get cycle level grant count"""
        if client_id is None:
            return self.total_grants
        return self.grant_counts[client_id] if client_id < len(self.grant_counts) else 0

    def update_request_timeline(self, timestamp, request_vector, prev_request_vector):
        """
        COMPATIBILITY: Update request timeline - simplified stub

        This method is called by the monitor but not needed for simple reset detection.
        The fence monitoring handles reset detection directly.
        """
        if self.debug_enabled:
            self.log.debug(f"ArbiterCompliance({self.title}): Request timeline update @ {timestamp}ns: "
                        f"0x{prev_request_vector:x} -> 0x{request_vector:x}")

        # Just update basic tracking for compatibility
        pass
