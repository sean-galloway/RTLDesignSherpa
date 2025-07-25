"""
Enhanced Generic Arbiter Monitor Component for Verification

This module provides improved ArbiterMonitor classes for observing various types of arbiter interfaces
including round-robin and weighted round-robin arbiters.

Key improvements:
- Better signal sampling timing
- Proper grant_valid checking
- Improved signal resolution handling
- More robust transaction tracking
- Added timestamps to critical log messages
- Fixed debug logging rate limiting issues
- Human-readable statistics formatting and reporting
"""

import cocotb
from collections import deque, namedtuple
from cocotb.triggers import FallingEdge, RisingEdge, Edge, Timer
from cocotb.utils import get_sim_time
from cocotb.log import SimLog

# Define Transaction type for arbiters
ArbiterTransaction = namedtuple('ArbiterTransaction', [
    'req_vector',      # Request vector from clients
    'gnt_vector',      # Grant vector indicating which client was selected
    'gnt_id',          # ID of the granted client
    'cycle_count',     # Number of cycles between request and grant
    'timestamp',       # Timestamp when grant was issued
    'weights',         # Optional weights (for weighted arbiters)
    'metadata'         # Dictionary for any additional metadata
])


class ArbiterMonitor:
    """
    Generic Arbiter Monitor component that observes arbiter transactions.

    This class provides:
    - Monitoring of request and grant signals with proper timing
    - Transaction tracking with timing information
    - Integrated pattern analysis and fairness checking
    - Support for both round-robin and weighted round-robin arbiters
    - Configurable callbacks for events
    - Human-readable statistics reporting
    """

    def __init__(self, dut, title, clock, reset_n, req_signal, gnt_valid_signal, gnt_signal,
                    gnt_id_signal, gnt_ack_signal=None, block_arb_signal=None,
                    max_thresh_signal=None, is_weighted=False, clients=None, log=None,
                    clock_period_ns=10):
        """
        Initialize Arbiter Monitor component.

        Args:
            dut: Device under test
            title: Component title (for logging)
            clock: Clock signal
            reset_n: Reset signal (active low)
            req_signal: Request input signal (bus)
            gnt_valid_signal: Grant valid output signal
            gnt_signal: Grant output signal (bus)
            gnt_id_signal: Grant ID output signal
            gnt_ack_signal: Grant acknowledge input signal (bus), optional
            block_arb_signal: Signal to block arbitration, optional
            max_thresh_signal: Maximum threshold signal for weighted arbiters, optional
            is_weighted: True if monitoring a weighted arbiter, False otherwise
            clients: Number of clients (derived from signal width if None)
            log: Logger instance (creates new if None)
            clock_period_ns: Clock period in nanoseconds
        """
        self.dut = dut
        self.title = title
        self.clock = clock
        self.reset_n = reset_n
        self.req_signal = req_signal
        self.gnt_valid_signal = gnt_valid_signal
        self.gnt_signal = gnt_signal
        self.gnt_id_signal = gnt_id_signal
        self.gnt_ack_signal = gnt_ack_signal
        self.block_arb_signal = block_arb_signal
        self.max_thresh_signal = max_thresh_signal
        self.is_weighted = is_weighted

        # Store clock period
        self.clock_period_ns = clock_period_ns

        # Create logger - FIXED: Use the underlying logger directly for debug messages
        # The issue was that RateLimitedLogger was suppressing debug messages
        if log and hasattr(log, 'base_log'):
            # If passed a RateLimitedLogger, use its underlying logger for monitor
            self.log = log.base_log
        elif log:
            # If passed a regular logger, use it directly
            self.log = log
        else:
            # Create a new logger
            self.log = SimLog(f"cocotb.{dut._name}.{title}")

        # Determine number of clients from signal width if not specified
        if clients is None:
            try:
                # Try to get the width from the signal
                if hasattr(self.req_signal, '_range'):
                    self.clients = len(self.req_signal._range)
                else:
                    # Fallback: try to read the signal and get its width
                    val = self.req_signal.value
                    if hasattr(val, 'binstr'):
                        self.clients = len(val.binstr)
                    else:
                        self.clients = val.n_bits
            except (AttributeError, TypeError):
                self.log.warning(f"ArbiterMonitor({self.title}): Could not determine number of clients from req_signal width, using default of 4")
                self.clients = 4  # Default value
        else:
            self.clients = int(clients)

        # Transaction tracking
        self.transactions = deque(maxlen=1000)  # Limit memory usage
        self.pending_requests = {}  # Maps client index to request time
        self.total_transactions = 0
        self.active_request_vector = 0
        self.blocked = False

        # Basic counters and statistics
        self.stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'avg_wait_time': 0,
            'wait_time_per_client': [0] * self.clients,
            'total_cycles': 0,
            'grant_sequences': [],  # Track grant sequences for pattern analysis
        }

        # Static period tracking
        self.is_static_period = False
        self.static_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'total_transactions': 0,
            'start_time': 0,
            'client_stats': []
        }

        # Pattern analysis tracking
        self.grant_history = []
        self.transition_matrix = {}
        self.consecutive_grants = {}
        self.current_consecutive = 0
        self.last_grant_client = None
        self.cycles_since_reset = 0

        # Latency tracking
        self.latency_histogram = {}
        self.max_latency = 0
        self.min_latency = float('inf')

        # Pattern coverage tracking
        self.patterns_seen = set()
        self.transitions_seen = set()
        self.violations = []

        # Callbacks
        self.transaction_callback = None
        self.reset_callback = None

        # Control flags
        self.monitoring_enabled = True
        self.debug_enabled = True

        self.log.info(f"ArbiterMonitor({self.title}): initialized with {self.clients} clients, "
                    f"clock period {self.clock_period_ns}ns{self.get_time_ns_str()}")

    @staticmethod
    def get_time_ns_str():
        """Get current simulation time as a formatted string"""
        time_ns = get_sim_time('ns')
        return f' @ {time_ns}ns'

    def enable_debug(self, enable=True):
        """Enable or disable debug logging"""
        self.debug_enabled = enable
        self.log.info(f"ArbiterMonitor({self.title}): Debug logging {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    def enable_monitoring(self, enable=True):
        """Enable or disable monitoring"""
        self.monitoring_enabled = enable
        self.log.info(f"ArbiterMonitor({self.title}): Monitoring {'enabled' if enable else 'disabled'}{self.get_time_ns_str()}")

    def start_monitoring(self):
        """Start all monitoring coroutines"""
        # Add monitor coroutines to scheduler
        self._req_monitor_thread = cocotb.start_soon(self._monitor_requests())
        self._gnt_monitor_thread = cocotb.start_soon(self._monitor_grants())
        self._reset_monitor_thread = cocotb.start_soon(self._monitor_reset())

        if self.block_arb_signal:
            self._block_monitor_thread = cocotb.start_soon(self._monitor_block())

        if self.max_thresh_signal and self.is_weighted:
            self._thresh_monitor_thread = cocotb.start_soon(self._monitor_thresholds())

        self.log.info(f"ArbiterMonitor({self.title}): All monitoring threads started{self.get_time_ns_str()}")

    def add_transaction_callback(self, callback):
        """Register a callback function for completed transactions."""
        self.transaction_callback = callback
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Added transaction callback: {callback.__name__}{self.get_time_ns_str()}")

    def add_reset_callback(self, callback):
        """Register a callback function for reset events."""
        self.reset_callback = callback
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Added reset callback: {callback.__name__}{self.get_time_ns_str()}")

    def set_static_period(self, is_static):
        """Set whether we're in a static test period for weight compliance checking"""
        self.is_static_period = is_static
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Static period {'started' if is_static else 'ended'}{self.get_time_ns_str()}")

    def reset_static_stats(self):
        """Reset statistics for a new static period"""
        self.static_stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'total_transactions': 0,
            'start_time': get_sim_time('ns'),
            'client_stats': []
        }
        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Static period statistics reset{self.get_time_ns_str()}")

    def get_static_period_stats(self):
        """Get statistics for the current static period"""
        if not hasattr(self, 'static_stats'):
            return {'total_grants': 0, 'client_stats': []}

        # Calculate percentages and create client stats
        total_grants = self.static_stats['total_grants']
        client_stats = []

        for i in range(self.clients):
            grants = self.static_stats['grants_per_client'][i]
            percentage = (grants / total_grants * 100) if total_grants > 0 else 0

            client_stats.append({
                'client_id': i,
                'grants': grants,
                'percentage': percentage
            })

        return {
            'total_grants': total_grants,
            'total_transactions': self.static_stats['total_transactions'],
            'client_stats': client_stats,
            'duration_ns': get_sim_time('ns') - self.static_stats['start_time']
        }

    def analyze_static_weight_compliance(self, expected_weights, requesting_clients=None):
        """Analyze weight compliance for static period data, optionally filtering to requesting clients only"""
        if not hasattr(self, 'static_stats') or self.static_stats['total_grants'] == 0:
            return {'status': 'no_data'}

        total_grants = self.static_stats['total_grants']

        # If requesting_clients is provided, filter to only those clients
        if requesting_clients is not None:
            # Only consider requesting clients for weight compliance
            filtered_weights = [expected_weights[i] if i in requesting_clients else 0 for i in range(len(expected_weights))]
            total_expected_weight = sum(filtered_weights)
            clients_to_analyze = requesting_clients
        else:
            # Use all clients (original behavior)
            total_expected_weight = sum(expected_weights)
            clients_to_analyze = list(range(min(len(expected_weights), self.clients)))

        if total_expected_weight == 0:
            return {'status': 'no_requesting_clients'}

        compliance_data = []
        overall_compliance_sum = 0

        for i in clients_to_analyze:
            actual_grants = self.static_stats['grants_per_client'][i]

            if requesting_clients is not None:
                # Only requesting clients contribute to expected weight
                expected_weight = expected_weights[i] if i in requesting_clients else 0
            else:
                expected_weight = expected_weights[i]

            expected_ratio = expected_weight / total_expected_weight if total_expected_weight > 0 else 0
            actual_ratio = actual_grants / total_grants

            # Calculate compliance (1.0 - deviation)
            compliance = 1.0 - abs(expected_ratio - actual_ratio) if expected_ratio > 0 else 1.0
            overall_compliance_sum += compliance

            compliance_data.append({
                'client': i,
                'expected_weight': expected_weight,
                'expected_ratio': expected_ratio,
                'actual_grants': actual_grants,
                'actual_ratio': actual_ratio,
                'compliance': compliance
            })

        avg_compliance = overall_compliance_sum / len(compliance_data) if compliance_data else 0

        return {
            'status': 'analyzed',
            'overall_compliance': avg_compliance,
            'client_compliance': compliance_data,
            'is_compliant': avg_compliance >= 0.75  # 75% compliance threshold for static periods (changed to >= to handle exact matches)
        }

    def _update_pattern_tracking(self, transaction):
        """Update all pattern tracking when a new transaction occurs"""
        grant_id = transaction.gnt_id
        self.cycles_since_reset += 1

        # Update grant history
        self.grant_history.append(grant_id)
        if len(self.grant_history) > 100:
            self.grant_history = self.grant_history[-50:]

        # Track patterns seen
        self.patterns_seen.add(transaction.req_vector)

        # Update transition matrix
        if self.last_grant_client is not None:
            transition = (self.last_grant_client, grant_id)
            self.transition_matrix[transition] = self.transition_matrix.get(transition, 0) + 1
            self.transitions_seen.add(transition)

        # Track consecutive grants
        if grant_id == self.last_grant_client:
            self.current_consecutive += 1
        else:
            if self.last_grant_client is not None:
                max_consecutive = self.consecutive_grants.get(self.last_grant_client, 0)
                self.consecutive_grants[self.last_grant_client] = max(max_consecutive, self.current_consecutive)
            self.current_consecutive = 1

        # Update latency tracking
        self._record_latency(transaction.cycle_count * self.clock_period_ns)

        # NEW: Update static period statistics if we're in a static period
        if hasattr(self, 'is_static_period') and self.is_static_period:
            if hasattr(self, 'static_stats'):
                self.static_stats['total_grants'] += 1
                self.static_stats['total_transactions'] += 1
                if grant_id < len(self.static_stats['grants_per_client']):
                    self.static_stats['grants_per_client'][grant_id] += 1

        # Update for next iteration
        self.last_grant_client = grant_id

    def _record_latency(self, latency_ns):
        """Record latency for histogram"""
        if latency_ns <= 0:
            return

        # Round to nearest 10ns bucket
        bucket = int(latency_ns / 10) * 10
        self.latency_histogram[bucket] = self.latency_histogram.get(bucket, 0) + 1

        self.max_latency = max(self.max_latency, latency_ns)
        self.min_latency = min(self.min_latency, latency_ns)

    def get_latency_percentiles(self):
        """Calculate latency percentiles"""
        if not self.latency_histogram:
            return {}

        # Flatten histogram to list of latencies
        latencies = []
        for bucket, count in self.latency_histogram.items():
            latencies.extend([bucket] * count)

        latencies.sort()
        n = len(latencies)

        if n == 0:
            return {}

        return {
            'p50': latencies[n // 2],
            'p90': latencies[int(n * 0.9)],
            'p95': latencies[int(n * 0.95)],
            'p99': latencies[int(n * 0.99)],
            'min': self.min_latency if self.min_latency != float('inf') else 0,
            'max': self.max_latency
        }

    def detect_burst_behavior(self, max_consecutive=3):
        """Detect excessive consecutive grants to same client"""
        bursts = []

        # Check current consecutive grants tracking
        for client_id, max_consecutive_seen in self.consecutive_grants.items():
            if max_consecutive_seen > max_consecutive:
                bursts.append({
                    'client': client_id,
                    'max_consecutive': max_consecutive_seen,
                    'threshold': max_consecutive
                })

        # Also check if current streak exceeds threshold
        if self.current_consecutive > max_consecutive and self.last_grant_client is not None:
            bursts.append({
                'client': self.last_grant_client,
                'max_consecutive': self.current_consecutive,
                'threshold': max_consecutive,
                'currently_active': True
            })

        return {
            'status': 'analyzed',
            'max_allowed_consecutive': max_consecutive,
            'bursts_detected': len(bursts),
            'bursts': bursts
        }

    def check_starvation(self, recent_window=50):
        """Check for client starvation in recent history - FIXED VERSION"""
        if len(self.grant_history) == 0:
            return {'status': 'no_data', 'starved_clients': [], 'grant_distribution': [0] * self.clients, 'window_size': 0}

        # Use the smaller of requested window or available history
        actual_window = min(recent_window, len(self.grant_history))

        if actual_window == 0:
            return {'status': 'no_data', 'starved_clients': [], 'grant_distribution': [0] * self.clients, 'window_size': 0}

        recent_grants = self.grant_history[-actual_window:]
        grant_counts = [0] * self.clients

        # Count grants for each client in the recent window
        for grant_id in recent_grants:
            if 0 <= grant_id < self.clients:  # Bounds check
                grant_counts[grant_id] += 1

        # Identify starved clients (no grants in recent window)
        starved_clients = [i for i, count in enumerate(grant_counts) if count == 0]

        # Debug logging with timestamp
        if self.debug_enabled and starved_clients:
            self.log.debug(f"ArbiterMonitor({self.title}): Starvation check: window={actual_window}, starved={starved_clients}{self.get_time_ns_str()}")
            self.log.debug(f"ArbiterMonitor({self.title}): Recent grant counts: {grant_counts}{self.get_time_ns_str()}")
            self.log.debug(f"ArbiterMonitor({self.title}): Recent grants: {recent_grants[-20:]}{self.get_time_ns_str()}")  # Last 20 grants

        return {
            'status': 'analyzed',
            'starved_clients': starved_clients,
            'grant_distribution': grant_counts,
            'window_size': actual_window,
            'total_grants_in_window': sum(grant_counts)
        }

    def get_transaction_count(self):
        """Return the total number of observed transactions"""
        return self.total_transactions

    def get_client_stats(self, client_id):
        """Get statistics for a specific client."""
        if client_id >= self.clients:
            self.log.error(f"ArbiterMonitor({self.title}): Invalid client ID: {client_id}, max is {self.clients-1}{self.get_time_ns_str()}")
            return None

        grants = self.stats['grants_per_client'][client_id]
        return {
            'grants': grants,
            'avg_wait_time': (self.stats['wait_time_per_client'][client_id] / grants) if grants > 0 else 0
        }

    def get_fairness_index(self):
        """Calculate Jain's fairness index for the arbiter."""
        grants = self.stats['grants_per_client']
        total_grants = sum(grants)

        if total_grants == 0:
            return 1.0  # No grants yet, assume fair

        n = len(grants)
        squared_sum = total_grants ** 2
        sum_of_squares = sum(x ** 2 for x in grants)

        return 1.0 if sum_of_squares == 0 else squared_sum / (n * sum_of_squares)

    def get_stats_summary(self):
        """Get a comprehensive statistics summary"""
        total_grants = self.stats['total_grants']

        summary = {
            'total_transactions': self.total_transactions,
            'total_grants': total_grants,
            'avg_wait_time': self.stats['avg_wait_time'],
            'fairness_index': self.get_fairness_index(),
            'client_stats': []
        }

        for i in range(self.clients):
            client_grants = self.stats['grants_per_client'][i]
            percentage = (client_grants / total_grants * 100) if total_grants > 0 else 0

            summary['client_stats'].append({
                'client_id': i,
                'grants': client_grants,
                'percentage': percentage,
                'avg_wait_time': (self.stats['wait_time_per_client'][i] / client_grants) if client_grants > 0 else 0
            })

        return summary

    def get_comprehensive_stats(self):
        """Get comprehensive statistics including all pattern analysis"""
        base_stats = self.get_stats_summary()

        # Pattern analysis
        burst_analysis = self.detect_burst_behavior()
        latency_percentiles = self.get_latency_percentiles()
        starvation_analysis = self.check_starvation()

        # Coverage analysis
        coverage_stats = {
            'pattern_coverage': {
                'unique_patterns_seen': len(self.patterns_seen),
                'single_client_patterns': sum(1 for p in self.patterns_seen if bin(p).count('1') == 1),
                'all_clients_pattern_seen': ((1 << self.clients) - 1) in self.patterns_seen,
            },
            'transition_coverage': {
                'transitions_seen': len(self.transitions_seen),
                'max_possible_transitions': self.clients * self.clients,
                'coverage_percent': (len(self.transitions_seen) / (self.clients * self.clients)) * 100 if self.clients > 0 else 0
            }
        }

        # Performance metrics
        throughput_stats = {
            'grants_per_cycle': base_stats['total_grants'] / self.cycles_since_reset if self.cycles_since_reset > 0 else 0,
            'latency_percentiles': latency_percentiles,
        }

        # Combine all statistics
        comprehensive_stats = {
            **base_stats,
            'burst_analysis': burst_analysis,
            'starvation_analysis': starvation_analysis,
            'coverage_analysis': coverage_stats,
            'performance_analysis': throughput_stats,
            'pattern_analysis': {
                'grant_history': self.grant_history[-20:] if len(self.grant_history) > 20 else self.grant_history,
                'transition_matrix': dict(list(self.transition_matrix.items())[:10]),  # First 10 transitions
                'violations': self.violations[-5:] if len(self.violations) > 5 else self.violations
            },
            'monitoring_metadata': {
                'cycles_monitored': self.cycles_since_reset,
                'debug_enabled': self.debug_enabled,
                'clients': self.clients
            }
        }

        return comprehensive_stats

    def reset_pattern_tracking(self):
        """Reset all pattern tracking (called on reset)"""
        self.grant_history.clear()
        self.transition_matrix.clear()
        self.consecutive_grants.clear()
        self.patterns_seen.clear()
        self.transitions_seen.clear()
        self.violations.clear()
        self.latency_histogram.clear()

        self.current_consecutive = 0
        self.last_grant_client = None
        self.cycles_since_reset = 0
        self.max_latency = 0
        self.min_latency = float('inf')

        if self.debug_enabled:
            self.log.debug(f"ArbiterMonitor({self.title}): Pattern tracking reset{self.get_time_ns_str()}")

    # =======================================================================
    # HUMAN-READABLE STATISTICS FORMATTING AND PRINTING METHODS
    # =======================================================================

    def print_comprehensive_stats(self):
        """Print comprehensive statistics in human-readable format to the monitor's log"""
        lines = []
        lines.append("=" * 80)
        lines.append("COMPREHENSIVE ARBITER STATISTICS REPORT")
        lines.append("=" * 80)
        lines.append(f"Report Generated: {self.get_time_ns_str()}")
        lines.append("")

        stats = self.get_comprehensive_stats()

        # Basic Statistics
        lines.append("BASIC STATISTICS:")
        lines.append("-" * 40)
        lines.append(f"  Total Transactions:     {stats['total_transactions']:,}")
        lines.append(f"  Total Grants:          {stats['total_grants']:,}")
        lines.append(f"  Average Wait Time:     {stats['avg_wait_time']:.2f} ns")
        lines.append(f"  Fairness Index:        {stats['fairness_index']:.3f}")
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

        # Performance Analysis
        perf = stats.get('performance_analysis', {})
        if perf:
            lines.append("PERFORMANCE ANALYSIS:")
            lines.append("-" * 40)
            lines.append(f"  Grants per Cycle:      {perf.get('grants_per_cycle', 0):.4f}")

            latency = perf.get('latency_percentiles', {})
            if latency:
                lines.append("  Latency Percentiles:")
                lines.append(f"    P50 (Median):        {latency.get('p50', 0):,} ns")
                lines.append(f"    P90:                 {latency.get('p90', 0):,} ns")
                lines.append(f"    P95:                 {latency.get('p95', 0):,} ns")
                lines.append(f"    P99:                 {latency.get('p99', 0):,} ns")
                lines.append(f"    Min:                 {latency.get('min', 0):,} ns")
                lines.append(f"    Max:                 {latency.get('max', 0):,} ns")
            lines.append("")

        # Burst Analysis
        burst_analysis = stats.get('burst_analysis', {})
        if burst_analysis:
            lines.append("BURST ANALYSIS:")
            lines.append("-" * 40)
            lines.append(f"  Max Allowed Consecutive: {burst_analysis.get('max_allowed_consecutive', 0)}")
            lines.append(f"  Bursts Detected:       {burst_analysis.get('bursts_detected', 0)}")

            bursts = burst_analysis.get('bursts', [])
            if bursts:
                lines.append("  Burst Details:")
                for i, burst in enumerate(bursts[:5]):  # Show first 5 bursts
                    active = " (ACTIVE)" if burst.get('currently_active', False) else ""
                    lines.append(f"    {i+1}. Client {burst['client']}: {burst['max_consecutive']} consecutive{active}")
                if len(bursts) > 5:
                    lines.append(f"    ... and {len(bursts) - 5} more bursts")
            lines.append("")

        # Starvation Analysis
        starvation = stats.get('starvation_analysis', {})
        if starvation.get('status') == 'analyzed':
            lines.append("STARVATION ANALYSIS:")
            lines.append("-" * 40)
            lines.append(f"  Analysis Window:       {starvation.get('window_size', 0)} grants")
            lines.append(f"  Total Grants in Window: {starvation.get('total_grants_in_window', 0)}")

            starved_clients = starvation.get('starved_clients', [])
            if starved_clients:
                lines.append(f"  Starved Clients:       {starved_clients}")
                lines.append("  ⚠️  WARNING: Client starvation detected!")
            else:
                lines.append(f"  Starved Clients:       None ✓")

            # Show grant distribution in recent window
            grant_dist = starvation.get('grant_distribution', [])
            if grant_dist:
                lines.append("  Recent Grant Distribution:")
                for i, grants in enumerate(grant_dist):
                    if grants > 0 or i in starved_clients:  # Show clients with grants or starved clients
                        status = "⚠️ " if i in starved_clients else "✓ "
                        lines.append(f"    {status}Client {i}: {grants} grants")
            lines.append("")

        # Coverage Analysis
        coverage = stats.get('coverage_analysis', {})
        if coverage:
            lines.append("COVERAGE ANALYSIS:")
            lines.append("-" * 40)

            pattern_cov = coverage.get('pattern_coverage', {})
            if pattern_cov:
                lines.append("  Pattern Coverage:")
                lines.append(f"    Unique Patterns Seen:  {pattern_cov.get('unique_patterns_seen', 0)}")
                lines.append(f"    Single Client Patterns: {pattern_cov.get('single_client_patterns', 0)}")
                all_clients_seen = pattern_cov.get('all_clients_pattern_seen', False)
                lines.append(f"    All Clients Pattern:   {'✓ Seen' if all_clients_seen else '✗ Not seen'}")

            transition_cov = coverage.get('transition_coverage', {})
            if transition_cov:
                lines.append("  Transition Coverage:")
                lines.append(f"    Transitions Seen:      {transition_cov.get('transitions_seen', 0)}")
                lines.append(f"    Max Possible:          {transition_cov.get('max_possible_transitions', 0)}")
                lines.append(f"    Coverage Percentage:   {transition_cov.get('coverage_percent', 0):.1f}%")
            lines.append("")

        # Pattern Analysis
        pattern_analysis = stats.get('pattern_analysis', {})
        if pattern_analysis:
            lines.append("PATTERN ANALYSIS:")
            lines.append("-" * 40)

            grant_history = pattern_analysis.get('grant_history', [])
            if grant_history:
                history_str = " → ".join(map(str, grant_history))
                lines.append(f"  Recent Grant Sequence: {history_str}")

            violations = pattern_analysis.get('violations', [])
            if violations:
                lines.append(f"  Pattern Violations:    {len(violations)}")
                for i, violation in enumerate(violations[:3]):  # Show first 3
                    lines.append(f"    {i+1}. {violation}")
                if len(violations) > 3:
                    lines.append(f"    ... and {len(violations) - 3} more violations")
            else:
                lines.append(f"  Pattern Violations:    None ✓")
            lines.append("")

        # Monitoring Metadata
        metadata = stats.get('monitoring_metadata', {})
        if metadata:
            lines.append("MONITORING METADATA:")
            lines.append("-" * 40)
            lines.append(f"  Cycles Monitored:      {metadata.get('cycles_monitored', 0):,}")
            lines.append(f"  Debug Enabled:         {'✓' if metadata.get('debug_enabled', False) else '✗'}")
            lines.append(f"  Client Count:          {metadata.get('clients', 0)}")
            lines.append("")

        lines.append("=" * 80)

        # Print all lines to the monitor's log
        for line in lines:
            self.log.info(line)

    def print_static_period_stats(self):
        """Print static period statistics in human-readable format to the monitor's log"""
        static_stats = self.get_static_period_stats()

        lines = []
        lines.append("=" * 60)
        lines.append("STATIC PERIOD STATISTICS")
        lines.append("=" * 60)
        lines.append(f"Report Generated: {self.get_time_ns_str()}")
        lines.append("")

        if static_stats['total_grants'] == 0:
            lines.append("No grants recorded in static period.")
            lines.append("=" * 60)
        else:
            lines.append("PERIOD SUMMARY:")
            lines.append("-" * 30)
            lines.append(f"  Total Grants:          {static_stats['total_grants']:,}")
            lines.append(f"  Total Transactions:    {static_stats['total_transactions']:,}")
            lines.append(f"  Duration:              {static_stats['duration_ns']:,} ns")
            lines.append("")

            lines.append("CLIENT PERFORMANCE:")
            lines.append("-" * 30)
            lines.append(f"{'Client':<8} {'Grants':<10} {'Percentage':<12}")
            lines.append("-" * 35)

            for client_stats in static_stats['client_stats']:
                lines.append(f"{client_stats['client_id']:<8} "
                            f"{client_stats['grants']:<10} "
                            f"{client_stats['percentage']:<11.1f}%")

            lines.append("")
            lines.append("=" * 60)

        # Print all lines to the monitor's log
        for line in lines:
            self.log.info(line)

    def print_weight_compliance_analysis(self, expected_weights, requesting_clients=None):
        """Print weight compliance analysis in human-readable format to the monitor's log"""
        compliance = self.analyze_static_weight_compliance(expected_weights, requesting_clients)

        lines = []
        lines.append("=" * 70)
        lines.append("WEIGHT COMPLIANCE ANALYSIS")
        lines.append("=" * 70)
        lines.append(f"Analysis Generated: {self.get_time_ns_str()}")
        lines.append("")

        if compliance['status'] not in ['analyzed']:
            lines.append(f"Analysis Status: {compliance['status'].upper()}")
            if compliance['status'] == 'no_data':
                lines.append("No data available for weight compliance analysis.")
            elif compliance['status'] == 'no_expected_weights':
                lines.append("No expected weights provided for analysis.")
            elif compliance['status'] == 'no_requesting_clients':
                lines.append("No requesting clients with non-zero weights.")
            lines.append("=" * 70)
        else:
            # Show scope of analysis
            if requesting_clients is not None:
                lines.append(f"Analysis Scope: Requesting clients only: {sorted(requesting_clients)}")
            else:
                lines.append(f"Analysis Scope: All clients")
            lines.append("")

            # Overall compliance
            overall_compliance = compliance['overall_compliance']
            is_compliant = compliance['is_compliant']

            lines.append("OVERALL COMPLIANCE:")
            lines.append("-" * 35)
            status_icon = "✓" if is_compliant else "✗"
            lines.append(f"  Compliance Score:      {overall_compliance:.1%} {status_icon}")
            lines.append(f"  Threshold:             75.0% (for static periods)")
            lines.append(f"  Result:                {'PASS' if is_compliant else 'FAIL'}")
            lines.append("")

            # Per-client compliance
            lines.append("PER-CLIENT COMPLIANCE:")
            lines.append("-" * 35)
            lines.append(f"{'Client':<8} {'Weight':<8} {'Expected%':<11} {'Actual%':<10} {'Compliance':<12} {'Status':<8}")
            lines.append("-" * 65)

            for client_data in compliance['client_compliance']:
                client_id = client_data['client']
                expected_weight = client_data['expected_weight']
                expected_ratio = client_data['expected_ratio'] * 100
                actual_ratio = client_data['actual_ratio'] * 100
                compliance_score = client_data['compliance']

                # Determine status
                if compliance_score > 0.9:
                    status = "✓ GOOD"
                elif compliance_score > 0.75:
                    status = "~ OK"
                else:
                    status = "✗ POOR"

                lines.append(f"{client_id:<8} "
                            f"{expected_weight:<8} "
                            f"{expected_ratio:<10.1f}% "
                            f"{actual_ratio:<9.1f}% "
                            f"{compliance_score:<11.1%} "
                            f"{status:<8}")

            lines.append("")

            # Summary and recommendations
            lines.append("ANALYSIS SUMMARY:")
            lines.append("-" * 35)

            poor_performers = [c for c in compliance['client_compliance'] if c['compliance'] < 0.75]
            good_performers = [c for c in compliance['client_compliance'] if c['compliance'] > 0.9]

            if not poor_performers:
                lines.append("✓ All analyzed clients meeting weight compliance targets")
            else:
                lines.append(f"⚠️  {len(poor_performers)} client(s) with poor weight compliance:")
                for client_data in poor_performers:
                    lines.append(f"   - Client {client_data['client']}: {client_data['compliance']:.1%} compliance")

            if good_performers:
                lines.append(f"✓ {len(good_performers)} client(s) with excellent compliance")

            lines.append("")
            lines.append("=" * 70)

        # Print all lines to the monitor's log
        for line in lines:
            self.log.info(line)

    # =======================================================================
    # MONITORING COROUTINES
    # =======================================================================

    async def _monitor_requests(self):
        """Monitor request signals and record new request events"""
        if not self.monitoring_enabled:
            return

        prev_req = 0

        while True:
            await RisingEdge(self.clock)

            try:
                # Sample requests on rising edge for stability
                if self.req_signal.value.is_resolvable:
                    req_vec = int(self.req_signal.value)

                    # Detect new requests (rising edges)
                    new_requests = req_vec & ~prev_req
                    if new_requests:
                        self.active_request_vector |= new_requests
                        current_time = get_sim_time('ns')

                        # Record request time for each new request
                        for i in range(self.clients):
                            if new_requests & (1 << i):
                                self.pending_requests[i] = current_time
                                if self.debug_enabled:
                                    self.log.debug(f"ArbiterMonitor({self.title}): New request from client {i} @ {current_time}ns")

                    prev_req = req_vec

            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"ArbiterMonitor({self.title}): Error monitoring requests: {e}{self.get_time_ns_str()}")

    async def _monitor_grants(self):
        """Monitor grant signals and create transaction records"""
        if not self.monitoring_enabled:
            return

        while True:
            # Wait for rising edge of clock for stable sampling
            await RisingEdge(self.clock)

            try:
                # Check if grant_valid is actually asserted first
                if not self.gnt_valid_signal.value.is_resolvable:
                    continue

                gnt_valid = int(self.gnt_valid_signal.value)
                if gnt_valid != 1:
                    continue  # No valid grant, skip

                # Now safely read grant signals
                if not self.gnt_signal.value.is_resolvable or not self.gnt_id_signal.value.is_resolvable:
                    if self.debug_enabled:
                        self.log.warning(f"ArbiterMonitor({self.title}): Grant signals not resolvable{self.get_time_ns_str()}")
                    continue

                gnt_vec = int(self.gnt_signal.value)
                gnt_id = int(self.gnt_id_signal.value)
                current_time = get_sim_time('ns')

                # Verify grant vector is not zero
                if gnt_vec == 0:
                    if self.debug_enabled:
                        self.log.warning(f"ArbiterMonitor({self.title}): Grant valid asserted but grant vector is 0{self.get_time_ns_str()}")
                    continue

                # Verify grant ID is within valid range
                if gnt_id >= self.clients:
                    self.log.warning(f"ArbiterMonitor({self.title}): Invalid grant ID {gnt_id} (max {self.clients-1}){self.get_time_ns_str()}")
                    continue

                # Verify that grant ID matches the set bit in grant vector
                expected_gnt_vec = (1 << gnt_id)
                if gnt_vec != expected_gnt_vec:
                    self.log.warning(f"ArbiterMonitor({self.title}): Grant ID ({gnt_id}) doesn't match grant vector (0x{gnt_vec:x}, expected 0x{expected_gnt_vec:x}){self.get_time_ns_str()}")

                # Calculate wait time
                request_time = self.pending_requests.get(gnt_id, current_time)
                wait_time = current_time - request_time
                cycle_count = int(wait_time / self.clock_period_ns) if self.clock_period_ns > 0 else 0

                # Create transaction record
                metadata = {'blocked': self.blocked}

                if self.max_thresh_signal and self.is_weighted:
                    try:
                        if self.max_thresh_signal.value.is_resolvable:
                            metadata['max_levelsold'] = int(self.max_thresh_signal.value)
                    except:
                        pass  # Ignore threshold read errors

                transaction = ArbiterTransaction(
                    req_vector=self.active_request_vector,
                    gnt_vector=gnt_vec,
                    gnt_id=gnt_id,
                    cycle_count=cycle_count,
                    timestamp=current_time,
                    weights=None,
                    metadata=metadata
                )

                # Update transaction tracking
                self.transactions.append(transaction)
                self.total_transactions += 1

                # Clear granted request from active requests
                self.active_request_vector &= ~gnt_vec
                if gnt_id in self.pending_requests:
                    del self.pending_requests[gnt_id]

                # Update statistics
                self.stats['total_grants'] += 1
                self.stats['grants_per_client'][gnt_id] += 1
                self.stats['wait_time_per_client'][gnt_id] += wait_time
                self.stats['total_cycles'] += cycle_count
                self.stats['grant_sequences'].append(gnt_id)

                # Keep only recent sequences for pattern analysis
                if len(self.stats['grant_sequences']) > 100:
                    self.stats['grant_sequences'] = self.stats['grant_sequences'][-50:]

                if self.stats['total_grants'] > 0:
                    self.stats['avg_wait_time'] = self.stats['total_cycles'] / self.stats['total_grants']

                # Update integrated pattern tracking
                self._update_pattern_tracking(transaction)

                if self.debug_enabled:
                    self.log.debug(f"ArbiterMonitor({self.title}): Grant to client {gnt_id} after {wait_time}ns wait ({cycle_count} cycles) @ {current_time}ns")

                # Call the transaction callback if registered
                if self.transaction_callback:
                    try:
                        self.transaction_callback(transaction)
                    except Exception as e:
                        self.log.error(f"ArbiterMonitor({self.title}): Error in transaction callback: {e}{self.get_time_ns_str()}")

            except Exception as e:
                self.log.error(f"ArbiterMonitor({self.title}): Error monitoring grants: {e}{self.get_time_ns_str()}")

    async def _monitor_reset(self):
        """Monitor reset signal and handle reset events"""
        while True:
            await FallingEdge(self.reset_n)

            # Reset detected
            current_time = get_sim_time('ns')
            self.log.info(f"ArbiterMonitor({self.title}): Reset detected @ {current_time}ns")

            # Clear state
            self.pending_requests.clear()
            self.active_request_vector = 0
            self.blocked = False

            # Reset pattern tracking
            self.reset_pattern_tracking()

            # Call reset callback if registered
            if self.reset_callback:
                try:
                    self.reset_callback()
                except Exception as e:
                    self.log.error(f"ArbiterMonitor({self.title}): Error in reset callback: {e}{self.get_time_ns_str()}")

            # Wait for reset to deassert
            await RisingEdge(self.reset_n)
            release_time = get_sim_time('ns')
            self.log.info(f"ArbiterMonitor({self.title}): Reset released @ {release_time}ns")

    async def _monitor_block(self):
        """Monitor block arbitration signal"""
        if not self.block_arb_signal:
            return

        while True:
            await Edge(self.block_arb_signal)
            try:
                if self.block_arb_signal.value.is_resolvable:
                    self.blocked = bool(int(self.block_arb_signal.value))
                    if self.debug_enabled:
                        self.log.debug(f"ArbiterMonitor({self.title}): Arbitration {'blocked' if self.blocked else 'unblocked'}{self.get_time_ns_str()}")
            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"ArbiterMonitor({self.title}): Error monitoring block signal: {e}{self.get_time_ns_str()}")

    async def _monitor_thresholds(self):
        """Monitor threshold changes for weighted arbiters"""
        if not (self.max_thresh_signal and self.is_weighted):
            return

        prev_thresh = None
        while True:
            await Edge(self.max_thresh_signal)
            try:
                if self.max_thresh_signal.value.is_resolvable:
                    new_thresh = int(self.max_thresh_signal.value)

                    if new_thresh != prev_thresh and prev_thresh is not None:
                        if self.debug_enabled:
                            self.log.debug(f"ArbiterMonitor({self.title}): Threshold changed from 0x{prev_thresh:x} to 0x{new_thresh:x}{self.get_time_ns_str()}")

                    prev_thresh = new_thresh
            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"ArbiterMonitor({self.title}): Error monitoring thresholds: {e}{self.get_time_ns_str()}")


class RoundRobinArbiterMonitor(ArbiterMonitor):
    """Monitor specifically tailored for Round Robin Arbiters."""

    def __init__(self, dut, title, clock, reset_n,
                req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                gnt_ack_signal=None, block_arb_signal=None, clients=None,
                log=None, clock_period_ns=10):
        """Initialize a Round Robin Arbiter Monitor"""

        super().__init__(
            dut=dut,
            title=title,
            clock=clock,
            reset_n=reset_n,
            req_signal=req_signal,
            gnt_valid_signal=gnt_valid_signal,
            gnt_signal=gnt_signal,
            gnt_id_signal=gnt_id_signal,
            gnt_ack_signal=gnt_ack_signal,
            block_arb_signal=block_arb_signal,
            is_weighted=False,
            clients=clients,
            log=log,
            clock_period_ns=clock_period_ns
        )

        # Round-robin specific tracking
        self.rr_violations = []

    def analyze_round_robin_pattern(self):
        """Analyze if the grant pattern follows round-robin behavior"""
        if len(self.grant_history) < self.clients:
            return {'status': 'insufficient_data', 'violations': len(self.rr_violations)}

        # Calculate round-robin efficiency
        total_transitions = len(self.grant_history) - 1
        sequential_transitions = 0

        for i in range(len(self.grant_history) - 1):
            from_client = self.grant_history[i]
            to_client = self.grant_history[i + 1]
            expected_next = (from_client + 1) % self.clients

            if to_client == expected_next:
                sequential_transitions += 1

        rr_efficiency = sequential_transitions / total_transitions if total_transitions > 0 else 0

        # Get starvation analysis
        starvation_analysis = self.check_starvation()

        return {
            'status': 'analyzed',
            'total_grants': len(self.grant_history),
            'violations': len(self.rr_violations),
            'rr_efficiency': rr_efficiency,
            'pattern_compliance': 1.0 - (len(self.rr_violations) / len(self.grant_history)) if self.grant_history else 0.0,
            'recent_sequence': self.grant_history[-min(20, len(self.grant_history)):],
            'violation_details': self.rr_violations[-5:],  # Last 5 violations
            'starvation_analysis': starvation_analysis,
            'transition_analysis': {
                'unique_transitions': len(self.transitions_seen),
                'max_possible': self.clients * self.clients,
                'coverage_percent': (len(self.transitions_seen) / (self.clients * self.clients)) * 100
            }
        }

    def reset_pattern_tracking(self):
        """Reset round-robin specific tracking"""
        super().reset_pattern_tracking()
        self.rr_violations.clear()


class WeightedRoundRobinArbiterMonitor(ArbiterMonitor):
    """Monitor specifically tailored for Weighted Round Robin Arbiters."""

    def __init__(self, dut, title, clock, reset_n,
                req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                gnt_ack_signal=None, block_arb_signal=None,
                max_thresh_signal=None, clients=None, log=None,
                clock_period_ns=10):
        """Initialize a Weighted Round Robin Arbiter Monitor"""

        super().__init__(
            dut=dut,
            title=title,
            clock=clock,
            reset_n=reset_n,
            req_signal=req_signal,
            gnt_valid_signal=gnt_valid_signal,
            gnt_signal=gnt_signal,
            gnt_id_signal=gnt_id_signal,
            gnt_ack_signal=gnt_ack_signal,
            block_arb_signal=block_arb_signal,
            max_thresh_signal=max_thresh_signal,
            is_weighted=True,
            clients=clients,
            log=log,
            clock_period_ns=clock_period_ns
        )

        # Weighted round-robin specific tracking
        self.client_consecutive_grants = [0] * self.clients
        self.observed_weights = [0] * self.clients
        self.weight_observations = []

    def analyze_weight_compliance(self, expected_weights=None):
        """Analyze if grant distribution matches expected weights"""
        if not expected_weights:
            return {'status': 'no_expected_weights'}

        if self.stats['total_grants'] < sum(expected_weights) * 2:
            return {'status': 'insufficient_data'}

        total_grants = self.stats['total_grants']
        total_expected_weight = sum(expected_weights)

        compliance_data = []
        for i in range(self.clients):
            actual_grants = self.stats['grants_per_client'][i]
            expected_ratio = expected_weights[i] / total_expected_weight
            actual_ratio = actual_grants / total_grants

            compliance_data.append({
                'client': i,
                'expected_weight': expected_weights[i],
                'expected_ratio': expected_ratio,
                'actual_grants': actual_grants,
                'actual_ratio': actual_ratio,
                'compliance': 1.0 - abs(expected_ratio - actual_ratio)
            })

        avg_compliance = sum(c['compliance'] for c in compliance_data) / len(compliance_data)

        return {
            'status': 'analyzed',
            'overall_compliance': avg_compliance,
            'client_compliance': compliance_data,
            'is_compliant': avg_compliance > 0.8  # 80% compliance threshold
        }
