"""
Enhanced Generic Arbiter Monitor Component for Verification

This module provides improved ArbiterMonitor classes for observing various types of arbiter interfaces
including round-robin and weighted round-robin arbiters.

Key improvements:
- Better signal sampling timing
- Proper grant_valid checking
- Improved signal resolution handling
- More robust transaction tracking
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
    Enhanced Generic Arbiter Monitor component that observes arbiter transactions.

    This class provides:
    - Monitoring of request and grant signals with proper timing
    - Transaction tracking with timing information
    - Support for both round-robin and weighted round-robin arbiters
    - Configurable callbacks for events
    - Improved signal sampling and validation
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

        # Create logger if not provided
        self.log = log or SimLog(f"cocotb.{dut._name}.{title}")

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
                self.log.warning("Could not determine number of clients from req_signal width, using default of 4")
                self.clients = 4  # Default value
        else:
            self.clients = int(clients)

        # Transaction tracking
        self.transactions = deque(maxlen=1000)  # Limit memory usage
        self.pending_requests = {}  # Maps client index to request time
        self.total_transactions = 0
        self.active_request_vector = 0
        self.blocked = False

        # Counters and statistics
        self.stats = {
            'total_grants': 0,
            'grants_per_client': [0] * self.clients,
            'avg_wait_time': 0,
            'wait_time_per_client': [0] * self.clients,
            'total_cycles': 0,
            'grant_sequences': [],  # Track grant sequences for pattern analysis
        }

        # Callbacks
        self.transaction_callback = None
        self.reset_callback = None

        # Control flags
        self.monitoring_enabled = True
        self.debug_enabled = False

        self.log.info(f"ArbiterMonitor '{title}' initialized with {self.clients} clients, "
                     f"clock period {self.clock_period_ns}ns")

    def enable_debug(self, enable=True):
        """Enable or disable debug logging"""
        self.debug_enabled = enable
        self.log.info(f"Debug logging {'enabled' if enable else 'disabled'}")

    def enable_monitoring(self, enable=True):
        """Enable or disable monitoring"""
        self.monitoring_enabled = enable
        self.log.info(f"Monitoring {'enabled' if enable else 'disabled'}")

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

        self.log.info("All monitoring threads started")

    def add_transaction_callback(self, callback):
        """Register a callback function for completed transactions."""
        self.transaction_callback = callback
        if self.debug_enabled:
            self.log.debug(f"Added transaction callback: {callback.__name__}")

    def add_reset_callback(self, callback):
        """Register a callback function for reset events."""
        self.reset_callback = callback
        if self.debug_enabled:
            self.log.debug(f"Added reset callback: {callback.__name__}")

    def get_transaction_count(self):
        """Return the total number of observed transactions"""
        return self.total_transactions

    def get_client_stats(self, client_id):
        """Get statistics for a specific client."""
        if client_id >= self.clients:
            self.log.error(f"Invalid client ID: {client_id}, max is {self.clients-1}")
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
                                    self.log.debug(f"New request from client {i} at {current_time}ns")

                    prev_req = req_vec

            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"Error monitoring requests: {e}")

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
                        self.log.warning(f"Grant signals not resolvable at {get_sim_time('ns')}ns")
                    continue

                gnt_vec = int(self.gnt_signal.value)
                gnt_id = int(self.gnt_id_signal.value)
                current_time = get_sim_time('ns')

                # Verify grant vector is not zero (this was the main issue)
                if gnt_vec == 0:
                    if self.debug_enabled:
                        self.log.warning(f"Grant valid asserted but grant vector is 0 at {current_time}ns")
                    continue

                # Verify grant ID is within valid range
                if gnt_id >= self.clients:
                    self.log.warning(f"Invalid grant ID {gnt_id} (max {self.clients-1}) at {current_time}ns")
                    continue

                # Verify that grant ID matches the set bit in grant vector
                expected_gnt_vec = (1 << gnt_id)
                if gnt_vec != expected_gnt_vec:
                    self.log.warning(f"Grant ID ({gnt_id}) doesn't match grant vector (0x{gnt_vec:x}, expected 0x{expected_gnt_vec:x}) at {current_time}ns")

                # Calculate wait time
                request_time = self.pending_requests.get(gnt_id, current_time)
                wait_time = current_time - request_time
                cycle_count = int(wait_time / self.clock_period_ns) if self.clock_period_ns > 0 else 0

                # Create transaction record
                metadata = {'blocked': self.blocked}

                if self.max_thresh_signal and self.is_weighted:
                    try:
                        if self.max_thresh_signal.value.is_resolvable:
                            metadata['max_threshold'] = int(self.max_thresh_signal.value)
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

                if self.debug_enabled:
                    self.log.debug(f"Grant to client {gnt_id} after {wait_time}ns wait ({cycle_count} cycles) at {current_time}ns")

                # Call the transaction callback if registered
                if self.transaction_callback:
                    try:
                        self.transaction_callback(transaction)
                    except Exception as e:
                        self.log.error(f"Error in transaction callback: {e}")

            except Exception as e:
                self.log.error(f"Error monitoring grants: {e}")

    async def _monitor_reset(self):
        """Monitor reset signal and handle reset events"""
        while True:
            await FallingEdge(self.reset_n)

            # Reset detected
            current_time = get_sim_time('ns')
            self.log.info(f"Reset detected at {current_time}ns")

            # Clear state
            self.pending_requests.clear()
            self.active_request_vector = 0
            self.blocked = False

            # Call reset callback if registered
            if self.reset_callback:
                try:
                    self.reset_callback()
                except Exception as e:
                    self.log.error(f"Error in reset callback: {e}")

            # Wait for reset to deassert
            await RisingEdge(self.reset_n)
            release_time = get_sim_time('ns')
            self.log.info(f"Reset released at {release_time}ns")

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
                        self.log.debug(f"Arbitration {'blocked' if self.blocked else 'unblocked'} at {get_sim_time('ns')}ns")
            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"Error monitoring block signal: {e}")

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
                            self.log.debug(f"Threshold changed from 0x{prev_thresh:x} to 0x{new_thresh:x} at {get_sim_time('ns')}ns")

                    prev_thresh = new_thresh
            except Exception as e:
                if self.debug_enabled:
                    self.log.warning(f"Error monitoring thresholds: {e}")


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
        self.expected_next_priority = 0
        self.priority_violations = 0

    def analyze_round_robin_pattern(self):
        """Analyze if the grant pattern follows round-robin behavior"""
        if len(self.stats['grant_sequences']) < self.clients * 2:
            return {'status': 'insufficient_data', 'violations': 0}

        sequences = self.stats['grant_sequences'][-self.clients * 3:]  # Look at recent grants

        violations = 0
        expected_next = None

        for i, gnt_id in enumerate(sequences):
            if expected_next is not None:
                # Check if this grant follows round-robin order
                if gnt_id != expected_next:
                    violations += 1

            # Calculate next expected grant (wrap around)
            expected_next = (gnt_id + 1) % self.clients

        return {
            'status': 'valid_round_robin' if violations == 0 else 'violations_detected',
            'violations': violations,
            'recent_sequence': sequences[-min(20, len(sequences)):],
            'pattern_compliance': 1.0 - (violations / len(sequences)) if sequences else 0.0
        }


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
