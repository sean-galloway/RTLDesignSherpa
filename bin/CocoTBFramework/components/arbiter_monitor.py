"""
Generic Arbiter Monitor Component for Verification

This module provides the ArbiterMonitor class for observing various types of arbiter interfaces
including round-robin and weighted round-robin arbiters.
"""

import cocotb
from collections import deque, namedtuple
from cocotb.triggers import FallingEdge, Edge, Timer
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
    - Monitoring of request and grant signals
    - Transaction tracking with timing information
    - Support for both round-robin and weighted round-robin arbiters
    - Configurable callbacks for events
    """

    def __init__(self, dut, title, clock, reset_n, req_signal, gnt_valid_signal, gnt_signal,
                    gnt_id_signal, gnt_ack_signal=None, block_arb_signal=None,
                    max_thresh_signal=None, is_weighted=False, clients=None, log=None,
                    clock_period_ns=(10, "ns")):
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
            clock_period: Tuple of (value, unit) for clock period, e.g. (10, "ns")
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
                self.clients = len(self.req_signal.value.binstr)
            except AttributeError:
                self.log.error("Could not determine number of clients from req_signal width")
                self.clients = 4  # Default value
        else:
            self.clients = int(clients)

        # Transaction tracking
        self.transactions = deque()
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
        }

        # Callbacks
        self.transaction_callback = None
        self.reset_callback = None

        # Add monitor coroutines to scheduler
        self._req_monitor_thread = cocotb.start_soon(self._monitor_requests())
        self._gnt_monitor_thread = cocotb.start_soon(self._monitor_grants())
        self._reset_monitor_thread = cocotb.start_soon(self._monitor_reset())

        if self.block_arb_signal:
            self._block_monitor_thread = cocotb.start_soon(self._monitor_block())

        if self.max_thresh_signal and self.is_weighted:
            self._thresh_monitor_thread = cocotb.start_soon(self._monitor_thresholds())

        self.log.info(f"ArbiterMonitor '{title}' initialized with {self.clients} clients, clock period_ns {self.clock_period_ns}")

    def add_transaction_callback(self, callback):
        """
        Register a callback function for completed transactions.

        Args:
            callback: Function to call with each new transaction
        """
        self.transaction_callback = callback
        self.log.debug(f"Added transaction callback: {callback.__name__}")

    def add_reset_callback(self, callback):
        """
        Register a callback function for reset events.

        Args:
            callback: Function to call when reset is detected
        """
        self.reset_callback = callback
        self.log.debug(f"Added reset callback: {callback.__name__}")

    def get_transaction_count(self):
        """Return the total number of observed transactions"""
        return self.total_transactions

    def get_client_stats(self, client_id):
        """
        Get statistics for a specific client.

        Args:
            client_id: ID of the client to get stats for

        Returns:
            Dictionary with client-specific statistics
        """
        if client_id >= self.clients:
            self.log.error(f"Invalid client ID: {client_id}, max is {self.clients-1}")
            return None

        return {
            'grants': self.stats['grants_per_client'][client_id],
            'avg_wait_time': (self.stats['wait_time_per_client'][client_id] /
                                self.stats['grants_per_client'][client_id])
                                if self.stats['grants_per_client'][client_id] > 0 else 0
        }

    def get_fairness_index(self):
        """
        Calculate Jain's fairness index for the arbiter.

        Returns:
            Fairness index between 0 and 1 (1 is perfectly fair)
        """
        grants = self.stats['grants_per_client']
        if sum(grants) == 0:
            return 1.0  # No grants yet, assume fair

        n = len(grants)
        squared_sum = sum(grants) ** 2
        sum_of_squares = sum(x ** 2 for x in grants)

        return 1.0 if sum_of_squares == 0 else squared_sum / (n * sum_of_squares)

    async def _monitor_requests(self):
        """Monitor request signals and record new request events"""
        prev_req = 0

        while True:
            await FallingEdge(self.clock)

            # Get current request vector
            if self.req_signal.value.is_resolvable:
                req_vec = self.req_signal.value.integer

                if new_requests := req_vec & ~prev_req:
                    self.active_request_vector |= new_requests
                    current_time = get_sim_time('ns')

                    # Record request time for each new request
                    for i in range(self.clients):
                        if new_requests & (1 << i):
                            self.pending_requests[i] = current_time
                            self.log.debug(f"New request from client {i} at {current_time}ns")

                prev_req = req_vec

# begin


    async def _monitor_grants(self):
        """Monitor grant signals and create transaction records"""
        while True:
            # Wait for grant valid assertion
            await FallingEdge(self.clock)

            # Capture grant information
            if self.gnt_signal.value.is_resolvable:
                gnt_vec = self.gnt_signal.value.integer
                gnt_id = self.gnt_id_signal.value.integer
                current_time = get_sim_time('ns')

                # Verify grant validity
                if gnt_vec == 0:
                    self.log.warning(f"Grant valid asserted but grant vector is 0 at {current_time}ns")
                    continue

                # Calculate which bit in gnt_vec is set
                gnt_bit = 0
                temp_vec = gnt_vec
                while temp_vec > 1:
                    temp_vec >>= 1
                    gnt_bit += 1

                # Verify that grant ID matches the set bit
                if gnt_bit != gnt_id:
                    self.log.warning(f"Grant ID ({gnt_id}) doesn't match grant vector bit ({gnt_bit}) at {current_time}ns")

                # Calculate wait time
                request_time = self.pending_requests.get(gnt_id, current_time)
                wait_time = current_time - request_time

                # Calculate cycle count using the provided clock period
                cycle_count = int(wait_time / self.clock_period_ns)

                # Create transaction record
                metadata = {}
                if self.block_arb_signal:
                    metadata['blocked'] = bool(self.blocked)

                if self.max_thresh_signal and self.is_weighted:
                    max_thresh_val = self.max_thresh_signal.value.integer
                    metadata['max_threshold'] = max_thresh_val

                transaction = ArbiterTransaction(
                    req_vector=self.active_request_vector,
                    gnt_vector=gnt_vec,
                    gnt_id=gnt_id,
                    cycle_count=cycle_count,
                    timestamp=current_time,
                    weights=None,  # Could extract weights for weighted arbiters
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
                self.stats['avg_wait_time'] = (
                    self.stats['total_cycles'] / self.stats['total_grants']
                )

                self.log.debug(f"Grant to client {gnt_id} after {wait_time}ns wait at {current_time}ns")

                # If grant ack is being used, wait for the ack
                if self.gnt_ack_signal:
                    # Check if ack is immediate or needs to be waited for
                    ack_value = self.gnt_ack_signal.value.integer
                    if (ack_value & gnt_vec) == 0:
                        # Wait for the specific bit in ack signal
                        await self._wait_for_ack_bit(gnt_id)
                        self.log.debug(f"Received ack from client {gnt_id}")

                # Call the transaction callback if registered
                if self.transaction_callback:
                    self.transaction_callback(transaction)


# End

    async def _wait_for_ack_bit(self, bit_position):
        """Wait for a specific bit in the ack signal to be asserted"""
        mask = 1 << bit_position

        while True:
            await Edge(self.gnt_ack_signal)
            if self.gnt_ack_signal.value.integer & mask:
                break
            # Use a fraction of the clock period to avoid tight loop
            await Timer(self.clock_period_ns / 10, units='ns')

    async def _monitor_reset(self):
        """Monitor reset signal and handle reset events"""
        while True:
            await FallingEdge(self.reset_n)

            # Reset detected
            self.log.info(f"Reset detected at {get_sim_time('ns')}ns")

            # Clear state
            self.pending_requests.clear()
            self.active_request_vector = 0

            # Call reset callback if registered
            if self.reset_callback:
                self.reset_callback()

            # Wait for reset to deassert
            await FallingEdge(self.clock)
            self.log.info(f"Reset released at {get_sim_time('ns')}ns")

    async def _monitor_block(self):
        """Monitor block arbitration signal"""
        if not self.block_arb_signal:
            return

        while True:
            await Edge(self.block_arb_signal)
            self.blocked = bool(self.block_arb_signal.value.integer)
            self.log.debug(f"Arbitration {'blocked' if self.blocked else 'unblocked'} at {get_sim_time('ns')}ns")

    async def _monitor_thresholds(self):
        """Monitor threshold changes for weighted arbiters"""
        if not (self.max_thresh_signal and self.is_weighted):
            return

        prev_thresh = 0
        while True:
            await Edge(self.max_thresh_signal)
            new_thresh = self.max_thresh_signal.value

            if new_thresh != prev_thresh:
                self.log.debug(f"Threshold changed from {prev_thresh} to {new_thresh} at {get_sim_time('ns')}ns")
                prev_thresh = new_thresh


class RoundRobinArbiterMonitor(ArbiterMonitor):
    """
    Monitor specifically tailored for Round Robin Arbiters.
    """

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
        self.last_priority = None
        self._priority_thread = cocotb.start_soon(self._track_priority())

    async def _track_priority(self):
        """
        Track the round-robin priority over time.
        This infers the internal mask state by observing grant patterns.
        """
        while True:
            await FallingEdge(self.clock)

            # If we have transactions, analyze the pattern
            if len(self.transactions) >= 2:
                last_tx = self.transactions[-1]
                prev_tx = self.transactions[-2]

                # If both transactions had the same request vector but different grants,
                # we can infer the priority changed
                if (last_tx.req_vector == prev_tx.req_vector and
                    last_tx.gnt_id != prev_tx.gnt_id):

                    self.last_priority = prev_tx.gnt_id
                    self.log.debug(f"Inferred priority change: {self.last_priority} at {get_sim_time('ns')}ns")

    def get_priority_changes(self):
        """Get statistics about priority changes"""
        if len(self.transactions) < 2:
            return {'changes': 0, 'pattern': 'unknown'}

        # Analyze the latest transactions to detect pattern
        changes = 0
        pattern = []

        for i in range(1, len(self.transactions)):
            prev = self.transactions[i-1]
            curr = self.transactions[i]

            if prev.gnt_id != curr.gnt_id:
                changes += 1
                pattern.append((prev.gnt_id, curr.gnt_id))

        # Determine if it's a standard round-robin pattern
        is_rr = True
        if len(pattern) >= self.clients:
            seen_clients = {gnt_id for _, gnt_id in pattern[-self.clients:]}
            is_rr = len(seen_clients) == self.clients

        return {
            'changes': changes,
            'pattern': 'round-robin' if is_rr else 'custom',
            'last_priority': self.last_priority
        }


class WeightedRoundRobinArbiterMonitor(ArbiterMonitor):
    """
    Monitor specifically tailored for Weighted Round Robin Arbiters.
    """

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
        self.inferred_weights = [1] * self.clients
        self.client_consecutive_grants = [0] * self.clients
        self._weights_thread = cocotb.start_soon(self._infer_weights())

    async def _infer_weights(self):
        """
        Infer the weights by monitoring consecutive grants to each client.
        This is a heuristic approach that may not be exact.
        """
        last_granted_client = None

        while True:
            await FallingEdge(self.clock)

            if self.gnt_id_signal.value.is_resolvable:
                gnt_id = self.gnt_id_signal.value.integer

                # If same client is granted again, increment consecutive count
                if gnt_id == last_granted_client:
                    self.client_consecutive_grants[gnt_id] += 1
                else:
                    # New client granted, update inferred weight for previous client
                    if last_granted_client is not None:
                        count = self.client_consecutive_grants[last_granted_client]
                        if count > 0:
                            self.inferred_weights[last_granted_client] = max(count, self.inferred_weights[last_granted_client])

                    # Reset consecutive counter for new client
                    self.client_consecutive_grants[gnt_id] = 1
                    last_granted_client = gnt_id

    def get_inferred_weights(self):
        """Get the inferred weights for each client"""
        return self.inferred_weights

    def get_weight_distribution(self):
        """Get statistics about the weight distribution"""
        if sum(self.stats['grants_per_client']) == 0:
            return {'distribution': 'unknown', 'ratio': []}

        # Calculate the observed grant ratio
        total_grants = sum(self.stats['grants_per_client'])
        grant_ratios = [count/total_grants for count in self.stats['grants_per_client']]

        # Calculate expected ratios based on inferred weights
        total_weight = sum(self.inferred_weights)
        expected_ratios = [w/total_weight for w in self.inferred_weights]

        # Calculate the difference between observed and expected
        ratio_diff = [abs(grant_ratios[i] - expected_ratios[i]) for i in range(self.clients)]
        avg_diff = sum(ratio_diff) / len(ratio_diff)

        return {
            'distribution': 'matching_weights' if avg_diff < 0.1 else 'non_matching',
            'observed_ratios': grant_ratios,
            'expected_ratios': expected_ratios,
            'difference': avg_diff
        }
