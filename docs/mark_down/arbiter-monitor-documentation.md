# Arbiter Monitor Documentation

## Overview
The Arbiter Monitor module provides components for observing and analyzing the behavior of arbiters in digital designs. It includes:

1. `ArbiterMonitor`: Core monitoring component for general arbiters
2. `RoundRobinArbiterMonitor`: Specialized monitor for round-robin arbiters
3. `WeightedRoundRobinArbiterMonitor`: Specialized monitor for weighted round-robin arbiters

These components allow verification engineers to analyze arbiter behavior, verify fairness, and detect problems in arbitration schemes.

## Key Features
- Track request and grant signals in real-time
- Calculate arbitration statistics (grants per client, wait times)
- Calculate fairness metrics
- Support for various arbiter types (standard, round-robin, weighted)
- Callback mechanisms for integration with other components
- Automatic reset detection and handling

## ArbiterTransaction

A named tuple that stores information about observed arbiter transactions:

```python
ArbiterTransaction = namedtuple('ArbiterTransaction', [
    'req_vector',      # Request vector from clients
    'gnt_vector',      # Grant vector indicating which client was selected
    'gnt_id',          # ID of the granted client
    'cycle_count',     # Number of cycles between request and grant
    'timestamp',       # Timestamp when grant was issued
    'weights',         # Optional weights (for weighted arbiters)
    'metadata'         # Dictionary for any additional metadata
])
```

This structure provides a complete snapshot of an arbitration event, including:
- Which clients requested service (`req_vector`)
- Which client received the grant (`gnt_vector` and `gnt_id`)
- How long the client waited (`cycle_count`)
- When the grant occurred (`timestamp`)
- Additional context information (`metadata`)

## ArbiterMonitor Class

### Purpose
The `ArbiterMonitor` provides a generic framework for monitoring arbiter interfaces, observing requests and grants, and calculating statistics about arbiter behavior.

### Class Definition
```python
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
```

### Key Methods

#### Callback Registration
```python
def add_transaction_callback(self, callback):
    """Register a callback function for completed transactions."""
```
Registers a function to be called whenever a transaction is completed.

```python
def add_reset_callback(self, callback):
    """Register a callback function for reset events."""
```
Registers a function to be called when reset is detected.

#### Statistics and Metrics
```python
def get_transaction_count(self):
    """Return the total number of observed transactions"""
```
Returns the total number of transactions observed.

```python
def get_client_stats(self, client_id):
    """Get statistics for a specific client."""
```
Returns statistics for a specific client, including grants and average wait time.

```python
def get_fairness_index(self):
    """Calculate Jain's fairness index for the arbiter."""
```
Calculates the Jain's fairness index, a measure of how fairly resources are distributed among clients.

#### Internal Monitoring
The class includes several internal monitoring methods that run as concurrent coroutines:

```python
async def _monitor_requests(self):
    """Monitor request signals and record new request events"""
```

```python
async def _monitor_grants(self):
    """Monitor grant signals and create transaction records"""
```

```python
async def _monitor_reset(self):
    """Monitor reset signal and handle reset events"""
```

```python
async def _wait_for_ack_bit(self, bit_position):
    """Wait for a specific bit in the ack signal to be asserted"""
```

## RoundRobinArbiterMonitor Class

### Purpose
The `RoundRobinArbiterMonitor` extends the base `ArbiterMonitor` with specialized functionality for round-robin arbiters, focusing on priority tracking and pattern detection.

### Class Definition
```python
class RoundRobinArbiterMonitor(ArbiterMonitor):
    """
    Monitor specifically tailored for Round Robin Arbiters.
    """

    def __init__(self, dut, title, clock, reset_n,
                    req_signal, gnt_valid_signal, gnt_signal, gnt_id_signal,
                    gnt_ack_signal=None, block_arb_signal=None, clients=None,
                    log=None, clock_period_ns=10):
        """Initialize a Round Robin Arbiter Monitor"""
```

### Key Features
- Tracks priority changes over time
- Infers the internal priority mask by observing grant patterns
- Analyzes if the arbiter follows a standard round-robin pattern

### Key Methods
```python
async def _track_priority(self):
    """
    Track the round-robin priority over time.
    This infers the internal mask state by observing grant patterns.
    """
```
Analyzes transaction patterns to infer the round-robin priority.

```python
def get_priority_changes(self):
    """Get statistics about priority changes"""
```
Returns detailed statistics about how priority has changed over time, including the pattern of changes and whether it follows a standard round-robin scheme.

## WeightedRoundRobinArbiterMonitor Class

### Purpose
The `WeightedRoundRobinArbiterMonitor` extends the base `ArbiterMonitor` with specialized functionality for weighted round-robin arbiters, focusing on inferring weights and analyzing distribution patterns.

### Class Definition
```python
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
```

### Key Features
- Infers client weights by analyzing consecutive grants
- Monitors threshold changes for weighted arbiters
- Calculates expected versus observed grant distributions
- Validates weighted fairness

### Key Methods
```python
async def _infer_weights(self):
    """
    Infer the weights by monitoring consecutive grants to each client.
    This is a heuristic approach that may not be exact.
    """
```
Analyzes consecutive grants to infer the weight assigned to each client.

```python
def get_inferred_weights(self):
    """Get the inferred weights for each client"""
```
Returns the inferred weights for each client.

```python
def get_weight_distribution(self):
    """Get statistics about the weight distribution"""
```
Returns detailed statistics about the observed weight distribution, comparing it with the expected distribution based on inferred weights.

## Usage Examples

### Basic Arbiter Monitoring
```python
# Create basic arbiter monitor
arb_mon = ArbiterMonitor(
    dut=dut,
    title="Main_Arbiter",
    clock=dut.clk,
    reset_n=dut.rst_n,
    req_signal=dut.req,
    gnt_valid_signal=dut.gnt_valid,
    gnt_signal=dut.gnt,
    gnt_id_signal=dut.gnt_id,
    log=logger
)

# Add transaction callback
def on_transaction(transaction):
    print(f"Grant to client {transaction.gnt_id} after {transaction.cycle_count} cycles")
    
arb_mon.add_transaction_callback(on_transaction)

# Wait for simulation to complete
await ClockCycles(dut.clk, 1000)

# Check fairness
fairness = arb_mon.get_fairness_index()
print(f"Fairness index: {fairness:.2f}")
```

### Round-Robin Arbiter Analysis
```python
# Create round-robin arbiter monitor
rr_mon = RoundRobinArbiterMonitor(
    dut=dut,
    title="RR_Arbiter",
    clock=dut.clk,
    reset_n=dut.rst_n,
    req_signal=dut.req,
    gnt_valid_signal=dut.gnt_valid,
    gnt_signal=dut.gnt,
    gnt_id_signal=dut.gnt_id,
    log=logger
)

# Wait for simulation to complete
await ClockCycles(dut.clk, 1000)

# Analyze priority pattern
priority_stats = rr_mon.get_priority_changes()
print(f"Priority changes: {priority_stats['changes']}")
print(f"Pattern type: {priority_stats['pattern']}")
```

### Weighted Round-Robin Analysis
```python
# Create weighted round-robin arbiter monitor
wrr_mon = WeightedRoundRobinArbiterMonitor(
    dut=dut,
    title="WRR_Arbiter",
    clock=dut.clk,
    reset_n=dut.rst_n,
    req_signal=dut.req,
    gnt_valid_signal=dut.gnt_valid,
    gnt_signal=dut.gnt,
    gnt_id_signal=dut.gnt_id,
    max_thresh_signal=dut.max_thresh,
    log=logger
)

# Wait for simulation to complete
await ClockCycles(dut.clk, 1000)

# Get inferred weights
weights = wrr_mon.get_inferred_weights()
print(f"Inferred weights: {weights}")

# Analyze weight distribution
dist = wrr_mon.get_weight_distribution()
print(f"Distribution type: {dist['distribution']}")
print(f"Observed ratios: {dist['observed_ratios']}")
print(f"Expected ratios: {dist['expected_ratios']}")
```

## Best Practices

1. **Monitor Configuration**: Match the monitor type to your arbiter implementation (standard, round-robin, or weighted).

2. **Signal Access**: Ensure all required signals are accessible from the testbench.

3. **Callbacks**: Use callbacks to integrate with scoreboards or other components:
   ```python
   # Integrate with scoreboard
   def on_transaction(transaction):
       scoreboard.add_transaction(transaction)
   
   arb_mon.add_transaction_callback(on_transaction)
   ```

4. **Reset Handling**: Register reset callbacks to reset dependent components:
   ```python
   def on_reset():
       scoreboard.clear()
       coverage.reset()
   
   arb_mon.add_reset_callback(on_reset)
   ```

5. **Fairness Analysis**: Check the fairness index periodically to detect starvation issues:
   ```python
   async def check_fairness():
       while True:
           await ClockCycles(dut.clk, 1000)
           fairness = arb_mon.get_fairness_index()
           assert fairness > 0.8, f"Poor fairness detected: {fairness:.2f}"
   ```

6. **Client-Specific Analysis**: Check individual client statistics to find specific issues:
   ```python
   for client in range(num_clients):
       stats = arb_mon.get_client_stats(client)
       print(f"Client {client}: grants={stats['grants']}, avg_wait={stats['avg_wait_time']:.2f}")
   ```

7. **Pattern Detection**: For round-robin arbiters, verify the priority changes follow the expected pattern:
   ```python
   priority_stats = rr_mon.get_priority_changes()
   assert priority_stats['pattern'] == 'round-robin', f"Unexpected priority pattern: {priority_stats['pattern']}"
   ```
