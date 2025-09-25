# arbiter_monitor.py

Enhanced Generic Arbiter Monitor Component for observing various types of arbiter interfaces including round-robin and weighted round-robin arbiters. This module provides comprehensive monitoring capabilities with improved signal sampling timing, proper grant validation, and robust transaction tracking.

## Overview

The `arbiter_monitor.py` module provides sophisticated arbiter monitoring capabilities for verification environments. It includes transaction tracking, fairness analysis, pattern compliance verification, and real-time statistics collection.

### Key Features
- **Multiple arbiter types**: Support for round-robin and weighted round-robin arbiters
- **Transaction tracking**: Complete transaction records with timing information
- **Fairness analysis**: Jain's fairness index calculation and compliance checking
- **Pattern verification**: Grant sequence analysis and compliance validation
- **Real-time statistics**: Live performance metrics and behavioral analysis
- **Flexible callbacks**: Event-driven architecture for integration
- **Robust signal handling**: Proper timing and X/Z state management

## Data Structures

### ArbiterTransaction

Named tuple representing a complete arbiter transaction.

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

**Fields:**
- `req_vector`: Binary representation of all active requests
- `gnt_vector`: Binary representation of the grant (usually one-hot)
- `gnt_id`: Integer ID of the client that received the grant
- `cycle_count`: Number of clock cycles from request to grant
- `timestamp`: Simulation timestamp when grant was issued
- `weights`: Weight values for weighted arbiters (optional)
- `metadata`: Additional information (blocked state, thresholds, etc.)

## Core Classes

### ArbiterMonitor

Enhanced generic arbiter monitor component that observes arbiter transactions with comprehensive analysis capabilities.

#### Constructor

```python
ArbiterMonitor(dut, title, clock, reset_n, req_signal, gnt_valid_signal, gnt_signal,
               gnt_id_signal, gnt_ack_signal=None, block_arb_signal=None,
               max_thresh_signal=None, is_weighted=False, clients=None, log=None,
               clock_period_ns=10)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title (for logging and identification)
- `clock`: Clock signal
- `reset_n`: Reset signal (active low)
- `req_signal`: Request input signal (bus)
- `gnt_valid_signal`: Grant valid output signal
- `gnt_signal`: Grant output signal (bus)
- `gnt_id_signal`: Grant ID output signal
- `gnt_ack_signal`: Grant acknowledge input signal (bus), optional
- `block_arb_signal`: Signal to block arbitration, optional
- `max_thresh_signal`: Maximum threshold signal for weighted arbiters, optional
- `is_weighted`: True if monitoring a weighted arbiter
- `clients`: Number of clients (auto-detected if None)
- `log`: Logger instance (creates new if None)
- `clock_period_ns`: Clock period in nanoseconds for timing calculations

#### Core Properties

- `clients`: Number of clients being arbitrated
- `transactions`: Deque of recent transactions (bounded for memory efficiency)
- `pending_requests`: Dictionary mapping client index to request timestamp
- `stats`: Comprehensive statistics dictionary
- `monitoring_enabled`: Global enable/disable flag
- `debug_enabled`: Debug logging control

## Monitoring Control

### `start_monitoring()`

Start all monitoring coroutines.

```python
arbiter_monitor.start_monitoring()
```

This method starts the following coroutines:
- Request monitoring (`_monitor_requests`)
- Grant monitoring (`_monitor_grants`)
- Reset monitoring (`_monitor_reset`)
- Block signal monitoring (`_monitor_block`) - if block signal provided
- Threshold monitoring (`_monitor_thresholds`) - if weighted arbiter

### `enable_monitoring(enable=True)`

Enable or disable monitoring.

```python
arbiter_monitor.enable_monitoring(True)   # Enable monitoring
arbiter_monitor.enable_monitoring(False)  # Disable monitoring
```

### `enable_debug(enable=True)`

Enable or disable debug logging.

```python
arbiter_monitor.enable_debug(True)   # Enable debug logging
arbiter_monitor.enable_debug(False)  # Disable debug logging
```

## Callback Management

### `add_transaction_callback(callback)`

Register a callback function for completed transactions.

**Parameters:**
- `callback`: Function that accepts an ArbiterTransaction object

```python
def transaction_handler(transaction):
    print(f"Grant to client {transaction.gnt_id} after {transaction.cycle_count} cycles")

arbiter_monitor.add_transaction_callback(transaction_handler)
```

### `add_reset_callback(callback)`

Register a callback function for reset events.

**Parameters:**
- `callback`: Function called when reset is detected

```python
def reset_handler():
    print("Arbiter reset detected")

arbiter_monitor.add_reset_callback(reset_handler)
```

## Statistics and Analysis

### `get_transaction_count()`

Get the total number of observed transactions.

**Returns:** Integer count of completed transactions

```python
total_transactions = arbiter_monitor.get_transaction_count()
```

### `get_client_stats(client_id)`

Get statistics for a specific client.

**Parameters:**
- `client_id`: Client identifier (0 to clients-1)

**Returns:** Dictionary with client-specific statistics or None if invalid client_id

```python
client_stats = arbiter_monitor.get_client_stats(0)
if client_stats:
    print(f"Client 0: {client_stats['grants']} grants, avg wait: {client_stats['avg_wait_time']:.2f}ns")
```

### `get_fairness_index()`

Calculate Jain's fairness index for the arbiter.

**Returns:** Float between 0.0 (completely unfair) and 1.0 (perfectly fair)

```python
fairness = arbiter_monitor.get_fairness_index()
if fairness > 0.9:
    print("Arbiter shows good fairness")
elif fairness < 0.5:
    print("Arbiter shows poor fairness")
```

### `get_stats_summary()`

Get a comprehensive statistics summary.

**Returns:** Dictionary with complete statistics including per-client data

```python
summary = arbiter_monitor.get_stats_summary()
print(f"Total transactions: {summary['total_transactions']}")
print(f"Fairness index: {summary['fairness_index']:.3f}")

for client_stat in summary['client_stats']:
    print(f"Client {client_stat['client_id']}: {client_stat['grants']} grants ({client_stat['percentage']:.1f}%)")
```

## Specialized Monitor Classes

### RoundRobinArbiterMonitor

Monitor specifically tailored for Round Robin Arbiters with pattern compliance analysis.

#### Constructor

```python
RoundRobinArbiterMonitor(dut, title, clock, reset_n, req_signal, gnt_valid_signal, 
                        gnt_signal, gnt_id_signal, gnt_ack_signal=None, 
                        block_arb_signal=None, clients=None, log=None, clock_period_ns=10)
```

Inherits all parameters from ArbiterMonitor (automatically sets `is_weighted=False`).

#### Additional Methods

##### `analyze_round_robin_pattern()`

Analyze if the grant pattern follows round-robin behavior.

**Returns:** Dictionary with pattern analysis results

```python
pattern_analysis = rr_monitor.analyze_round_robin_pattern()
if pattern_analysis['status'] == 'valid_round_robin':
    print("Round-robin pattern verified")
else:
    print(f"Pattern violations detected: {pattern_analysis['violations']}")
    print(f"Compliance: {pattern_analysis['pattern_compliance']:.1%}")
```

### WeightedRoundRobinArbiterMonitor

Monitor specifically tailored for Weighted Round Robin Arbiters with weight compliance analysis.

#### Constructor

```python
WeightedRoundRobinArbiterMonitor(dut, title, clock, reset_n, req_signal, gnt_valid_signal,
                                gnt_signal, gnt_id_signal, gnt_ack_signal=None, 
                                block_arb_signal=None, max_thresh_signal=None, 
                                clients=None, log=None, clock_period_ns=10)
```

Inherits all parameters from ArbiterMonitor (automatically sets `is_weighted=True`).

#### Additional Methods

##### `analyze_weight_compliance(expected_weights=None)`

Analyze if grant distribution matches expected weights.

**Parameters:**
- `expected_weights`: List of expected weights for each client

**Returns:** Dictionary with weight compliance analysis

```python
expected_weights = [1, 2, 3, 4]  # Client weights
compliance = wrr_monitor.analyze_weight_compliance(expected_weights)

if compliance['is_compliant']:
    print(f"Weight compliance verified: {compliance['overall_compliance']:.1%}")
else:
    print("Weight compliance issues detected:")
    for client_data in compliance['client_compliance']:
        print(f"  Client {client_data['client']}: {client_data['compliance']:.1%} compliant")
```

## Usage Patterns

### Basic Round-Robin Arbiter Monitoring

```python
import cocotb
from cocotb.triggers import Timer, RisingEdge
from components.misc.arbiter_monitor import RoundRobinArbiterMonitor

@cocotb.test()
async def test_round_robin_arbiter(dut):
    """Test round-robin arbiter fairness and pattern compliance"""
    
    # Create round-robin arbiter monitor
    arbiter_monitor = RoundRobinArbiterMonitor(
        dut=dut,
        title="RR_Arbiter",
        clock=dut.clk,
        reset_n=dut.reset_n,
        req_signal=dut.req,
        gnt_valid_signal=dut.gnt_valid,
        gnt_signal=dut.gnt,
        gnt_id_signal=dut.gnt_id,
        clients=4,  # 4-client arbiter
        clock_period_ns=10
    )
    
    # Add transaction callback for logging
    def log_transaction(txn):
        print(f"Grant to client {txn.gnt_id} after {txn.cycle_count} cycles")
    
    arbiter_monitor.add_transaction_callback(log_transaction)
    
    # Start monitoring
    arbiter_monitor.start_monitoring()
    
    # Run test stimulus
    await reset_sequence(dut)
    await stimulus_sequence(dut)
    
    # Analyze results
    stats = arbiter_monitor.get_stats_summary()
    pattern_analysis = arbiter_monitor.analyze_round_robin_pattern()
    
    # Verify fairness
    fairness = arbiter_monitor.get_fairness_index()
    assert fairness > 0.8, f"Poor fairness detected: {fairness:.3f}"
    
    # Verify round-robin pattern
    assert pattern_analysis['status'] == 'valid_round_robin', \
        f"Round-robin pattern violations: {pattern_analysis['violations']}"
    
    print(f"Test completed: {stats['total_transactions']} transactions, "
          f"fairness={fairness:.3f}")

async def reset_sequence(dut):
    """Apply reset sequence"""
    dut.reset_n.value = 0
    await Timer(100, units='ns')
    dut.reset_n.value = 1
    await Timer(50, units='ns')

async def stimulus_sequence(dut):
    """Generate test stimulus"""
    # Apply various request patterns
    for cycle in range(1000):
        # Generate random request pattern
        dut.req.value = random.randint(0, 15)  # 4-bit request vector
        await RisingEdge(dut.clk)
```

### Weighted Round-Robin Arbiter Monitoring

```python
@cocotb.test()
async def test_weighted_arbiter(dut):
    """Test weighted round-robin arbiter with weight compliance"""
    
    # Create weighted arbiter monitor
    arbiter_monitor = WeightedRoundRobinArbiterMonitor(
        dut=dut,
        title="WRR_Arbiter",
        clock=dut.clk,
        reset_n=dut.reset_n,
        req_signal=dut.req,
        gnt_valid_signal=dut.gnt_valid,
        gnt_signal=dut.gnt,
        gnt_id_signal=dut.gnt_id,
        max_thresh_signal=dut.max_thresh,
        clients=4,
        clock_period_ns=10
    )
    
    # Enable debug for detailed analysis
    arbiter_monitor.enable_debug(True)
    
    # Start monitoring
    arbiter_monitor.start_monitoring()
    
    # Configure arbiter weights
    expected_weights = [1, 2, 3, 4]  # Client 0=1, Client 1=2, etc.
    
    # Run test
    await reset_sequence(dut)
    await configure_weights(dut, expected_weights)
    await stimulus_sequence_weighted(dut)
    
    # Analyze weight compliance
    compliance = arbiter_monitor.analyze_weight_compliance(expected_weights)
    
    assert compliance['is_compliant'], \
        f"Weight compliance failed: {compliance['overall_compliance']:.1%}"
    
    # Print detailed results
    print("Weight Compliance Analysis:")
    for client_data in compliance['client_compliance']:
        print(f"  Client {client_data['client']}: "
              f"Expected {client_data['expected_ratio']:.1%}, "
              f"Actual {client_data['actual_ratio']:.1%}, "
              f"Compliance {client_data['compliance']:.1%}")
```

### Advanced Monitoring with Statistics Analysis

```python
class ArbiterAnalyzer:
    """Advanced arbiter analysis with detailed statistics"""
    
    def __init__(self, arbiter_monitor):
        self.monitor = arbiter_monitor
        self.analysis_data = []
        
        # Add callback for real-time analysis
        self.monitor.add_transaction_callback(self.analyze_transaction)
    
    def analyze_transaction(self, transaction):
        """Analyze each transaction for patterns"""
        self.analysis_data.append({
            'timestamp': transaction.timestamp,
            'client_id': transaction.gnt_id,
            'wait_cycles': transaction.cycle_count,
            'req_vector': transaction.req_vector,
            'blocked': transaction.metadata.get('blocked', False)
        })
    
    def generate_report(self):
        """Generate comprehensive analysis report"""
        stats = self.monitor.get_stats_summary()
        
        report = {
            'summary': stats,
            'fairness_analysis': self._analyze_fairness(),
            'timing_analysis': self._analyze_timing(),
            'pattern_analysis': self._analyze_patterns()
        }
        
        return report
    
    def _analyze_fairness(self):
        """Analyze fairness over time"""
        fairness = self.monitor.get_fairness_index()
        
        # Calculate fairness in windows
        window_size = 100
        fairness_history = []
        
        for i in range(0, len(self.analysis_data), window_size):
            window = self.analysis_data[i:i+window_size]
            if len(window) >= window_size:
                client_counts = [0] * self.monitor.clients
                for txn in window:
                    client_counts[txn['client_id']] += 1
                
                # Calculate Jain's fairness for this window
                n = len(client_counts)
                squared_sum = sum(client_counts) ** 2
                sum_of_squares = sum(x ** 2 for x in client_counts)
                
                window_fairness = 1.0 if sum_of_squares == 0 else squared_sum / (n * sum_of_squares)
                fairness_history.append(window_fairness)
        
        return {
            'overall_fairness': fairness,
            'fairness_trend': fairness_history,
            'fairness_stability': np.std(fairness_history) if fairness_history else 0
        }
    
    def _analyze_timing(self):
        """Analyze timing characteristics"""
        wait_times = [txn['wait_cycles'] for txn in self.analysis_data]
        
        if not wait_times:
            return {'status': 'no_data'}
        
        return {
            'avg_wait_time': np.mean(wait_times),
            'max_wait_time': np.max(wait_times),
            'min_wait_time': np.min(wait_times),
            'wait_time_std': np.std(wait_times),
            'percentiles': {
                '50th': np.percentile(wait_times, 50),
                '90th': np.percentile(wait_times, 90),
                '99th': np.percentile(wait_times, 99)
            }
        }
    
    def _analyze_patterns(self):
        """Analyze grant patterns"""
        if isinstance(self.monitor, RoundRobinArbiterMonitor):
            return self.monitor.analyze_round_robin_pattern()
        elif isinstance(self.monitor, WeightedRoundRobinArbiterMonitor):
            # Would need expected weights to analyze
            return {'status': 'weighted_analysis_requires_expected_weights'}
        else:
            return {'status': 'pattern_analysis_not_available'}

# Usage
analyzer = ArbiterAnalyzer(arbiter_monitor)
# ... run test ...
report = analyzer.generate_report()
```

### Callback-Based Integration

```python
class ArbiterTestBench:
    """Testbench with integrated arbiter monitoring"""
    
    def __init__(self, dut):
        self.dut = dut
        self.scoreboard = ArbiterScoreboard()
        self.coverage = ArbiterCoverage()
        
        # Create monitor
        self.arbiter_monitor = RoundRobinArbiterMonitor(
            dut=dut,
            title="TB_Arbiter",
            clock=dut.clk,
            reset_n=dut.reset_n,
            req_signal=dut.req,
            gnt_valid_signal=dut.gnt_valid,
            gnt_signal=dut.gnt,
            gnt_id_signal=dut.gnt_id
        )
        
        # Register callbacks
        self.arbiter_monitor.add_transaction_callback(self.scoreboard.record_transaction)
        self.arbiter_monitor.add_transaction_callback(self.coverage.sample_transaction)
        self.arbiter_monitor.add_reset_callback(self.handle_reset)
    
    def handle_reset(self):
        """Handle reset events"""
        self.scoreboard.reset()
        self.coverage.reset()
        print("Testbench reset due to DUT reset")
    
    async def run_test(self, test_name):
        """Run a specific test"""
        print(f"Starting test: {test_name}")
        
        # Start monitoring
        self.arbiter_monitor.start_monitoring()
        
        # Run test-specific stimulus
        await self.run_stimulus(test_name)
        
        # Generate final report
        self.generate_final_report()
    
    def generate_final_report(self):
        """Generate comprehensive test report"""
        stats = self.arbiter_monitor.get_stats_summary()
        fairness = self.arbiter_monitor.get_fairness_index()
        
        print(f"\n=== Arbiter Test Report ===")
        print(f"Total Transactions: {stats['total_transactions']}")
        print(f"Fairness Index: {fairness:.3f}")
        print(f"Average Wait Time: {stats['avg_wait_time']:.1f} cycles")
        
        for client_stat in stats['client_stats']:
            print(f"Client {client_stat['client_id']}: "
                  f"{client_stat['grants']} grants ({client_stat['percentage']:.1f}%), "
                  f"avg wait: {client_stat['avg_wait_time']:.1f} cycles")
```

## Error Handling and Debugging

### Signal Resolution Issues

```python
# Enable debug logging for signal issues
arbiter_monitor.enable_debug(True)

# Monitor will log warnings for:
# - Unresolvable signals
# - Invalid grant vectors (all zeros when valid asserted)
# - Grant ID out of range
# - Mismatched grant ID and grant vector
```

### Performance Considerations

```python
# Limit transaction history for memory efficiency
arbiter_monitor.transactions.maxlen = 500  # Reduce from default 1000

# Disable debug logging for performance
arbiter_monitor.enable_debug(False)

# Temporarily disable monitoring during intensive operations
arbiter_monitor.enable_monitoring(False)
# ... intensive operations ...
arbiter_monitor.enable_monitoring(True)
```

## Best Practices

### 1. **Proper Signal Connections**
```python
# Ensure all required signals are connected
assert hasattr(dut, 'req'), "Request signal missing"
assert hasattr(dut, 'gnt_valid'), "Grant valid signal missing"
assert hasattr(dut, 'gnt'), "Grant signal missing"
assert hasattr(dut, 'gnt_id'), "Grant ID signal missing"
```

### 2. **Clock Period Configuration**
```python
# Set accurate clock period for timing analysis
clock_period_ns = 10  # 100MHz clock
arbiter_monitor = ArbiterMonitor(..., clock_period_ns=clock_period_ns)
```

### 3. **Use Appropriate Monitor Type**
```python
# Use specialized monitors for better analysis
if arbiter_type == "round_robin":
    monitor = RoundRobinArbiterMonitor(...)
elif arbiter_type == "weighted":
    monitor = WeightedRoundRobinArbiterMonitor(...)
else:
    monitor = ArbiterMonitor(...)
```

### 4. **Regular Statistics Checking**
```python
# Check statistics periodically during long tests
async def periodic_stats_check():
    while True:
        await Timer(1000000, units='ns')  # Every 1ms
        stats = arbiter_monitor.get_stats_summary()
        if stats['total_transactions'] > 0:
            fairness = arbiter_monitor.get_fairness_index()
            if fairness < 0.5:
                print(f"WARNING: Low fairness detected: {fairness:.3f}")
```

### 5. **Comprehensive Final Analysis**
```python
# Always perform final analysis
def final_analysis(arbiter_monitor):
    # Basic statistics
    stats = arbiter_monitor.get_stats_summary()
    fairness = arbiter_monitor.get_fairness_index()
    
    # Pattern-specific analysis
    if isinstance(arbiter_monitor, RoundRobinArbiterMonitor):
        pattern = arbiter_monitor.analyze_round_robin_pattern()
        assert pattern['status'] == 'valid_round_robin'
    
    # Fairness assertions
    assert fairness > 0.7, f"Poor fairness: {fairness:.3f}"
    assert stats['total_transactions'] > 100, "Insufficient test coverage"
```

The arbiter monitoring components provide comprehensive verification capabilities for arbitration logic, enabling thorough analysis of fairness, timing, and behavioral compliance in complex multi-master systems.
