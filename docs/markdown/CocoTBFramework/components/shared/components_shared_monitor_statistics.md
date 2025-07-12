# monitor_statistics.py

Robust statistics class for Monitor components that provides comprehensive tracking of monitoring operations, protocol violations, and system state observations.

## Overview

The `monitor_statistics.py` module provides the `MonitorStatistics` class, which is designed specifically for monitor components that observe transactions and protocol behavior without actively participating in the communication. This class tracks various monitoring metrics and provides a standard interface for accessing statistics.

## Class

### MonitorStatistics

Robust statistics class designed for Monitor components to track observation metrics.

#### Constructor

```python
MonitorStatistics()
```

Creates a new MonitorStatistics instance with all counters initialized to zero.

```python
# Create monitor statistics
stats = MonitorStatistics()
```

#### Core Metrics

The class tracks the following metrics:

- **`received_transactions`**: Number of transactions received/observed
- **`transactions_observed`**: Number of transactions successfully observed  
- **`protocol_violations`**: Number of protocol violations detected
- **`x_z_violations`**: Number of X/Z (undefined) signal violations
- **`empty_cycles`**: Number of cycles where no valid transaction was present
- **`full_cycles`**: Number of cycles where buffers/FIFOs were full
- **`read_while_empty`**: Number of read attempts on empty buffers
- **`write_while_full`**: Number of write attempts on full buffers

#### Methods

##### `get_stats() -> Dict[str, int]`

Return all statistics as a dictionary.

**Returns:** Dictionary containing all statistics with metric names as keys and counts as values

```python
stats = monitor.get_stats()
print(f"Transactions observed: {stats['transactions_observed']}")
print(f"Protocol violations: {stats['protocol_violations']}")
print(f"X/Z violations: {stats['x_z_violations']}")

# Example output:
# {
#     'received_transactions': 1500,
#     'transactions_observed': 1485,
#     'protocol_violations': 3,
#     'x_z_violations': 12,
#     'empty_cycles': 450,
#     'full_cycles': 23,
#     'read_while_empty': 2,
#     'write_while_full': 1
# }
```

##### `reset()`

Reset all statistics to zero.

```python
# Clear all counters
stats.reset()

# Verify reset
all_stats = stats.get_stats()
assert all(count == 0 for count in all_stats.values())
```

##### `__str__() -> str`

Human-readable string representation.

**Returns:** String showing key statistics in a readable format

```python
print(stats)
# Output: MonitorStats: 1485 received, 3 violations, 12 X/Z
```

##### `__repr__() -> str`

Detailed representation for debugging.

**Returns:** String showing the complete internal state

```python
print(repr(stats))
# Output: MonitorStatistics({'received_transactions': 1485, 'transactions_observed': 1485, ...})
```

## Usage Patterns

### Basic Monitor Implementation

```python
class ProtocolMonitor:
    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.stats = MonitorStatistics()
        self.log = logging.getLogger(__name__)
    
    @cocotb.coroutine
    def monitor_loop(self):
        """Main monitoring loop"""
        while True:
            yield RisingEdge(self.clock)
            
            # Check for valid transaction
            if self.dut.valid.value == 1 and self.dut.ready.value == 1:
                self.stats.received_transactions += 1
                
                # Check for X/Z values
                if self._check_for_x_z_values():
                    self.stats.x_z_violations += 1
                    self.log.warning("X/Z values detected in transaction")
                else:
                    # Successfully observed transaction
                    self.stats.transactions_observed += 1
                    self._process_transaction()
            
            # Check for protocol violations
            if self._check_protocol_violations():
                self.stats.protocol_violations += 1
                self.log.error("Protocol violation detected")
            
            # Track empty/full conditions
            if self.dut.empty.value == 1:
                self.stats.empty_cycles += 1
                
                # Check for read while empty
                if self.dut.read.value == 1:
                    self.stats.read_while_empty += 1
                    self.log.warning("Read attempted while empty")
            
            if self.dut.full.value == 1:
                self.stats.full_cycles += 1
                
                # Check for write while full
                if self.dut.write.value == 1:
                    self.stats.write_while_full += 1
                    self.log.warning("Write attempted while full")
    
    def _check_for_x_z_values(self):
        """Check if any monitored signals have X/Z values"""
        try:
            # Check critical signals for X/Z
            for signal in [self.dut.addr, self.dut.data, self.dut.cmd]:
                if not signal.value.is_resolvable:
                    return True
            return False
        except:
            return True
    
    def _check_protocol_violations(self):
        """Check for protocol-specific violations"""
        # Example protocol checks
        if (self.dut.valid.value == 1 and 
            self.dut.ready.value == 1 and 
            self.dut.addr.value.is_resolvable):
            
            addr = int(self.dut.addr.value)
            
            # Check address alignment
            if addr % 4 != 0:
                return True
            
            # Check address range
            if addr >= 0x10000:
                return True
        
        return False
    
    def _process_transaction(self):
        """Process a valid transaction"""
        # Extract transaction details and forward to scoreboard
        pass
    
    def get_monitoring_report(self):
        """Generate monitoring report"""
        stats = self.stats.get_stats()
        
        success_rate = 0
        if stats['received_transactions'] > 0:
            success_rate = (stats['transactions_observed'] / stats['received_transactions']) * 100
        
        return f"""
        Monitoring Report:
        ==================
        Transactions received: {stats['received_transactions']}
        Transactions observed: {stats['transactions_observed']}
        Success rate: {success_rate:.1f}%
        
        Issues Detected:
        - Protocol violations: {stats['protocol_violations']}
        - X/Z violations: {stats['x_z_violations']}
        - Read while empty: {stats['read_while_empty']}
        - Write while full: {stats['write_while_full']}
        
        System State:
        - Empty cycles: {stats['empty_cycles']}
        - Full cycles: {stats['full_cycles']}
        """
```

### FIFO Monitor Example

```python
class FIFOMonitor:
    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock
        self.stats = MonitorStatistics()
        self.log = logging.getLogger(__name__)
        
        # FIFO-specific tracking
        self.depth_history = []
        self.max_depth_seen = 0
    
    @cocotb.coroutine
    def monitor_fifo(self):
        """Monitor FIFO operations"""
        while True:
            yield RisingEdge(self.clock)
            
            # Monitor write operations
            if self.dut.write.value == 1:
                self.stats.received_transactions += 1
                
                if self.dut.full.value == 1:
                    self.stats.write_while_full += 1
                    self.log.error("Write attempted while FIFO full")
                else:
                    self.stats.transactions_observed += 1
                    self._track_write_transaction()
            
            # Monitor read operations
            if self.dut.read.value == 1:
                self.stats.received_transactions += 1
                
                if self.dut.empty.value == 1:
                    self.stats.read_while_empty += 1
                    self.log.error("Read attempted while FIFO empty")
                else:
                    self.stats.transactions_observed += 1
                    self._track_read_transaction()
            
            # Track FIFO state
            if self.dut.empty.value == 1:
                self.stats.empty_cycles += 1
            
            if self.dut.full.value == 1:
                self.stats.full_cycles += 1
            
            # Track depth if available
            if hasattr(self.dut, 'count'):
                try:
                    depth = int(self.dut.count.value)
                    self.depth_history.append(depth)
                    self.max_depth_seen = max(self.max_depth_seen, depth)
                    
                    # Keep only recent history
                    if len(self.depth_history) > 1000:
                        self.depth_history = self.depth_history[-500:]
                        
                except:
                    pass
    
    def _track_write_transaction(self):
        """Track write transaction details"""
        try:
            if not self.dut.wr_data.value.is_resolvable:
                self.stats.x_z_violations += 1
                self.log.warning("X/Z data in write transaction")
        except:
            self.stats.x_z_violations += 1
    
    def _track_read_transaction(self):
        """Track read transaction details"""
        try:
            if not self.dut.rd_data.value.is_resolvable:
                self.stats.x_z_violations += 1
                self.log.warning("X/Z data in read transaction")
        except:
            self.stats.x_z_violations += 1
    
    def get_fifo_analysis(self):
        """Get FIFO-specific analysis"""
        stats = self.stats.get_stats()
        
        analysis = {
            'basic_stats': stats,
            'max_depth_seen': self.max_depth_seen,
            'average_depth': sum(self.depth_history) / len(self.depth_history) if self.depth_history else 0,
            'utilization_percent': (self.max_depth_seen / getattr(self.dut, 'DEPTH', 100)) * 100
        }
        
        return analysis
```

### AXI Monitor Example

```python
class AXIMonitor:
    def __init__(self, dut, aclk):
        self.dut = dut
        self.aclk = aclk
        self.stats = MonitorStatistics()
        self.log = logging.getLogger(__name__)
        
        # AXI-specific tracking
        self.outstanding_transactions = {}
        self.burst_tracking = {}
    
    @cocotb.coroutine
    def monitor_axi(self):
        """Monitor AXI transactions"""
        # Start separate coroutines for different channels
        cocotb.fork(self._monitor_write_address())
        cocotb.fork(self._monitor_write_data())
        cocotb.fork(self._monitor_write_response())
        cocotb.fork(self._monitor_read_address())
        cocotb.fork(self._monitor_read_data())
    
    @cocotb.coroutine
    def _monitor_write_address(self):
        """Monitor AXI write address channel"""
        while True:
            yield RisingEdge(self.aclk)
            
            if (self.dut.awvalid.value == 1 and self.dut.awready.value == 1):
                self.stats.received_transactions += 1
                
                try:
                    awid = int(self.dut.awid.value)
                    awaddr = int(self.dut.awaddr.value)
                    awlen = int(self.dut.awlen.value)
                    
                    # Check for X/Z values
                    if (not self.dut.awid.value.is_resolvable or
                        not self.dut.awaddr.value.is_resolvable or
                        not self.dut.awlen.value.is_resolvable):
                        self.stats.x_z_violations += 1
                    else:
                        self.stats.transactions_observed += 1
                        self._track_write_address(awid, awaddr, awlen)
                        
                except:
                    self.stats.x_z_violations += 1
    
    @cocotb.coroutine  
    def _monitor_write_data(self):
        """Monitor AXI write data channel"""
        while True:
            yield RisingEdge(self.aclk)
            
            if (self.dut.wvalid.value == 1 and self.dut.wready.value == 1):
                self.stats.received_transactions += 1
                
                try:
                    if not self.dut.wdata.value.is_resolvable:
                        self.stats.x_z_violations += 1
                    else:
                        self.stats.transactions_observed += 1
                        
                except:
                    self.stats.x_z_violations += 1
    
    def _track_write_address(self, awid, awaddr, awlen):
        """Track write address transaction"""
        self.outstanding_transactions[awid] = {
            'type': 'write',
            'addr': awaddr,
            'len': awlen,
            'data_beats': 0,
            'start_time': cocotb.utils.get_sim_time()
        }
    
    def get_axi_report(self):
        """Generate AXI-specific monitoring report"""
        stats = self.stats.get_stats()
        
        return f"""
        AXI Monitor Report:
        ===================
        Transactions: {stats['transactions_observed']}/{stats['received_transactions']}
        Protocol Violations: {stats['protocol_violations']}
        X/Z Violations: {stats['x_z_violations']}
        Outstanding Transactions: {len(self.outstanding_transactions)}
        """
```

### Advanced Statistics Analysis

```python
class AdvancedMonitorAnalysis:
    def __init__(self, monitor_stats):
        self.stats = monitor_stats
        self.history = []
    
    def capture_snapshot(self):
        """Capture current statistics snapshot"""
        snapshot = {
            'timestamp': cocotb.utils.get_sim_time(),
            'stats': self.stats.get_stats().copy()
        }
        self.history.append(snapshot)
    
    def calculate_rates(self, time_window=None):
        """Calculate transaction rates over time"""
        if len(self.history) < 2:
            return {}
        
        recent = self.history[-1]
        baseline = self.history[0] if time_window is None else self._find_baseline(time_window)
        
        if baseline is None:
            return {}
        
        time_diff = recent['timestamp'] - baseline['timestamp']
        if time_diff == 0:
            return {}
        
        rates = {}
        for metric in recent['stats']:
            diff = recent['stats'][metric] - baseline['stats'][metric]
            rates[f'{metric}_rate'] = diff / time_diff
        
        return rates
    
    def _find_baseline(self, time_window):
        """Find baseline snapshot within time window"""
        current_time = self.history[-1]['timestamp']
        target_time = current_time - time_window
        
        for snapshot in reversed(self.history[:-1]):
            if snapshot['timestamp'] <= target_time:
                return snapshot
        
        return self.history[0]
    
    def detect_anomalies(self):
        """Detect statistical anomalies"""
        if len(self.history) < 10:
            return []
        
        anomalies = []
        recent_stats = self.stats.get_stats()
        
        # Check for sudden increase in violations
        if len(self.history) > 1:
            prev_stats = self.history[-2]['stats']
            
            violation_increase = (recent_stats['protocol_violations'] - 
                                prev_stats['protocol_violations'])
            
            if violation_increase > 5:  # Threshold
                anomalies.append({
                    'type': 'violation_spike',
                    'description': f'Protocol violations increased by {violation_increase}',
                    'severity': 'high'
                })
            
            xz_increase = (recent_stats['x_z_violations'] - 
                          prev_stats['x_z_violations'])
            
            if xz_increase > 10:  # Threshold
                anomalies.append({
                    'type': 'xz_spike',
                    'description': f'X/Z violations increased by {xz_increase}',
                    'severity': 'medium'
                })
        
        return anomalies
    
    def generate_trend_analysis(self):
        """Generate trend analysis report"""
        if len(self.history) < 5:
            return "Insufficient data for trend analysis"
        
        trends = {}
        metrics = ['received_transactions', 'protocol_violations', 'x_z_violations']
        
        for metric in metrics:
            values = [snapshot['stats'][metric] for snapshot in self.history[-10:]]
            
            # Simple trend calculation
            if len(values) >= 2:
                recent_avg = sum(values[-3:]) / len(values[-3:])
                older_avg = sum(values[:3]) / len(values[:3])
                
                if recent_avg > older_avg * 1.1:
                    trends[metric] = 'increasing'
                elif recent_avg < older_avg * 0.9:
                    trends[metric] = 'decreasing'
                else:
                    trends[metric] = 'stable'
        
        return trends
```

### Integration with Test Framework

```python
@cocotb.test()
def comprehensive_monitoring_test(dut):
    """Test with comprehensive monitoring"""
    
    # Set up monitoring
    monitor = ProtocolMonitor(dut, dut.clk)
    analysis = AdvancedMonitorAnalysis(monitor.stats)
    
    # Start monitoring
    monitor_task = cocotb.fork(monitor.monitor_loop())
    
    # Run test sequence
    yield run_test_operations(dut)
    
    # Capture final statistics
    analysis.capture_snapshot()
    
    # Generate comprehensive report
    final_stats = monitor.stats.get_stats()
    rates = analysis.calculate_rates()
    anomalies = analysis.detect_anomalies()
    trends = analysis.generate_trend_analysis()
    
    # Log results
    cocotb.log.info("=== Final Monitoring Results ===")
    cocotb.log.info(f"Transactions observed: {final_stats['transactions_observed']}")
    cocotb.log.info(f"Protocol violations: {final_stats['protocol_violations']}")
    cocotb.log.info(f"X/Z violations: {final_stats['x_z_violations']}")
    
    if anomalies:
        cocotb.log.warning(f"Detected {len(anomalies)} anomalies")
        for anomaly in anomalies:
            cocotb.log.warning(f"  {anomaly['type']}: {anomaly['description']}")
    
    # Assert test criteria
    assert final_stats['protocol_violations'] == 0, "Protocol violations detected"
    assert final_stats['x_z_violations'] <= 5, "Too many X/Z violations"
    
    # Clean up
    monitor_task.kill()
```

## Best Practices

### 1. **Reset Statistics Between Test Phases**
```python
def run_test_phase(phase_name, monitor):
    monitor.stats.reset()
    # Run phase
    yield run_phase_operations()
    # Report phase results
    stats = monitor.stats.get_stats()
    log.info(f"{phase_name}: {stats}")
```

### 2. **Use Statistics for Test Validation**
```python
# Validate expected activity levels
stats = monitor.stats.get_stats()
assert stats['transactions_observed'] > 100, "Insufficient transaction activity"
assert stats['protocol_violations'] == 0, "Protocol violations detected"
```

### 3. **Monitor Continuously During Long Tests**
```python
@cocotb.coroutine
def periodic_stats_report(monitor, interval=1000):
    while True:
        yield ClockCycles(dut.clk, interval)
        stats = monitor.stats.get_stats()
        log.info(f"Stats update: {stats}")
```

### 4. **Combine with Other Statistics Classes**
```python
# Use alongside master/slave statistics for complete picture
master_stats = MasterStatistics()
monitor_stats = MonitorStatistics()
slave_stats = SlaveStatistics()

# Compare at end of test
def compare_statistics():
    m_stats = master_stats.get_stats()
    mon_stats = monitor_stats.get_stats()
    s_stats = slave_stats.get_stats()
    
    # Validate consistency
    assert abs(m_stats['transactions_sent'] - mon_stats['transactions_observed']) <= 1
```

The MonitorStatistics class provides essential visibility into monitoring operations and system behavior, enabling effective debugging and validation of protocol implementations during verification.
