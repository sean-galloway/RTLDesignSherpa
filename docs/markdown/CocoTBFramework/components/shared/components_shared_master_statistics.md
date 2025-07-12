# master_statistics.py

Statistics tracking classes for Master and Slave components that provide comprehensive performance monitoring, error tracking, and throughput analysis for BFM (Bus Functional Model) components.

## Overview

The `master_statistics.py` module provides three main classes:
- **MasterStatistics**: For master components (writers/drivers)
- **SlaveStatistics**: For slave components (readers/responders)  
- **ComponentStatistics**: Backward compatibility alias for MasterStatistics

These classes track performance metrics, error conditions, and provide detailed statistics for analysis and debugging.

## Classes

### MasterStatistics

Statistics tracking for Master components that initiate transactions.

#### Constructor

```python
MasterStatistics(window_size: int = 100)
```

**Parameters:**
- `window_size`: Number of recent transactions to track for moving averages (default: 100)

#### Core Metrics

- **Transaction Counts**: `transactions_sent`, `transactions_completed`, `transactions_failed`
- **Data Transfer**: `bytes_transferred`
- **Performance**: `total_latency`, `peak_throughput`
- **Protocol Issues**: `protocol_violations`, `timeout_events`, `retry_attempts`
- **Flow Control**: `flow_control_stalls`, `backpressure_cycles`
- **Error Tracking**: `error_types`, `last_error_time`, `last_error_message`

#### Methods

##### `record_transaction_start() -> float`
Record the start of a transaction.

**Returns:** Transaction start timestamp for latency calculation

```python
stats = MasterStatistics()
start_time = stats.record_transaction_start()
# ... perform transaction ...
stats.record_transaction_complete(start_time, bytes_count=64)
```

##### `record_transaction_complete(start_time: float, bytes_count: int = 0)`
Record completion of a transaction.

**Parameters:**
- `start_time`: Transaction start timestamp from `record_transaction_start()`
- `bytes_count`: Number of bytes transferred in this transaction

```python
# Complete transaction with timing and data count
stats.record_transaction_complete(start_time, bytes_count=32)
```

##### `record_transaction_failed(error_type: str, error_message: str = "")`
Record a failed transaction.

**Parameters:**
- `error_type`: Type/category of error
- `error_message`: Detailed error message

```python
stats.record_transaction_failed("timeout", "Transaction timed out after 1000 cycles")
stats.record_transaction_failed("decode_error", "Invalid address 0xDEADBEEF")
```

##### `record_protocol_violation(violation_type: str)`
Record a protocol violation.

```python
stats.record_protocol_violation("invalid_burst_length")
```

##### `record_timeout()`
Record a timeout event.

```python
stats.record_timeout()
```

##### `record_retry()`
Record a retry attempt.

```python
stats.record_retry()
```

##### `record_flow_control_stall(cycles: int = 1)`
Record flow control stalls (backpressure).

**Parameters:**
- `cycles`: Number of clock cycles stalled

```python
stats.record_flow_control_stall(cycles=5)  # Stalled for 5 cycles
```

##### `update_throughput()`
Update throughput calculations (call periodically).

```python
# Call every second or every N transactions
stats.update_throughput()
```

#### Analysis Methods

##### `get_average_latency() -> float`
Get average latency across all transactions.

```python
avg_latency = stats.get_average_latency()
print(f"Average latency: {avg_latency:.2f} seconds")
```

##### `get_recent_average_latency() -> float`
Get average latency for recent transactions (within window).

```python
recent_latency = stats.get_recent_average_latency()
```

##### `get_current_throughput() -> float`
Get current throughput (transactions per second).

```python
current_tps = stats.get_current_throughput()
```

##### `get_average_throughput() -> float`
Get average throughput across all time.

```python
avg_tps = stats.get_average_throughput()
```

##### `get_success_rate() -> float`
Get transaction success rate as percentage.

```python
success_rate = stats.get_success_rate()
print(f"Success rate: {success_rate:.1f}%")
```

##### `get_stats() -> Dict[str, Any]`
Get comprehensive statistics dictionary.

**Returns:** Dictionary containing all statistics including:
- Transaction counts and success rates
- Performance metrics (latency, throughput)
- Protocol and flow control statistics
- Error information
- Operational info (uptime, window size)

```python
all_stats = stats.get_stats()
print(f"Completed: {all_stats['transactions_completed']}")
print(f"Success rate: {all_stats['success_rate_percent']:.1f}%")
print(f"Average latency: {all_stats['average_latency_ms']:.2f}ms")
```

##### `reset()`
Reset all statistics to initial state.

```python
stats.reset()  # Clear all counters and history
```

#### String Representation

```python
print(stats)
# Output: MasterStats: 150/155 (96.8% success), Avg Latency: 2.34ms, Throughput: 45.2 tps
```

### SlaveStatistics

Statistics tracking for Slave components that respond to transactions.

#### Constructor

```python
SlaveStatistics(window_size: int = 100)
```

#### Core Metrics

- **Transaction Counts**: `transactions_received`, `transactions_processed`, `transactions_rejected`
- **Response Statistics**: `responses_sent`, `response_errors`
- **Performance**: `average_processing_time`, `peak_processing_rate`
- **Error Conditions**: `protocol_violations`, `malformed_requests`, `buffer_overruns`, `buffer_underruns`

#### Methods

##### `record_transaction_received(bytes_count: int = 0) -> float`
Record receipt of a new transaction.

**Parameters:**
- `bytes_count`: Number of bytes in the transaction

**Returns:** Timestamp for processing time calculation

```python
stats = SlaveStatistics()
start_time = stats.record_transaction_received(bytes_count=32)
# ... process transaction ...
stats.record_transaction_processed(start_time)
```

##### `record_transaction_processed(start_time: float)`
Record successful processing of a transaction.

```python
stats.record_transaction_processed(start_time)
```

##### `record_transaction_rejected(reason: str)`
Record rejection of a transaction.

```python
stats.record_transaction_rejected("invalid_address")
stats.record_transaction_rejected("buffer_full")
```

##### `record_response_sent(success: bool = True)`
Record a response sent back to master.

```python
stats.record_response_sent(success=True)   # Successful response
stats.record_response_sent(success=False)  # Error response
```

##### `record_protocol_violation(violation_type: str)`
Record a protocol violation.

```python
stats.record_protocol_violation("invalid_command")
```

##### `record_malformed_request()`
Record a malformed request.

```python
stats.record_malformed_request()
```

##### `record_buffer_overrun()`
Record a buffer overrun condition.

```python
stats.record_buffer_overrun()
```

##### `record_buffer_underrun()`
Record a buffer underrun condition.

```python
stats.record_buffer_underrun()
```

#### Analysis Methods

##### `get_processing_rate() -> float`
Get current processing rate (transactions per second).

##### `get_average_processing_time() -> float`
Get average processing time for recent transactions.

##### `get_acceptance_rate() -> float`
Get transaction acceptance rate as percentage.

```python
acceptance_rate = stats.get_acceptance_rate()
print(f"Acceptance rate: {acceptance_rate:.1f}%")
```

##### `get_stats() -> Dict[str, Any]`
Get comprehensive statistics dictionary.

##### `reset()`
Reset all statistics to initial state.

#### String Representation

```python
print(stats)
# Output: SlaveStats: 145/150 (96.7% accepted), Processing: 1.23ms, Rate: 50.1 tps
```

## Usage Patterns

### Basic Master Usage

```python
class ProtocolMaster:
    def __init__(self):
        self.stats = MasterStatistics(window_size=200)
    
    @cocotb.coroutine
    def send_transaction(self, packet):
        # Record transaction start
        start_time = self.stats.record_transaction_start()
        
        try:
            # Send transaction
            yield self.drive_packet(packet)
            
            # Wait for completion
            yield self.wait_for_response()
            
            # Record successful completion
            bytes_sent = len(packet.data) if hasattr(packet, 'data') else 0
            self.stats.record_transaction_complete(start_time, bytes_sent)
            
        except TimeoutError:
            self.stats.record_timeout()
        except ProtocolError as e:
            self.stats.record_protocol_violation(str(e))
        except Exception as e:
            self.stats.record_transaction_failed("unknown_error", str(e))
    
    def handle_backpressure(self, cycles):
        self.stats.record_flow_control_stall(cycles)
    
    def get_performance_report(self):
        stats = self.stats.get_stats()
        return f"""
        Master Performance Report:
        Transactions: {stats['transactions_completed']}/{stats['transactions_sent']} ({stats['success_rate_percent']:.1f}% success)
        Average Latency: {stats['average_latency_ms']:.2f}ms
        Current Throughput: {stats['current_throughput_tps']:.1f} TPS
        Protocol Violations: {stats['protocol_violations']}
        Flow Control Stalls: {stats['flow_control_stalls']}
        """
```

### Basic Slave Usage

```python
class ProtocolSlave:
    def __init__(self):
        self.stats = SlaveStatistics(window_size=150)
    
    @cocotb.coroutine
    def handle_transaction(self, transaction):
        # Record transaction received
        start_time = self.stats.record_transaction_received()
        
        try:
            # Validate transaction
            if not self.validate_transaction(transaction):
                self.stats.record_malformed_request()
                return
            
            # Check if we can accept the transaction
            if self.buffer_full():
                self.stats.record_transaction_rejected("buffer_full")
                self.stats.record_response_sent(success=False)
                return
            
            # Process transaction
            response = yield self.process_transaction(transaction)
            
            # Record successful processing
            self.stats.record_transaction_processed(start_time)
            
            # Send response
            yield self.send_response(response)
            self.stats.record_response_sent(success=True)
            
        except ValidationError as e:
            self.stats.record_protocol_violation(str(e))
            self.stats.record_response_sent(success=False)
        except ProcessingError as e:
            self.stats.record_transaction_rejected(str(e))
            self.stats.record_response_sent(success=False)
    
    def get_performance_report(self):
        stats = self.stats.get_stats()
        return f"""
        Slave Performance Report:
        Transactions: {stats['transactions_processed']}/{stats['transactions_received']} ({stats['acceptance_rate_percent']:.1f}% accepted)
        Processing Time: {stats['average_processing_time_ms']:.2f}ms
        Processing Rate: {stats['processing_rate_tps']:.1f} TPS
        Protocol Violations: {stats['protocol_violations']}
        Buffer Issues: Overruns={stats['buffer_overruns']}, Underruns={stats['buffer_underruns']}
        """
```

### Advanced Performance Monitoring

```python
class PerformanceMonitor:
    def __init__(self, components):
        self.components = components
        self.monitoring = True
        
    @cocotb.coroutine
    def performance_monitor_loop(self):
        """Continuously monitor and report performance"""
        while self.monitoring:
            yield Timer(1000000, units='ns')  # Every 1ms
            
            for name, component in self.components.items():
                if hasattr(component, 'stats'):
                    component.stats.update_throughput()
                    
                    # Check for performance issues
                    self.check_performance_alerts(name, component.stats)
    
    def check_performance_alerts(self, component_name, stats):
        """Check for performance issues and generate alerts"""
        component_stats = stats.get_stats()
        
        # Check success rate
        if component_stats.get('success_rate_percent', 100) < 95:
            self.log.warning(f"{component_name}: Low success rate {component_stats['success_rate_percent']:.1f}%")
        
        # Check throughput for masters
        if isinstance(stats, MasterStatistics):
            current_tps = component_stats.get('current_throughput_tps', 0)
            if current_tps < 10:  # Below expected minimum
                self.log.warning(f"{component_name}: Low throughput {current_tps:.1f} TPS")
        
        # Check processing time for slaves
        if isinstance(stats, SlaveStatistics):
            proc_time = component_stats.get('average_processing_time_ms', 0)
            if proc_time > 100:  # Above expected maximum
                self.log.warning(f"{component_name}: High processing time {proc_time:.1f}ms")
    
    def generate_summary_report(self):
        """Generate comprehensive performance summary"""
        report = ["=== Performance Summary ==="]
        
        for name, component in self.components.items():
            if hasattr(component, 'stats'):
                stats = component.stats.get_stats()
                component_type = "Master" if isinstance(component.stats, MasterStatistics) else "Slave"
                
                report.append(f"\n{name} ({component_type}):")
                if component_type == "Master":
                    report.append(f"  Transactions: {stats['transactions_completed']}/{stats['transactions_sent']}")
                    report.append(f"  Success Rate: {stats['success_rate_percent']:.1f}%")
                    report.append(f"  Avg Latency: {stats['average_latency_ms']:.2f}ms")
                    report.append(f"  Throughput: {stats['current_throughput_tps']:.1f} TPS")
                else:
                    report.append(f"  Transactions: {stats['transactions_processed']}/{stats['transactions_received']}")
                    report.append(f"  Acceptance Rate: {stats['acceptance_rate_percent']:.1f}%")
                    report.append(f"  Processing Time: {stats['average_processing_time_ms']:.2f}ms")
                    report.append(f"  Processing Rate: {stats['processing_rate_tps']:.1f} TPS")
        
        return "\n".join(report)
```

### Statistics Comparison and Analysis

```python
def compare_performance_windows(stats, window1_start, window1_end, window2_start, window2_end):
    """Compare performance between two time windows"""
    # This would require extending the statistics classes to support
    # time-windowed analysis, but shows the concept
    
    all_stats = stats.get_stats()
    
    # Analysis would compare metrics like:
    # - Throughput differences
    # - Latency changes  
    # - Error rate variations
    # - Success rate trends
    
    comparison = {
        'window1_tps': calculate_window_throughput(window1_start, window1_end),
        'window2_tps': calculate_window_throughput(window2_start, window2_end),
        'throughput_change_percent': 0,  # Calculate percentage change
        'latency_change_ms': 0,          # Calculate latency difference
        'error_rate_change': 0           # Calculate error rate change
    }
    
    return comparison

def export_stats_to_csv(stats_dict, filename):
    """Export statistics to CSV for external analysis"""
    import csv
    
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        
        # Write header
        writer.writerow(['Metric', 'Value', 'Unit'])
        
        # Write statistics
        for key, value in stats_dict.items():
            unit = ''
            if 'latency' in key.lower() and 'ms' in key:
                unit = 'ms'
            elif 'throughput' in key.lower() or 'tps' in key:
                unit = 'transactions/sec'
            elif 'percent' in key:
                unit = '%'
            elif 'count' in key or key.endswith('s'):
                unit = 'count'
            
            writer.writerow([key, value, unit])
```

## Integration with Test Framework

### Automatic Statistics Collection

```python
@cocotb.test()
def test_with_automatic_stats(dut):
    """Test that automatically collects and reports statistics"""
    
    # Create components with statistics
    master = create_master_with_stats(dut)
    slave = create_slave_with_stats(dut)
    
    # Run test
    yield run_test_sequence(master, slave)
    
    # Collect final statistics
    master_stats = master.stats.get_stats()
    slave_stats = slave.stats.get_stats()
    
    # Generate test report
    test_report = f"""
    Test Completion Report:
    
    Master Statistics:
    - Transactions Sent: {master_stats['transactions_sent']}
    - Success Rate: {master_stats['success_rate_percent']:.1f}%
    - Average Latency: {master_stats['average_latency_ms']:.2f}ms
    - Peak Throughput: {master_stats['peak_throughput_tps']:.1f} TPS
    
    Slave Statistics:  
    - Transactions Received: {slave_stats['transactions_received']}
    - Acceptance Rate: {slave_stats['acceptance_rate_percent']:.1f}%
    - Average Processing Time: {slave_stats['average_processing_time_ms']:.2f}ms
    - Protocol Violations: {slave_stats['protocol_violations']}
    """
    
    cocotb.log.info(test_report)
    
    # Assert minimum performance requirements
    assert master_stats['success_rate_percent'] >= 95, "Master success rate too low"
    assert slave_stats['acceptance_rate_percent'] >= 95, "Slave acceptance rate too low"
    assert master_stats['average_latency_ms'] <= 10, "Master latency too high"
```

## Best Practices

### 1. **Choose Appropriate Window Sizes**
- Smaller windows (50-100) for real-time monitoring
- Larger windows (500-1000) for stable averages
- Very large windows for long-term trend analysis

### 2. **Update Throughput Regularly**
```python
# In main test loop
if cycle % 1000 == 0:  # Every 1000 cycles
    master.stats.update_throughput()
    slave.stats.update_throughput()
```

### 3. **Use Meaningful Error Categories**
```python
# Good - specific error types
stats.record_transaction_failed("address_decode_error", "Invalid address range")
stats.record_transaction_failed("timeout_exceeded", "No response after 5000 cycles")

# Avoid - generic error types  
stats.record_transaction_failed("error", "Something went wrong")
```

### 4. **Reset Statistics for Test Phases**
```python
def run_test_phase(phase_name, master, slave):
    # Reset statistics for this phase
    master.stats.reset()
    slave.stats.reset()
    
    # Run phase
    yield run_phase_operations()
    
    # Report phase results
    phase_stats = {
        'master': master.stats.get_stats(),
        'slave': slave.stats.get_stats()
    }
    
    generate_phase_report(phase_name, phase_stats)
```

### 5. **Monitor Performance Continuously**
Use the statistics classes to detect performance degradation and protocol issues in real-time during long-running tests.

The statistics classes provide essential visibility into component performance and behavior, enabling effective debugging, optimization, and verification of protocol implementations.
