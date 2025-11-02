# fifo_monitor.py

FIFO Monitor component for passive observation of FIFO transactions. Inherits from FIFOMonitorBase for unified functionality while preserving exact timing behavior and monitoring capabilities.

## Overview

The `FIFOMonitor` class provides pure monitoring functionality for FIFO interfaces without interfering with signal flow. It can monitor either the write side (master interface) or read side (slave interface) of FIFO transactions, providing comprehensive protocol violation detection and transaction analysis.

### Key Features
- **Pure Monitoring**: Observes transactions without driving any signals
- **Dual-Side Support**: Can monitor write-side or read-side operations
- **Protocol Violation Detection**: Detects read-while-empty, write-while-full, and other violations
- **FIFO Depth Tracking**: Estimates FIFO utilization and depth
- **Performance Analysis**: Tracks transaction patterns and timing
- **Rich Statistics**: Comprehensive monitoring and coverage metrics

## Core Class

### FIFOMonitor

FIFO Monitor component for passive transaction observation.

#### Constructor

```python
FIFOMonitor(dut, title, prefix, clock, field_config, is_slave=False,
            mode='fifo_mux',
            bus_name='',
            pkt_prefix='',
            multi_sig=False,
            fifo_depth=16,
            log=None, super_debug=False,
            signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix for signal naming
- `clock`: Clock signal
- `field_config`: Field configuration (FieldConfig object or dict)
- `is_slave`: If True, monitor read side; if False, monitor write side
- `mode`: FIFO mode ('fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `fifo_depth`: FIFO depth for tracking (default: 16)
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping
- `**kwargs`: Additional arguments for BusMonitor

**Example:**
```python
# Write-side monitor
write_monitor = FIFOMonitor(
    dut=dut,
    title="WriteMonitor",
    prefix="",
    clock=clock,
    field_config=field_config,
    is_slave=False  # Monitor write side
)

# Read-side monitor  
read_monitor = FIFOMonitor(
    dut=dut,
    title="ReadMonitor",
    prefix="",
    clock=clock,
    field_config=field_config,
    is_slave=True,  # Monitor read side
    fifo_depth=32   # FIFO capacity for depth tracking
)
```

## Core Methods

### FIFO Configuration

#### `set_fifo_capacity(capacity)`

Set the assumed FIFO capacity for depth tracking.

**Parameters:**
- `capacity`: FIFO capacity in entries

```python
# Set FIFO capacity for accurate depth tracking
monitor.set_fifo_capacity(64)
```

### Transaction Access

#### `get_observed_packets(count=None)`

Get observed transactions from the standard cocotb receive queue.

**Parameters:**
- `count`: Number of packets to return (None = all)

**Returns:** List of observed FIFOPacket instances

```python
# Get all observed transactions
all_packets = monitor.get_observed_packets()

# Get last 10 transactions
recent_packets = monitor.get_observed_packets(count=10)

# Process observed transactions
for packet in all_packets:
    print(f"Monitored: {packet.formatted()}")
```

#### `clear_queue()`

Clear the observed transactions queue.

```python
# Clear accumulated observations
monitor.clear_queue()
```

#### `create_packet(**field_values)`

Create a packet with specified field values for comparison.

**Parameters:**
- `**field_values`: Field values to set in packet

**Returns:** FIFOPacket instance

```python
# Create packet for expected value comparison
expected = monitor.create_packet(data=0x12345678)
```

### Statistics and Analysis

#### `get_stats()`

Get comprehensive statistics including monitoring and FIFO-specific metrics.

**Returns:** Dictionary containing all statistics

```python
stats = monitor.get_stats()

# Monitor statistics
monitor_stats = stats['monitor_stats']
print(f"Transactions observed: {monitor_stats['transactions_observed']}")
print(f"Protocol violations: {monitor_stats['protocol_violations']}")
print(f"Read while empty: {monitor_stats['read_while_empty']}")
print(f"Write while full: {monitor_stats['write_while_full']}")

# FIFO-specific statistics
print(f"Monitor type: {stats['monitor_type']}")
print(f"FIFO depth estimate: {stats['fifo_depth_estimate']}")
print(f"FIFO capacity: {stats['fifo_capacity']}")
print(f"Utilization: {stats['utilization_percentage']:.1f}%")
```

## Monitoring Modes

### Write-Side Monitoring (`is_slave=False`)

Monitors the write interface of a FIFO:

```python
# Write-side monitor observes:
# - write signal assertions
# - full signal conditions  
# - write data values
# - write-while-full violations

write_monitor = FIFOMonitor(
    dut=dut,
    title="WriteMonitor", 
    prefix="",
    clock=clock,
    field_config=field_config,
    is_slave=False
)

# Signals monitored: write, full, data (and field signals if multi_sig=True)
```

### Read-Side Monitoring (`is_slave=True`)

Monitors the read interface of a FIFO:

```python
# Read-side monitor observes:
# - read signal assertions
# - empty signal conditions
# - read data values  
# - read-while-empty violations

read_monitor = FIFOMonitor(
    dut=dut,
    title="ReadMonitor",
    prefix="",
    clock=clock, 
    field_config=field_config,
    is_slave=True
)

# Signals monitored: read, empty, data (and field signals if multi_sig=True)
```

## Usage Patterns

### Basic Transaction Monitoring

```python
# Set up write and read monitors
field_config = FieldConfig.create_data_only(32)

write_monitor = FIFOMonitor(dut, "WriteMonitor", "", clock, field_config, is_slave=False)
read_monitor = FIFOMonitor(dut, "ReadMonitor", "", clock, field_config, is_slave=True)

# Let test run for a while
await Timer(10000, 'ns')

# Analyze observed transactions
write_packets = write_monitor.get_observed_packets()
read_packets = read_monitor.get_observed_packets()

print(f"Observed {len(write_packets)} writes, {len(read_packets)} reads")

# Verify FIFO behavior
assert len(write_packets) >= len(read_packets), "More reads than writes detected"
```

### Protocol Violation Detection

```python
class ProtocolChecker:
    def __init__(self, dut, clock, field_config):
        self.write_monitor = FIFOMonitor(
            dut, "WriteChecker", "", clock, field_config, 
            is_slave=False, fifo_depth=16
        )
        self.read_monitor = FIFOMonitor(
            dut, "ReadChecker", "", clock, field_config,
            is_slave=True, fifo_depth=16
        )
        
    async def check_protocol_compliance(self, duration_ns=50000):
        """Check for protocol violations over specified duration"""
        start_time = cocotb.utils.get_sim_time('ns')
        violations = []
        
        while cocotb.utils.get_sim_time('ns') - start_time < duration_ns:
            await Timer(100, 'ns')
            
            # Check write side violations
            write_stats = self.write_monitor.get_stats()
            if write_stats['monitor_stats']['write_while_full'] > 0:
                violations.append({
                    'type': 'write_while_full',
                    'count': write_stats['monitor_stats']['write_while_full'],
                    'time': cocotb.utils.get_sim_time('ns'),
                    'side': 'write'
                })
            
            # Check read side violations
            read_stats = self.read_monitor.get_stats() 
            if read_stats['monitor_stats']['read_while_empty'] > 0:
                violations.append({
                    'type': 'read_while_empty',
                    'count': read_stats['monitor_stats']['read_while_empty'],
                    'time': cocotb.utils.get_sim_time('ns'),
                    'side': 'read'
                })
        
        return violations
    
    def generate_compliance_report(self, violations):
        """Generate detailed compliance report"""
        write_stats = self.write_monitor.get_stats()
        read_stats = self.read_monitor.get_stats()
        
        report = f"""
        FIFO Protocol Compliance Report:
        ================================
        
        Write Side:
        - Transactions observed: {write_stats['monitor_stats']['transactions_observed']}
        - Protocol violations: {write_stats['monitor_stats']['protocol_violations']}
        - Write while full: {write_stats['monitor_stats']['write_while_full']}
        - FIFO utilization: {write_stats['utilization_percentage']:.1f}%
        
        Read Side:
        - Transactions observed: {read_stats['monitor_stats']['transactions_observed']}
        - Protocol violations: {read_stats['monitor_stats']['protocol_violations']}
        - Read while empty: {read_stats['monitor_stats']['read_while_empty']}
        - FIFO utilization: {read_stats['utilization_percentage']:.1f}%
        
        Violations Timeline:
        """
        
        for violation in violations:
            report += f"\n  {violation['time']}ns: {violation['type']} on {violation['side']} side"
        
        return report

# Usage
checker = ProtocolChecker(dut, clock, field_config)
violations = await checker.check_protocol_compliance(duration_ns=100000)
print(checker.generate_compliance_report(violations))
```

### FIFO Depth and Utilization Analysis

```python
class FIFOAnalyzer:
    def __init__(self, dut, clock, field_config, fifo_capacity):
        self.write_monitor = FIFOMonitor(
            dut, "WriteAnalyzer", "", clock, field_config,
            is_slave=False, fifo_depth=fifo_capacity
        )
        self.read_monitor = FIFOMonitor(
            dut, "ReadAnalyzer", "", clock, field_config,
            is_slave=True, fifo_depth=fifo_capacity
        )
        self.capacity = fifo_capacity
        self.utilization_history = []
        
    async def analyze_utilization(self, duration_ns=20000, sample_interval_ns=200):
        """Analyze FIFO utilization over time"""
        start_time = cocotb.utils.get_sim_time('ns')
        
        while cocotb.utils.get_sim_time('ns') - start_time < duration_ns:
            current_time = cocotb.utils.get_sim_time('ns')
            
            # Get current utilization from both sides
            write_stats = self.write_monitor.get_stats()
            read_stats = self.read_monitor.get_stats()
            
            self.utilization_history.append({
                'time': current_time,
                'write_utilization': write_stats['utilization_percentage'],
                'read_utilization': read_stats['utilization_percentage'],
                'write_depth': write_stats['fifo_depth_estimate'],
                'read_depth': read_stats['fifo_depth_estimate']
            })
            
            await Timer(sample_interval_ns, 'ns')
        
        return self.analyze_utilization_patterns()
    
    def analyze_utilization_patterns(self):
        """Analyze utilization patterns"""
        if not self.utilization_history:
            return {}
        
        write_utils = [h['write_utilization'] for h in self.utilization_history]
        read_utils = [h['read_utilization'] for h in self.utilization_history]
        
        return {
            'max_write_utilization': max(write_utils),
            'avg_write_utilization': sum(write_utils) / len(write_utils),
            'max_read_utilization': max(read_utils), 
            'avg_read_utilization': sum(read_utils) / len(read_utils),
            'peak_depth_estimate': max(h['write_depth'] for h in self.utilization_history),
            'utilization_samples': len(self.utilization_history)
        }
    
    def detect_congestion_events(self, threshold_percent=80):
        """Detect high utilization events"""
        congestion_events = []
        
        for sample in self.utilization_history:
            if (sample['write_utilization'] > threshold_percent or 
                sample['read_utilization'] > threshold_percent):
                congestion_events.append(sample)
        
        return congestion_events

# Usage
analyzer = FIFOAnalyzer(dut, clock, field_config, fifo_capacity=32)
utilization_analysis = await analyzer.analyze_utilization(duration_ns=50000)
congestion = analyzer.detect_congestion_events(threshold_percent=75)

print(f"Utilization analysis: {utilization_analysis}")
print(f"Congestion events: {len(congestion)}")
```

### Multi-Field Transaction Analysis

```python
# Configure multi-field monitoring
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex", encoding={
    0: "NOP", 1: "READ", 2: "WRITE", 3: "BURST"
}))

# Create monitor with multi-signal mode
monitor = FIFOMonitor(
    dut=dut,
    title="MultiFieldMonitor",
    prefix="",
    clock=clock,
    field_config=field_config,
    is_slave=False,  # Monitor write side
    multi_sig=True   # Each field has individual signal
)

# Analyze transaction patterns
await Timer(15000, 'ns')
packets = monitor.get_observed_packets()

# Analyze command distribution
command_stats = {}
for packet in packets:
    cmd = getattr(packet, 'cmd', 0)
    command_stats[cmd] = command_stats.get(cmd, 0) + 1

print("Command distribution:")
for cmd, count in command_stats.items():
    cmd_name = field_config.get_field('cmd').encoding.get(cmd, f"UNKNOWN_{cmd}")
    print(f"  {cmd_name}: {count} transactions")

# Analyze address patterns
addresses = [getattr(p, 'addr', 0) for p in packets if hasattr(p, 'addr')]
if addresses:
    print(f"Address range: 0x{min(addresses):X} - 0x{max(addresses):X}")
    print(f"Unique addresses: {len(set(addresses))}")
```

### Performance Monitoring

```python
class PerformanceMonitor:
    def __init__(self, dut, clock, field_config):
        self.write_monitor = FIFOMonitor(
            dut, "WritePerfMonitor", "", clock, field_config, is_slave=False
        )
        self.read_monitor = FIFOMonitor(
            dut, "ReadPerfMonitor", "", clock, field_config, is_slave=True
        )
        self.performance_log = []
        
    async def monitor_performance(self, duration_ns=25000):
        """Monitor performance metrics over time"""
        start_time = cocotb.utils.get_sim_time('ns')
        last_write_count = 0
        last_read_count = 0
        
        while cocotb.utils.get_sim_time('ns') - start_time < duration_ns:
            current_time = cocotb.utils.get_sim_time('ns')
            
            # Get current transaction counts
            write_packets = len(self.write_monitor.get_observed_packets())
            read_packets = len(self.read_monitor.get_observed_packets())
            
            # Calculate rates
            time_delta_ns = 1000  # Sample interval
            write_rate = (write_packets - last_write_count) / (time_delta_ns / 1e9)
            read_rate = (read_packets - last_read_count) / (time_delta_ns / 1e9)
            
            self.performance_log.append({
                'time': current_time,
                'write_count': write_packets,
                'read_count': read_packets,
                'write_rate_tps': write_rate,
                'read_rate_tps': read_rate
            })
            
            last_write_count = write_packets
            last_read_count = read_packets
            
            await Timer(1000, 'ns')  # Sample every 1us
        
        return self.analyze_performance()
    
    def analyze_performance(self):
        """Analyze collected performance data"""
        if not self.performance_log:
            return {}
        
        write_rates = [p['write_rate_tps'] for p in self.performance_log]
        read_rates = [p['read_rate_tps'] for p in self.performance_log]
        
        final_entry = self.performance_log[-1]
        
        return {
            'total_write_transactions': final_entry['write_count'],
            'total_read_transactions': final_entry['read_count'],
            'peak_write_rate_tps': max(write_rates),
            'peak_read_rate_tps': max(read_rates),
            'avg_write_rate_tps': sum(write_rates) / len(write_rates),
            'avg_read_rate_tps': sum(read_rates) / len(read_rates),
            'fifo_efficiency': final_entry['read_count'] / max(final_entry['write_count'], 1)
        }

# Usage
perf_monitor = PerformanceMonitor(dut, clock, field_config)
performance = await perf_monitor.monitor_performance(duration_ns=100000)
print(f"Performance metrics: {performance}")
```

### Real-Time Transaction Callbacks

```python
class CallbackMonitor:
    def __init__(self, dut, clock, field_config):
        self.monitor = FIFOMonitor(dut, "CallbackMonitor", "", clock, field_config)
        self.transaction_log = []
        
        # Add callback for real-time processing
        self.monitor.add_callback(self.process_transaction)
        
    def process_transaction(self, packet):
        """Process transactions in real-time as they're observed"""
        timestamp = cocotb.utils.get_sim_time('ns')
        
        # Log transaction with timestamp
        log_entry = {
            'timestamp': timestamp,
            'packet': packet,
            'data': getattr(packet, 'data', None)
        }
        self.transaction_log.append(log_entry)
        
        # Real-time analysis
        if hasattr(packet, 'data') and packet.data == 0xDEADBEEF:
            log.info(f"Special marker packet detected at {timestamp}ns")
        
        # Trigger alerts for specific patterns
        if len(self.transaction_log) > 100:
            recent_data = [entry['data'] for entry in self.transaction_log[-10:]]
            if all(d == recent_data[0] for d in recent_data):
                log.warning(f"Repeated data pattern detected: 0x{recent_data[0]:X}")
    
    def get_transaction_timeline(self):
        """Get detailed transaction timeline"""
        return [
            f"{entry['timestamp']}ns: {entry['packet'].formatted()}"
            for entry in self.transaction_log
        ]

# Usage
callback_monitor = CallbackMonitor(dut, clock, field_config)
# Monitor automatically processes transactions as they occur
await Timer(20000, 'ns')
timeline = callback_monitor.get_transaction_timeline()
```

## Error Detection

### Automatic Protocol Violation Detection

The FIFOMonitor automatically detects various protocol violations:

```python
# Check for violations after test run
stats = monitor.get_stats()
monitor_stats = stats['monitor_stats']

# Protocol violations
if monitor_stats['protocol_violations'] > 0:
    log.error(f"Protocol violations detected: {monitor_stats['protocol_violations']}")

# Specific violation types
if monitor_stats['write_while_full'] > 0:
    log.error(f"Write-while-full violations: {monitor_stats['write_while_full']}")

if monitor_stats['read_while_empty'] > 0:
    log.error(f"Read-while-empty violations: {monitor_stats['read_while_empty']}")

# X/Z signal violations
if monitor_stats['x_z_violations'] > 0:
    log.error(f"X/Z signal violations: {monitor_stats['x_z_violations']}")
```

### Custom Violation Checking

```python
def check_custom_violations(monitor, packets):
    """Check for custom protocol violations"""
    violations = []
    
    # Check for data pattern violations
    for i, packet in enumerate(packets):
        if hasattr(packet, 'data'):
            if packet.data & 0x80000000:  # MSB should never be set
                violations.append(f"MSB violation in packet {i}: 0x{packet.data:X}")
    
    # Check for timing violations
    if len(packets) > 1:
        for i in range(1, len(packets)):
            if hasattr(packets[i], 'start_time') and hasattr(packets[i-1], 'start_time'):
                time_diff = packets[i].start_time - packets[i-1].start_time
                if time_diff < 100:  # Minimum 100ns between transactions
                    violations.append(f"Timing violation between packets {i-1} and {i}: {time_diff}ns")
    
    return violations

# Usage
packets = monitor.get_observed_packets()
custom_violations = check_custom_violations(monitor, packets)
if custom_violations:
    for violation in custom_violations:
        log.warning(f"Custom violation: {violation}")
```

## Best Practices

### 1. **Use Appropriate Side Monitoring**
```python
# Monitor write side for write-related issues
write_monitor = FIFOMonitor(dut, "WriteMonitor", "", clock, field_config, is_slave=False)

# Monitor read side for read-related issues
read_monitor = FIFOMonitor(dut, "ReadMonitor", "", clock, field_config, is_slave=True)
```

### 2. **Set Correct FIFO Capacity**
```python
# Set accurate FIFO capacity for depth tracking
monitor.set_fifo_capacity(actual_fifo_depth)
```

### 3. **Use Callbacks for Real-Time Analysis**
```python
# Add callback for immediate processing
monitor.add_callback(real_time_processor)
```

### 4. **Regular Statistics Checking**
```python
# Check statistics periodically
async def periodic_check():
    while True:
        await Timer(10000, 'ns')
        stats = monitor.get_stats()
        if stats['monitor_stats']['protocol_violations'] > 0:
            log.warning("New protocol violations detected")
```

### 5. **Clear Queues Between Test Phases**
```python
# Reset between test phases
monitor.clear_queue()
```

The FIFOMonitor provides comprehensive passive monitoring capabilities with automatic protocol violation detection, performance analysis, and flexible configuration options for thorough FIFO interface verification.
