# fifo_slave.py

FIFO Slave component for reading transactions from FIFO interfaces. Inherits from FIFOMonitorBase for unified functionality while preserving exact API and timing behavior.

## Overview

The `FIFOSlave` class combines monitoring capabilities with active read signal control to consume transactions from FIFO interfaces. It observes transactions like a monitor while actively driving read signals to control data flow, making it ideal for modeling FIFO consumers.

### Key Features
- **Active Read Control**: Drives read signals with configurable timing and delays
- **Transaction Monitoring**: Observes and processes incoming transactions
- **Flow Control**: Handles FIFO empty conditions with backpressure support
- **Memory Integration**: Built-in memory model support for data storage
- **Protocol Violation Detection**: Detects read-while-empty and other issues
- **Flexible Timing**: Configurable read delays with randomization support

## Core Class

### FIFOSlave

FIFO Slave component for reading transactions from FIFO interfaces.

#### Constructor

```python
FIFOSlave(dut, title, prefix, clock, field_config,
          timeout_cycles=1000, mode='fifo_mux',
          bus_name='',
          pkt_prefix='',
          multi_sig=False,
          randomizer=None, log=None, super_debug=False,
          signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix for signal naming
- `clock`: Clock signal
- `field_config`: Field configuration (FieldConfig object or dict)
- `timeout_cycles`: Timeout for operations (default: 1000)
- `mode`: FIFO mode ('fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for read delays
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping
- `**kwargs`: Additional arguments for BusMonitor

**Example:**
```python
# Basic FIFO slave
slave = FIFOSlave(
    dut=dut,
    title="ReadSlave",
    prefix="",
    clock=clock,
    field_config=field_config
)

# Advanced configuration
slave = FIFOSlave(
    dut=dut,
    title="AdvancedSlave",
    prefix="",
    clock=clock,
    field_config=field_config,
    timeout_cycles=2000,
    mode='fifo_flop',
    multi_sig=True,
    randomizer=custom_randomizer,
    signal_map={'read': 'rd_en', 'empty': 'fifo_empty'}
)
```

## Core Methods

### Bus Control

#### `async reset_bus()`

Reset the bus and clear all queued transactions.

```python
# Reset slave and clear state
await slave.reset_bus()
```

#### `async wait_cycles(cycles)`

Wait for specified number of clock cycles.

**Parameters:**
- `cycles`: Number of cycles to wait

```python
# Wait for 5 cycles
await slave.wait_cycles(5)
```

### Transaction Access

#### `get_observed_packets(count=None)`

Get observed transactions from the standard cocotb receive queue.

**Parameters:**
- `count`: Number of packets to return (None = all)

**Returns:** List of observed FIFOPacket instances

```python
# Get all observed transactions
all_packets = slave.get_observed_packets()

# Get last 5 transactions
recent_packets = slave.get_observed_packets(count=5)

# Process observed transactions
for packet in all_packets:
    print(f"Received: {packet.formatted()}")
```

#### `clear_queue()`

Clear the observed transactions queue.

```python
# Clear accumulated transactions
slave.clear_queue()
```

#### `create_packet(**field_values)`

Create a packet with specified field values.

**Parameters:**
- `**field_values`: Field values to set in packet

**Returns:** FIFOPacket instance

```python
# Create packet for comparison
expected = slave.create_packet(data=0x12345678)
```

### Memory Operations

#### `handle_memory_write(packet)`

Handle memory write using integrated memory model.

**Parameters:**
- `packet`: Packet to write to memory

**Returns:** True if successful, False otherwise

```python
# Automatically called during transaction processing
# Can also be called manually
success = slave.handle_memory_write(packet)
```

#### `handle_memory_read(packet)`

Handle memory read using integrated memory model.

**Parameters:**
- `packet`: Packet with address to read from

**Returns:** Tuple of (success, data)

```python
# Read from memory
success, data = slave.handle_memory_read(packet)
if success:
    log.info(f"Read data: 0x{data:X}")
```

### Statistics and Monitoring

#### `get_stats()`

Get comprehensive statistics including base and monitoring statistics.

**Returns:** Dictionary containing all statistics

```python
stats = slave.get_stats()

# Monitor statistics
monitor_stats = stats['monitor_stats']
print(f"Transactions received: {monitor_stats['received_transactions']}")
print(f"Transactions observed: {monitor_stats['transactions_observed']}")
print(f"Protocol violations: {monitor_stats['protocol_violations']}")
print(f"Read while empty: {monitor_stats['read_while_empty']}")

# Component statistics
print(f"Observed packets: {stats['observed_packets']}")
print(f"Component type: {stats['component_type']}")
```

## Operational Modes

### FIFO_MUX Mode

In `fifo_mux` mode, data is captured in the same cycle as the read:

```python
slave = FIFOSlave(dut, "MuxSlave", "", clock, field_config, mode='fifo_mux')

# Data captured immediately when read=1 and empty=0
# Timeline: read=1 -> data captured same cycle
```

### FIFO_FLOP Mode  

In `fifo_flop` mode, data is captured in the cycle following the read:

```python
slave = FIFOSlave(dut, "FlopSlave", "", clock, field_config, mode='fifo_flop')

# Data captured one cycle after read assertion
# Timeline: read=1 -> wait 1 cycle -> data captured
```

## Usage Patterns

### Basic Read Operations

```python
# Set up slave
field_config = FieldConfig.create_data_only(32)
slave = FIFOSlave(dut, "Slave", "", clock, field_config)

# Start monitoring (automatic in background)
# Slave automatically drives read signals and captures data

# Access observed transactions
await Timer(1000, 'ns')  # Let some transactions occur
packets = slave.get_observed_packets()
for packet in packets:
    print(f"Received data: 0x{packet.data:X}")
```

### Multi-Field Transaction Processing

```python
# Configure multi-field packets
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex"))

# Create slave with multi-signal mode
slave = FIFOSlave(
    dut=dut,
    title="MultiFieldSlave",
    prefix="",
    clock=clock,
    field_config=field_config,
    multi_sig=True
)

# Process complex transactions
await Timer(1000, 'ns')
packets = slave.get_observed_packets()
for packet in packets:
    print(f"Command: {packet.cmd}, Address: 0x{packet.addr:X}, Data: 0x{packet.data:X}")
    
    # Process based on command
    if packet.cmd == 1:  # READ
        print("Processing read command")
    elif packet.cmd == 2:  # WRITE
        print("Processing write command")
```

### Randomized Read Timing

```python
# Create randomizer for read delays
read_randomizer = FlexRandomizer({
    'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
})

# Create slave with randomized timing
slave = FIFOSlave(
    dut=dut,
    title="RandomSlave",
    prefix="",
    clock=clock,
    field_config=field_config,
    randomizer=read_randomizer
)

# Reads will have randomized delays between transactions
```

### Memory-Integrated Processing

```python
# Set up memory model
memory = MemoryModel(num_lines=256, bytes_per_line=4)

# Create slave with memory integration
slave = FIFOSlave(
    dut=dut,
    title="MemorySlave",
    prefix="",
    clock=clock,
    field_config=field_config,
    memory_model=memory
)

# Transactions automatically stored in memory
await Timer(2000, 'ns')

# Verify memory contents
packets = slave.get_observed_packets()
for packet in packets:
    if hasattr(packet, 'addr') and hasattr(packet, 'data'):
        # Verify memory write occurred
        success, stored_data = slave.handle_memory_read(packet)
        assert success and stored_data == packet.data
```

### Real-Time Transaction Processing

```python
class ProcessingSlave:
    def __init__(self, dut, clock, field_config):
        self.slave = FIFOSlave(dut, "ProcessingSlave", "", clock, field_config)
        self.processed_count = 0
        
        # Add callback for real-time processing
        self.slave.add_callback(self.process_transaction)
        
    def process_transaction(self, packet):
        """Process transactions as they arrive"""
        self.processed_count += 1
        
        # Real-time processing
        if hasattr(packet, 'cmd'):
            if packet.cmd == 1:  # READ command
                self.handle_read_request(packet)
            elif packet.cmd == 2:  # WRITE command
                self.handle_write_request(packet)
        
        log.info(f"Processed transaction {self.processed_count}: {packet.formatted()}")
    
    def handle_read_request(self, packet):
        """Handle read request"""
        if hasattr(packet, 'addr'):
            log.info(f"Read request for address 0x{packet.addr:X}")
            # Process read...
    
    def handle_write_request(self, packet):
        """Handle write request"""
        if hasattr(packet, 'addr') and hasattr(packet, 'data'):
            log.info(f"Write request: 0x{packet.data:X} -> 0x{packet.addr:X}")
            # Process write...

# Usage
processor = ProcessingSlave(dut, clock, field_config)
# Transactions processed automatically as they arrive
```

### Error Detection and Monitoring

```python
class MonitoringSlave:
    def __init__(self, dut, clock, field_config):
        self.slave = FIFOSlave(
            dut=dut,
            title="MonitoringSlave", 
            prefix="",
            clock=clock,
            field_config=field_config
        )
        self.error_log = []
        
    async def monitor_with_error_detection(self, duration_ns=10000):
        """Monitor for specified duration with error checking"""
        start_time = cocotb.utils.get_sim_time('ns')
        
        while cocotb.utils.get_sim_time('ns') - start_time < duration_ns:
            await Timer(100, 'ns')
            
            # Check for protocol violations
            stats = self.slave.get_stats()
            monitor_stats = stats['monitor_stats']
            
            if monitor_stats['protocol_violations'] > 0:
                self.error_log.append({
                    'type': 'protocol_violation',
                    'count': monitor_stats['protocol_violations'],
                    'time': cocotb.utils.get_sim_time('ns')
                })
            
            if monitor_stats['read_while_empty'] > 0:
                self.error_log.append({
                    'type': 'read_while_empty',
                    'count': monitor_stats['read_while_empty'],
                    'time': cocotb.utils.get_sim_time('ns')
                })
        
        return self.error_log
    
    def generate_error_report(self):
        """Generate comprehensive error report"""
        stats = self.slave.get_stats()
        
        report = f"""
        Slave Error Report:
        ==================
        Total Transactions: {stats['monitor_stats']['transactions_observed']}
        Protocol Violations: {stats['monitor_stats']['protocol_violations']}
        Read While Empty: {stats['monitor_stats']['read_while_empty']}
        X/Z Violations: {stats['monitor_stats']['x_z_violations']}
        
        Error Timeline:
        """
        
        for error in self.error_log:
            report += f"\n  {error['time']}ns: {error['type']} (count: {error['count']})"
        
        return report

# Usage
monitor = MonitoringSlave(dut, clock, field_config)
await monitor.monitor_with_error_detection(duration_ns=50000)
print(monitor.generate_error_report())
```

### High-Performance Data Collection

```python
class HighPerformanceSlave:
    def __init__(self, dut, clock, field_config):
        # Configure for maximum performance
        self.slave = FIFOSlave(
            dut=dut,
            title="HighPerfSlave",
            prefix="",
            clock=clock,
            field_config=field_config,
            super_debug=False  # Disable debug for performance
        )
        self.collection_buffer = []
        
    async def fast_collection(self, target_count=1000):
        """High-speed data collection"""
        collected = 0
        start_time = time.time()
        
        while collected < target_count:
            await Timer(10, 'ns')  # Minimal wait
            
            # Check for new transactions
            current_packets = self.slave.get_observed_packets()
            if len(current_packets) > collected:
                # New transactions available
                new_packets = current_packets[collected:]
                self.collection_buffer.extend(new_packets)
                collected = len(current_packets)
        
        end_time = time.time()
        duration = end_time - start_time
        rate = target_count / duration
        
        log.info(f"Collected {target_count} transactions in {duration:.2f}s ({rate:.1f} TPS)")
        return self.collection_buffer
    
    def analyze_collected_data(self):
        """Analyze collected transaction data"""
        if not self.collection_buffer:
            return {}
        
        data_values = [p.data for p in self.collection_buffer if hasattr(p, 'data')]
        
        analysis = {
            'count': len(self.collection_buffer),
            'unique_data_values': len(set(data_values)),
            'data_range': (min(data_values), max(data_values)) if data_values else (0, 0),
            'average_data': sum(data_values) / len(data_values) if data_values else 0
        }
        
        return analysis

# Usage
collector = HighPerformanceSlave(dut, clock, field_config)
await collector.fast_collection(target_count=5000)
analysis = collector.analyze_collected_data()
print(f"Collection analysis: {analysis}")
```

### Custom Signal Mapping

```python
# For non-standard FIFO interfaces
def create_custom_slave(dut, clock, custom_signals):
    """Create slave with custom signal naming"""
    
    # Map custom signals to expected names
    signal_map = {
        'read': custom_signals.get('read_enable', 'read'),
        'empty': custom_signals.get('empty_flag', 'empty'),
        'data': custom_signals.get('read_data', 'data')
    }
    
    # Create field configuration
    field_config = FieldConfig.create_data_only(32)
    
    # Create slave with custom mapping
    slave = FIFOSlave(
        dut=dut,
        title="CustomSlave",
        prefix="",
        clock=clock,
        field_config=field_config,
        signal_map=signal_map,
        super_debug=True  # Enable for signal mapping debugging
    )
    
    return slave

# Usage with custom interface
custom_signals = {
    'read_enable': 'rd_en',
    'empty_flag': 'fifo_empty',
    'read_data': 'dout'
}
slave = create_custom_slave(dut, clock, custom_signals)
```

## Protocol Violation Detection

The FIFOSlave automatically detects and reports various protocol violations:

### Read While Empty

```python
# Automatically detected and logged
stats = slave.get_stats()
read_while_empty_count = stats['monitor_stats']['read_while_empty']

if read_while_empty_count > 0:
    log.warning(f"Detected {read_while_empty_count} read-while-empty violations")
```

### X/Z Signal Values

```python
# X/Z values in signals automatically detected
stats = slave.get_stats()
xz_violations = stats['monitor_stats']['x_z_violations']

if xz_violations > 0:
    log.warning(f"Detected {xz_violations} X/Z signal violations")
```

## Timing Analysis

### Read Timing Patterns

```python
class TimingAnalyzer:
    def __init__(self, slave):
        self.slave = slave
        self.timing_data = []
        
    async def analyze_read_timing(self, duration_ns=10000):
        """Analyze read signal timing patterns"""
        start_time = cocotb.utils.get_sim_time('ns')
        last_packet_count = 0
        
        while cocotb.utils.get_sim_time('ns') - start_time < duration_ns:
            current_time = cocotb.utils.get_sim_time('ns')
            current_packets = len(self.slave.get_observed_packets())
            
            if current_packets > last_packet_count:
                # New transaction detected
                self.timing_data.append({
                    'time': current_time,
                    'transaction_count': current_packets
                })
                last_packet_count = current_packets
            
            await Timer(50, 'ns')
        
        return self.analyze_intervals()
    
    def analyze_intervals(self):
        """Analyze time intervals between transactions"""
        if len(self.timing_data) < 2:
            return {}
        
        intervals = []
        for i in range(1, len(self.timing_data)):
            interval = self.timing_data[i]['time'] - self.timing_data[i-1]['time']
            intervals.append(interval)
        
        return {
            'total_transactions': len(self.timing_data),
            'average_interval_ns': sum(intervals) / len(intervals),
            'min_interval_ns': min(intervals),
            'max_interval_ns': max(intervals),
            'intervals': intervals
        }

# Usage
analyzer = TimingAnalyzer(slave)
timing_analysis = await analyzer.analyze_read_timing(duration_ns=20000)
print(f"Timing analysis: {timing_analysis}")
```

## Best Practices

### 1. **Use Appropriate Mode for Interface**
```python
# For combinatorial FIFO outputs
slave = FIFOSlave(dut, "CombSlave", "", clock, field_config, mode='fifo_mux')

# For registered FIFO outputs  
slave = FIFOSlave(dut, "RegSlave", "", clock, field_config, mode='fifo_flop')
```

### 2. **Monitor Error Conditions**
```python
# Regular error checking
async def check_slave_health(slave):
    stats = slave.get_stats()
    monitor_stats = stats['monitor_stats']
    
    assert monitor_stats['protocol_violations'] == 0, "Protocol violations detected"
    assert monitor_stats['x_z_violations'] == 0, "X/Z signal violations detected"
```

### 3. **Use Memory Integration for Verification**
```python
# Enable memory model for data verification
memory = MemoryModel(num_lines=1024, bytes_per_line=4)
slave = FIFOSlave(dut, "VerifySlave", "", clock, field_config, memory_model=memory)
```

### 4. **Configure Appropriate Randomizers**
```python
# For realistic read patterns
realistic_randomizer = FlexRandomizer({
    'read_delay': ([(0, 1), (2, 5)], [8, 2])  # Mostly quick reads
})

# For stress testing
stress_randomizer = FlexRandomizer({
    'read_delay': ([(0, 10), (20, 100)], [1, 1])  # Variable delays
})
```

### 5. **Clear Queues Between Test Phases**
```python
# Reset state between test phases
await slave.reset_bus()
slave.clear_queue()
```

The FIFOSlave provides comprehensive transaction monitoring and read control capabilities with automatic error detection, performance tracking, and flexible timing control for thorough FIFO interface verification.
