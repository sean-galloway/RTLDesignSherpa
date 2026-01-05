<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# fifo_master.py

FIFO Master component for driving write transactions into FIFO interfaces. Inherits from FIFOComponentBase for unified functionality while preserving exact API and timing behavior.

## Overview

The `FIFOMaster` class is a high-performance transaction driver that writes data to FIFO interfaces. It combines cocotb's BusDriver functionality with the shared infrastructure from FIFOComponentBase to provide optimized signal handling, memory integration, and comprehensive statistics.

### Key Features
- **High-Performance Writing**: Optimized transaction queuing and pipeline management
- **Flow Control**: Automatic handling of FIFO full conditions with backpressure support
- **Timing Control**: Configurable write delays with randomization support
- **Memory Integration**: Built-in memory model support for data verification
- **Rich Statistics**: Comprehensive performance tracking and error detection
- **Flexible Configuration**: Support for both single-signal and multi-signal modes

## Core Class

### FIFOMaster

FIFO Master component for driving write transactions.

#### Constructor

```python
FIFOMaster(dut, title, prefix, clock, field_config,
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
- `timeout_cycles`: Timeout for waiting for FIFO not full (default: 1000)
- `mode`: FIFO mode ('fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for write delays
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping
- `**kwargs`: Additional arguments for BusDriver

**Example:**
```python
# Basic FIFO master
master = FIFOMaster(
    dut=dut,
    title="WriteMaster",
    prefix="",
    clock=clock,
    field_config=field_config
)

# Advanced configuration
master = FIFOMaster(
    dut=dut,
    title="AdvancedMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    timeout_cycles=2000,
    mode='fifo_flop',
    multi_sig=True,
    randomizer=custom_randomizer,
    signal_map={'write': 'wr_en', 'full': 'fifo_full'}
)
```

## Core Methods

### Transaction Management

#### `async send(packet)`

Modern send interface for sending a single packet.

**Parameters:**
- `packet`: FIFOPacket to send

**Returns:** True when transaction completes

```python
# Create and send packet
packet = master.create_packet(data=0xDEADBEEF)
await master.send(packet)
```

#### `async busy_send(transaction)`

Send a transaction and wait for completion.

**Parameters:**
- `transaction`: Transaction packet to send

```python
# Send with completion waiting
packet = FIFOPacket(field_config, addr=0x1000, data=0x12345678)
await master.busy_send(packet)
```

#### `create_packet(**field_values)`

Create a packet with specified field values.

**Parameters:**
- `**field_values`: Field values to set in packet

**Returns:** FIFOPacket instance with specified values

```python
# Create packet with multiple fields
packet = master.create_packet(
    addr=0x1000,
    data=0xDEADBEEF,
    cmd=0x2
)

# Create simple data packet
packet = master.create_packet(data=0x12345678)
```

### Bus Control

#### `async reset_bus()`

Reset the bus to a known state.

```python
# Reset master and clear queues
await master.reset_bus()
```

#### `async wait_cycles(cycles)`

Wait for specified number of clock cycles.

**Parameters:**
- `cycles`: Number of cycles to wait

```python
# Wait for 10 cycles
await master.wait_cycles(10)
```

### Memory Operations

#### `async write_to_memory(packet)`

Write packet to memory using integrated memory model.

**Parameters:**
- `packet`: Packet to write to memory

**Returns:** True if successful, False otherwise

```python
# Write to memory
packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
success = await master.write_to_memory(packet)
if success:
    log.info("Memory write successful")
```

#### `async read_from_memory(packet)`

Read data from memory using integrated memory model.

**Parameters:**
- `packet`: Packet with address to read from

**Returns:** Tuple of (success, data)

```python
# Read from memory
packet = master.create_packet(addr=0x1000)
success, data = await master.read_from_memory(packet)
if success:
    log.info(f"Read data: 0x{data:X}")
```

### Statistics and Monitoring

#### `get_stats()`

Get comprehensive statistics including master-specific and base statistics.

**Returns:** Dictionary containing all statistics

```python
stats = master.get_stats()

# Master-specific statistics
master_stats = stats['master_stats']
print(f"Transactions sent: {master_stats['transactions_sent']}")
print(f"Success rate: {master_stats['success_rate_percent']:.1f}%")
print(f"Average latency: {master_stats['average_latency_ms']:.2f}ms")
print(f"Current throughput: {master_stats['current_throughput_tps']:.1f} TPS")

# Component statistics
print(f"Transfer busy: {stats['transfer_busy']}")
print(f"Queue depth: {stats['queue_depth']}")

# Base statistics from FIFOComponentBase
print(f"Component type: {stats['component_type']}")
print(f"Signal mapping: {stats['signal_mapping_source']}")
```

## Usage Patterns

### Basic Write Operations

```python
# Set up master
field_config = FieldConfig.create_data_only(32)
master = FIFOMaster(dut, "Master", "", clock, field_config)

# Send single transaction
packet = master.create_packet(data=0x12345678)
await master.send(packet)

# Send multiple transactions
for i in range(10):
    packet = master.create_packet(data=0x1000 + i)
    await master.send(packet)
```

### Multi-Field Transactions

```python
# Configure multi-field packets
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex"))

# Create master with multi-signal mode
master = FIFOMaster(
    dut=dut,
    title="MultiFieldMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    multi_sig=True
)

# Send complex transactions
packet = master.create_packet(
    addr=0x1000,
    data=0xDEADBEEF,
    cmd=0x2  # WRITE command
)
await master.send(packet)
```

### Randomized Timing

```python
# Create randomizer for write delays
write_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 5), (10, 20)], [0.6, 0.3, 0.1])
})

# Create master with randomized timing
master = FIFOMaster(
    dut=dut,
    title="RandomMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    randomizer=write_randomizer
)

# Sends will have randomized delays
for i in range(50):
    packet = master.create_packet(data=0x2000 + i)
    await master.send(packet)  # Each send has random delay
```

### Memory-Integrated Testing

```python
# Set up memory model
memory = MemoryModel(num_lines=256, bytes_per_line=4)

# Create master with memory integration
master = FIFOMaster(
    dut=dut,
    title="MemoryMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    memory_model=memory
)

# Transactions automatically written to memory
for addr in range(0x1000, 0x1100, 4):
    packet = master.create_packet(addr=addr, data=addr + 0x5000)
    await master.send(packet)
    
    # Verify memory write
    success = await master.write_to_memory(packet)
    assert success, f"Failed to write to memory at {addr:X}"

# Read back and verify
for addr in range(0x1000, 0x1100, 4):
    packet = master.create_packet(addr=addr)
    success, data = await master.read_from_memory(packet)
    assert success and data == addr + 0x5000
```

### High-Performance Batch Operations

```python
class BatchMaster:
    def __init__(self, dut, clock, field_config):
        self.master = FIFOMaster(dut, "BatchMaster", "", clock, field_config)
        
    async def send_batch(self, packets, batch_size=10):
        """Send packets in batches for optimal performance"""
        for i in range(0, len(packets), batch_size):
            batch = packets[i:i+batch_size]
            
            # Send batch
            for packet in batch:
                await self.master.send(packet)
            
            # Check for flow control issues
            stats = self.master.get_stats()
            if stats['master_stats']['flow_control_stalls'] > 100:
                log.warning("High flow control stalls detected")
                # Adjust timing or batch size
                
    async def stress_test(self, count=1000):
        """High-throughput stress test"""
        packets = []
        for i in range(count):
            packet = self.master.create_packet(data=0x8000 + i)
            packets.append(packet)
        
        start_time = time.time()
        await self.send_batch(packets)
        end_time = time.time()
        
        # Analyze performance
        stats = self.master.get_stats()
        duration = end_time - start_time
        throughput = count / duration
        
        log.info(f"Stress test: {throughput:.1f} transactions/sec")
        log.info(f"Success rate: {stats['master_stats']['success_rate_percent']:.1f}%")
        log.info(f"Flow control stalls: {stats['master_stats']['flow_control_stalls']}")
```

### Error Handling and Recovery

```python
class RobustMaster:
    def __init__(self, dut, clock, field_config):
        self.master = FIFOMaster(
            dut=dut,
            title="RobustMaster",
            prefix="",
            clock=clock,
            field_config=field_config,
            timeout_cycles=2000  # Longer timeout for problematic interfaces
        )
        self.error_count = 0
        
    async def robust_send(self, packet, max_retries=3):
        """Send with retry on failure"""
        for attempt in range(max_retries + 1):
            try:
                await self.master.send(packet)
                return True
                
            except Exception as e:
                self.error_count += 1
                log.warning(f"Send attempt {attempt + 1} failed: {e}")
                
                if attempt < max_retries:
                    # Reset bus and retry
                    await self.master.reset_bus()
                    await self.master.wait_cycles(10)
                else:
                    log.error(f"All {max_retries + 1} attempts failed")
                    return False
        
        return False
    
    async def monitored_send(self, packet):
        """Send with continuous monitoring"""
        stats_before = self.master.get_stats()
        
        success = await self.robust_send(packet)
        
        stats_after = self.master.get_stats()
        
        # Check for new issues
        master_stats = stats_after['master_stats']
        prev_stats = stats_before['master_stats']
        
        new_violations = (master_stats['protocol_violations'] - 
                         prev_stats['protocol_violations'])
        new_timeouts = (master_stats['timeout_events'] - 
                       prev_stats['timeout_events'])
        
        if new_violations > 0:
            log.error(f"Protocol violations detected: {new_violations}")
        if new_timeouts > 0:
            log.error(f"Timeouts detected: {new_timeouts}")
            
        return success and new_violations == 0 and new_timeouts == 0
```

### Custom Signal Mapping

```python
# For non-standard FIFO interfaces
def create_custom_master(dut, clock, custom_signals):
    """Create master with custom signal naming"""
    
    # Map custom signals to expected names
    signal_map = {
        'write': custom_signals.get('write_enable', 'write'),
        'full': custom_signals.get('full_flag', 'full'),
        'data': custom_signals.get('write_data', 'data')
    }
    
    # Create field configuration
    field_config = FieldConfig.create_data_only(32)
    
    # Create master with custom mapping
    master = FIFOMaster(
        dut=dut,
        title="CustomMaster",
        prefix="",
        clock=clock,
        field_config=field_config,
        signal_map=signal_map,
        super_debug=True  # Enable for signal mapping debugging
    )
    
    return master

# Usage with custom interface
custom_signals = {
    'write_enable': 'wr_en',
    'full_flag': 'almost_full',
    'write_data': 'din'
}
master = create_custom_master(dut, clock, custom_signals)
```

## Performance Analysis

### Monitoring Performance

```python
class PerformanceAnalyzer:
    def __init__(self, master):
        self.master = master
        self.snapshots = []
        
    def take_snapshot(self):
        """Take performance snapshot"""
        stats = self.master.get_stats()
        snapshot = {
            'timestamp': time.time(),
            'stats': stats['master_stats'].copy()
        }
        self.snapshots.append(snapshot)
    
    def analyze_performance(self):
        """Analyze performance over time"""
        if len(self.snapshots) < 2:
            return {}
            
        recent = self.snapshots[-1]['stats']
        baseline = self.snapshots[0]['stats']
        
        analysis = {
            'total_transactions': recent['transactions_sent'],
            'success_rate': recent['success_rate_percent'],
            'average_latency_ms': recent['average_latency_ms'],
            'current_throughput_tps': recent['current_throughput_tps'],
            'flow_control_stalls': recent['flow_control_stalls'],
            'protocol_violations': recent['protocol_violations']
        }
        
        # Calculate rates since baseline
        time_diff = self.snapshots[-1]['timestamp'] - self.snapshots[0]['timestamp']
        if time_diff > 0:
            tx_diff = recent['transactions_sent'] - baseline['transactions_sent']
            analysis['average_rate_tps'] = tx_diff / time_diff
        
        return analysis

# Usage in test
analyzer = PerformanceAnalyzer(master)

# Take baseline snapshot
analyzer.take_snapshot()

# Run test operations
for i in range(1000):
    packet = master.create_packet(data=0x3000 + i)
    await master.send(packet)
    
    # Take periodic snapshots
    if i % 100 == 0:
        analyzer.take_snapshot()

# Final analysis
performance = analyzer.analyze_performance()
print(f"Test performance: {performance}")
```

## Error Conditions

### Flow Control Handling

The master automatically handles FIFO full conditions:

```python
# Master will:
# 1. Detect full signal assertion
# 2. Deassert write signal
# 3. Wait for full signal to deassert
# 4. Resume writing
# 5. Track flow control stalls in statistics

# Monitor flow control in your test
stats = master.get_stats()
if stats['master_stats']['flow_control_stalls'] > expected_threshold:
    log.warning("Excessive flow control stalls detected")
```

### Timeout Protection

```python
# Configure timeout for problematic interfaces
master = FIFOMaster(
    dut=dut,
    title="TimeoutProtectedMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    timeout_cycles=5000  # Wait up to 5000 cycles for not-full
)

# Timeouts are automatically tracked in statistics
stats = master.get_stats()
timeout_count = stats['master_stats']['timeout_events']
```

## Best Practices

### 1. **Use Factory Functions**
```python
# Recommended - use factory for setup
master = create_fifo_master(dut, "Master", clock, field_config)

# Rather than direct instantiation
```

### 2. **Monitor Statistics Regularly**
```python
# Check performance periodically
if cycle % 1000 == 0:
    stats = master.get_stats()
    if stats['master_stats']['success_rate_percent'] < 95:
        log.warning("Low success rate detected")
```

### 3. **Use Appropriate Randomizers**
```python
# For high-throughput testing
fast_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 1)], [9, 1])  # Mostly back-to-back
})

# For stress testing
stress_randomizer = FlexRandomizer({
    'write_delay': ([(0, 2), (5, 20), (50, 100)], [5, 3, 1])  # Variable delays
})
```

### 4. **Handle Memory Integration**
```python
# Always check memory operations
if master.memory_model:
    success = await master.write_to_memory(packet)
    if not success:
        log.error("Memory write failed")
```

### 5. **Reset Between Test Phases**
```python
# Reset master state between test phases
await master.reset_bus()
```

The FIFOMaster provides a high-performance, feature-rich interface for writing transactions to FIFO interfaces with comprehensive error handling, performance monitoring, and integration capabilities.
