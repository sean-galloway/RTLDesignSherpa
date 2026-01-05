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

# gaxi_slave.py

GAXI Slave with integrated structured pipeline that maintains all existing functionality and timing while adding better debugging and error recovery through structured pipeline phases.

## Overview

The `GAXISlave` class provides:
- **Structured receive pipeline** with enhanced debugging and error recovery
- **Active ready signal driving** with timing control
- **Mode-specific data capture** (skid, fifo_mux, fifo_flop)
- **Memory model integration** using base MemoryModel directly
- **Comprehensive statistics** including pipeline performance
- **Optional pipeline debugging** for troubleshooting

Inherits from GAXIMonitorBase which provides common monitoring functionality and signal resolution.

## Class

### GAXISlave

```python
class GAXISlave(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config,
                 multi_sig=False, randomizer=None, memory_model=None,
                 log=None, super_debug=False, pipeline_debug=False,
                 signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix
- `clock`: Clock signal
- `field_config`: Field configuration
- `timeout_cycles`: Timeout for operations (default: 1000)
- `mode`: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for ready delays
- `memory_model`: Optional memory model for transactions
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `pipeline_debug`: Enable pipeline phase debugging
- `signal_map`: Optional manual signal mapping override
- `**kwargs`: Additional arguments

## Data Capture Modes

The GAXISlave supports different data capture timing based on the mode:

### Skid Mode (`mode='skid'`)
- **Data capture**: Immediate (same cycle as handshake)
- **Use case**: Standard pipeline with no delay
- **Performance**: Fastest response time

### FIFO MUX Mode (`mode='fifo_mux'`)
- **Data capture**: Immediate (same cycle as handshake)
- **Use case**: Multiplexed FIFO interface
- **Performance**: Fast response time

### FIFO FLOP Mode (`mode='fifo_flop'`)
- **Data capture**: Delayed (one cycle after handshake)
- **Use case**: Registered FIFO interface
- **Performance**: One cycle latency for data capture

## Core Methods

### Bus Management

#### `async reset_bus()`
Reset bus with enhanced pipeline state management.

```python
await slave.reset_bus()
```

### Callback Management

#### `add_callback(callback)`
Add callback for received transactions.

**Parameters:**
- `callback`: Function to call when transaction is received

```python
def transaction_handler(packet):
    print(f"Received: {packet.formatted()}")

slave.add_callback(transaction_handler)
```

#### `remove_callback(callback)`
Remove callback.

```python
slave.remove_callback(transaction_handler)
```

### Data Access

#### `get_observed_packets(count=None)`
Get observed packets from the receive queue.

**Parameters:**
- `count`: Number of packets to return (None = all)

**Returns:** List of observed packets

```python
# Get all observed packets
all_packets = slave.get_observed_packets()

# Get last 5 packets
recent_packets = slave.get_observed_packets(5)
```

#### `clear_observed_packets()`
Clear the observed packets queue.

```python
slave.clear_observed_packets()
```

### Pipeline Control and Debugging

#### `enable_pipeline_debug(enable=True)`
Enable or disable pipeline debugging at runtime.

```python
# Enable detailed pipeline logging
slave.enable_pipeline_debug(True)

# Disable for performance
slave.enable_pipeline_debug(False)
```

#### `get_pipeline_stats()`
Get pipeline-specific statistics.

**Returns:** Dictionary with pipeline statistics

```python
pipeline_stats = slave.get_pipeline_stats()
print(f"Current state: {pipeline_stats['current_state']}")
print(f"Handshakes: {pipeline_stats['handshake_count']}")
print(f"Immediate captures: {pipeline_stats['immediate_captures']}")
print(f"Deferred captures: {pipeline_stats['deferred_captures']}")
```

#### `get_pipeline_debug_info()`
Get detailed pipeline debug information.

```python
debug_info = slave.get_pipeline_debug_info()
print(f"Phase timings: {debug_info['phase_timings']}")
print(f"Mode: {debug_info['mode']}")
```

### Statistics

#### `get_stats()`
Get comprehensive statistics including pipeline stats.

**Returns:** Dictionary containing all statistics

```python
stats = slave.get_stats()
print(f"Monitor stats: {stats['slave_stats']}")
print(f"Pipeline stats: {stats['pipeline_stats']}")
print(f"Base stats: {stats}")
```

## Pipeline Architecture

The GAXISlave uses a structured 3-phase receive pipeline:

### Phase 1: Handle Pending Transactions
- Process deferred captures from fifo_flop mode
- Maintain exact original timing
- Enhanced debugging and statistics

### Phase 2: Ready Timing Control
- Apply `ready_delay` from randomizer
- Deassert ready during delay periods
- Assert ready when ready to accept data
- Wait for falling edge for signal sampling

### Phase 3: Transaction Processing
- Detect valid/ready handshake
- Create packet and capture timing
- Mode-specific data capture (immediate vs deferred)
- Memory operations and callback triggering

### Pipeline State Tracking
```python
# Pipeline states
"idle" → "monitor_start" → "cycle_start" → "phase1" → 
"phase2" → "phase3" → "cycle_end" → "cycle_start" ...

# Error states  
"error_recovery", "reset"
```

## Usage Patterns

### Basic Usage

```python
import cocotb
from cocotb.triggers import RisingEdge
from CocoTBFramework.components.gaxi import GAXISlave
from CocoTBFramework.shared.field_config import FieldConfig

@cocotb.test()
async def test_gaxi_slave(dut):
    clock = dut.clk
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32, format="hex"))
    field_config.add_field(FieldDefinition("data", 32, format="hex"))
    
    # Create slave
    slave = GAXISlave(
        dut=dut,
        title="TestSlave",
        prefix="",
        clock=clock,
        field_config=field_config,
        mode='skid',
        pipeline_debug=True  # Enable pipeline debugging
    )
    
    # Add callback to process transactions
    def process_transaction(packet):
        print(f"Slave received: addr=0x{packet.addr:X}, data=0x{packet.data:X}")
    
    slave.add_callback(process_transaction)
    
    # Reset bus
    await slave.reset_bus()
    
    # Start monitoring (automatically started)
    # Transactions will be captured and processed via callbacks
    
    # Wait for some transactions
    await Timer(1000, units='ns')
    
    # Check received transactions
    packets = slave.get_observed_packets()
    print(f"Received {len(packets)} transactions")
```

### Mode-Specific Configuration

```python
# Skid mode - immediate capture
skid_slave = GAXISlave(
    dut=dut,
    title="SkidSlave",
    prefix="s_",
    clock=clock,
    field_config=field_config,
    mode='skid'  # Immediate data capture
)

# FIFO FLOP mode - delayed capture  
flop_slave = GAXISlave(
    dut=dut,
    title="FlopSlave", 
    prefix="f_",
    clock=clock,
    field_config=field_config,
    mode='fifo_flop'  # Delayed data capture
)
```

### Advanced Configuration with Memory

```python
from CocoTBFramework.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.shared.memory_model import MemoryModel

# Create randomizer for ready delays
randomizer = FlexRandomizer({
    'ready_delay': ([(0, 1), (2, 8), (9, 30)], [0.6, 0.3, 0.1])
})

# Create memory model for transaction storage
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)

# Create slave with advanced configuration
slave = GAXISlave(
    dut=dut,
    title="AdvancedSlave",
    prefix="adv_",
    clock=clock,
    field_config=field_config,
    randomizer=randomizer,
    memory_model=memory,
    mode='fifo_mux',
    pipeline_debug=True,
    multi_sig=True
)
```

### Memory-Integrated Processing

```python
@cocotb.test()
async def test_memory_slave(dut):
    # Create memory model
    memory = MemoryModel(num_lines=256, bytes_per_line=4, log=log)
    
    # Create slave with memory
    slave = GAXISlave(
        dut=dut,
        title="MemorySlave",
        prefix="",
        clock=clock,
        field_config=field_config,
        memory_model=memory
    )
    
    # Memory operations happen automatically in the pipeline
    # Check memory contents after transactions
    await Timer(1000, units='ns')
    
    # Get memory statistics
    stats = slave.get_stats()
    if 'memory_stats' in stats:
        memory_stats = stats['memory_stats']
        print(f"Memory writes: {memory_stats['writes']}")
        print(f"Memory coverage: {memory_stats['write_coverage']:.1%}")
```

### Pipeline Performance Analysis

```python
@cocotb.test()
async def test_pipeline_performance(dut):
    slave = GAXISlave(dut, "PerfSlave", "", clock, field_config,
                     pipeline_debug=True)
    
    # Run for a period
    await Timer(10000, units='ns')
    
    # Analyze pipeline performance
    pipeline_stats = slave.get_pipeline_stats()
    
    print(f"Pipeline Performance Analysis:")
    print(f"  Total handshakes: {pipeline_stats['handshake_count']}")
    print(f"  Immediate captures: {pipeline_stats['immediate_captures']}")
    print(f"  Deferred captures: {pipeline_stats['deferred_captures']}")
    print(f"  Memory operations: {pipeline_stats['memory_operations']}")
    print(f"  Errors: {pipeline_stats['error_count']}")
    
    # Calculate efficiency metrics
    total_captures = (pipeline_stats['immediate_captures'] + 
                     pipeline_stats['deferred_captures'])
    if total_captures > 0:
        immediate_rate = pipeline_stats['immediate_captures'] / total_captures
        print(f"  Immediate capture rate: {immediate_rate:.1%}")
    
    # Get timing information
    debug_info = slave.get_pipeline_debug_info()
    for phase, timing in debug_info['phase_timings'].items():
        print(f"  {phase}: {timing}ns")
```

### Ready Delay Testing

```python
@cocotb.test()
async def test_ready_delays(dut):
    # Create randomizer with specific delay patterns
    randomizer = FlexRandomizer({
        'ready_delay': ([(0, 0), (1, 1), (5, 10)], [0.5, 0.3, 0.2])
    })
    
    slave = GAXISlave(
        dut=dut,
        title="DelayedSlave",
        prefix="",
        clock=clock,
        field_config=field_config,
        randomizer=randomizer,
        pipeline_debug=True
    )
    
    # Track ready signal behavior
    ready_assert_times = []
    ready_delays = []
    
    def track_ready_timing(packet):
        # This callback is called when transaction completes
        # Can analyze timing here
        pass
    
    slave.add_callback(track_ready_timing)
    
    # Monitor for a period
    await Timer(5000, units='ns')
    
    # Analyze ready delay effectiveness
    pipeline_stats = slave.get_pipeline_stats()
    print(f"Ready delay testing: {pipeline_stats['handshake_count']} handshakes")
```

### Callback-Based Processing

```python
class TransactionProcessor:
    def __init__(self):
        self.received_count = 0
        self.data_sum = 0
        
    def process_transaction(self, packet):
        """Callback for processing received transactions"""
        self.received_count += 1
        self.data_sum += packet.data
        
        print(f"Transaction {self.received_count}: "
              f"addr=0x{packet.addr:X}, data=0x{packet.data:X}")
        
        # Perform application-specific processing
        if packet.addr >= 0x8000:
            print("  → High address region access")
        
        if packet.data == 0xDEADBEEF:
            print("  → Test pattern detected")
    
    def get_summary(self):
        avg_data = self.data_sum / self.received_count if self.received_count > 0 else 0
        return {
            'received_count': self.received_count,
            'average_data': avg_data
        }

@cocotb.test()
async def test_callback_processing(dut):
    # Create processor
    processor = TransactionProcessor()
    
    # Create slave with callback
    slave = GAXISlave(dut, "CallbackSlave", "", clock, field_config)
    slave.add_callback(processor.process_transaction)
    
    # Run test
    await Timer(2000, units='ns')
    
    # Get processing summary
    summary = processor.get_summary()
    print(f"Processing summary: {summary}")
```

### Error Handling and Recovery

```python
@cocotb.test()
async def test_error_recovery(dut):
    slave = GAXISlave(dut, "ErrorSlave", "", clock, field_config,
                     pipeline_debug=True)
    
    # Callback that might cause errors
    def error_prone_callback(packet):
        if packet.data == 0xBADDATA:
            raise ValueError("Bad data detected")
        print(f"Processed: {packet.formatted()}")
    
    slave.add_callback(error_prone_callback)
    
    try:
        # Run test
        await Timer(1000, units='ns')
        
    except Exception as e:
        log.error(f"Test error: {e}")
        
        # Check pipeline state
        debug_info = slave.get_pipeline_debug_info()
        print(f"Pipeline state: {debug_info['current_state']}")
        
        # Pipeline should continue operating despite callback errors
        pipeline_stats = slave.get_pipeline_stats()
        print(f"Error count: {pipeline_stats['error_count']}")
        
        # Reset if needed
        await slave.reset_bus()
```

## Error Handling

### Signal Mapping Errors
```python
try:
    slave = GAXISlave(dut, "Slave", "", clock, field_config)
except RuntimeError as e:
    # Try manual signal mapping
    signal_map = {'valid': 'custom_valid', 'ready': 'custom_ready'}
    slave = GAXISlave(dut, "Slave", "", clock, field_config,
                     signal_map=signal_map)
```

### Memory Operation Errors
```python
# Memory operations handled automatically with error logging
# Check memory statistics for error information
stats = slave.get_stats()
if 'memory_stats' in stats:
    memory_stats = stats['memory_stats']
    if memory_stats['boundary_violations'] > 0:
        log.warning(f"Memory boundary violations: {memory_stats['boundary_violations']}")
```

### Pipeline Errors
```python
# Pipeline errors are tracked in statistics
pipeline_stats = slave.get_pipeline_stats()
if pipeline_stats['error_count'] > 0:
    log.warning(f"Pipeline errors detected: {pipeline_stats['error_count']}")
    
    # Get detailed error information
    debug_info = slave.get_pipeline_debug_info()
    print(f"Current state: {debug_info['current_state']}")
```

## Best Practices

### 1. **Choose Appropriate Mode for DUT**
```python
# Match slave mode to DUT implementation
if dut_uses_registered_interface:
    mode = 'fifo_flop'  # Delayed capture
else:
    mode = 'skid'       # Immediate capture
```

### 2. **Use Callbacks for Transaction Processing**
```python
# Prefer callbacks over polling
slave.add_callback(process_transaction)

# Avoid polling _recvQ directly
# packets = slave._recvQ  # Don't do this
packets = slave.get_observed_packets()  # Do this instead
```

### 3. **Enable Pipeline Debugging During Development**
```python
slave = GAXISlave(..., pipeline_debug=True)   # Development
slave = GAXISlave(..., pipeline_debug=False)  # Production
```

### 4. **Configure Ready Delays Appropriately**
```python
# For throughput testing
randomizer = FlexRandomizer({'ready_delay': ([(0, 0)], [1.0])})

# For realistic backpressure
randomizer = FlexRandomizer({
    'ready_delay': ([(0, 1), (2, 8)], [0.7, 0.3])
})
```

### 5. **Monitor Pipeline Statistics**
```python
# Regular statistics monitoring
if transaction_count % 100 == 0:
    pipeline_stats = slave.get_pipeline_stats()
    if pipeline_stats['error_count'] > expected_threshold:
        handle_error_condition()
```

The GAXISlave provides comprehensive transaction reception capabilities with flexible timing control, mode-specific data capture, and extensive debugging support for thorough verification of GAXI protocol implementations.