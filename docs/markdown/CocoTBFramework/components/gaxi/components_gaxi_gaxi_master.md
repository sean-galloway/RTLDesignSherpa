# gaxi_master.py

GAXI Master with integrated structured pipeline that maintains all existing functionality and timing while adding better debugging and error recovery through structured pipeline phases.

## Overview

The `GAXIMaster` class provides:
- **Structured pipeline** with enhanced debugging and error recovery
- **Exact timing compatibility** with existing code
- **Signal resolution** and data driving from GAXIComponentBase
- **Memory model integration** using base MemoryModel directly
- **Comprehensive statistics** including pipeline performance
- **Optional pipeline debugging** for troubleshooting

Inherits common functionality from GAXIComponentBase and extends CocoTB BusDriver.

## Class

### GAXIMaster

```python
class GAXIMaster(GAXIComponentBase, BusDriver):
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
- `timeout_cycles`: Timeout for handshake operations (default: 1000)
- `mode`: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for timing
- `memory_model`: Optional memory model for transactions
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `pipeline_debug`: Enable pipeline phase debugging
- `signal_map`: Optional manual signal mapping override
- `**kwargs`: Additional arguments

## Core Methods

### Transaction Sending

#### `async send(packet)`
Send a packet and wait for completion.

**Parameters:**
- `packet`: Packet to send

**Returns:** True when complete

```python
# Create and send packet
packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
await master.send(packet)
```

#### `async busy_send(transaction)`
Send a transaction and wait for completion with busy checking.

**Parameters:**
- `transaction`: Transaction to send

```python
# Send with busy checking
transaction = master.create_packet(data=0x12345678)
await master.busy_send(transaction)
```

#### `create_packet(**field_values)`
Create a packet with specified field values.

**Parameters:**
- `**field_values`: Initial field values

**Returns:** GAXIPacket instance

```python
# Create packet with fields
packet = master.create_packet(
    addr=0x2000,
    data=0xCAFEBABE,
    cmd=0x1  # READ command
)
```

### Bus Management

#### `async reset_bus()`
Reset bus with enhanced pipeline state management.

```python
await master.reset_bus()
```

### Memory Operations

#### `async write_to_memory(packet)`
Write packet to memory using unified memory integration.

**Parameters:**
- `packet`: Packet to write

**Returns:** Success boolean

```python
packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
success = await master.write_to_memory(packet)
if not success:
    log.error("Memory write failed")
```

#### `async read_from_memory(packet)`
Read data from memory using unified memory integration.

**Parameters:**
- `packet`: Packet with address to read

**Returns:** Tuple of (success, data)

```python
packet = master.create_packet(addr=0x1000)
success, data = await master.read_from_memory(packet)
if success:
    log.info(f"Read data: 0x{data:X}")
```

### Pipeline Control and Debugging

#### `enable_pipeline_debug(enable=True)`
Enable or disable pipeline debugging at runtime.

**Parameters:**
- `enable`: Enable debugging flag

```python
# Enable detailed pipeline logging
master.enable_pipeline_debug(True)

# Disable for performance
master.enable_pipeline_debug(False)
```

#### `get_pipeline_stats()`
Get pipeline-specific statistics.

**Returns:** Dictionary with pipeline statistics

```python
pipeline_stats = master.get_pipeline_stats()
print(f"Current state: {pipeline_stats['current_state']}")
print(f"Queue depth: {pipeline_stats['queue_depth']}")
print(f"Phase counts: P1={pipeline_stats['phase1_count']}")
```

#### `get_pipeline_debug_info()`
Get detailed pipeline debug information.

**Returns:** Dictionary with debug information

```python
debug_info = master.get_pipeline_debug_info()
print(f"Phase timings: {debug_info['phase_timings']}")
print(f"Statistics: {debug_info['phase_statistics']}")
```

### Statistics

#### `get_stats()`
Get comprehensive statistics including pipeline stats.

**Returns:** Dictionary containing all statistics

```python
stats = master.get_stats()
print(f"Master stats: {stats['master_stats']}")
print(f"Base stats: {stats}")
print(f"Pipeline stats: {stats['pipeline_stats']}")
```

## Pipeline Architecture

The GAXIMaster uses a structured 3-phase pipeline:

### Phase 1: Apply Delays
- Apply `valid_delay` from randomizer
- Deassert valid and clear data during delay
- Maintains exact original timing

### Phase 2: Drive and Handshake
- Drive signals for transaction
- Assert valid signal
- Wait for ready handshake (with timeout)
- Enhanced error recovery on timeout

### Phase 3: Complete Transfer
- Capture completion time
- Deassert valid
- Clear data bus
- Move to sent queue

### Pipeline State Tracking
```python
# Pipeline states
"idle" → "queued" → "pipeline_active" → "transaction_start" →
"phase1" → "phase2" → "phase3" → "transaction_complete" → "idle"

# Error states
"error_recovery", "reset"
```

## Usage Patterns

### Basic Usage

```python
import cocotb
from cocotb.triggers import RisingEdge
from CocoTBFramework.components.gaxi import GAXIMaster
from CocoTBFramework.shared.field_config import FieldConfig

@cocotb.test()
async def test_gaxi_master(dut):
    clock = dut.clk
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32, format="hex"))
    field_config.add_field(FieldDefinition("data", 32, format="hex"))
    
    # Create master
    master = GAXIMaster(
        dut=dut,
        title="TestMaster",
        prefix="",
        clock=clock,
        field_config=field_config,
        pipeline_debug=True  # Enable pipeline debugging
    )
    
    # Reset bus
    await master.reset_bus()
    
    # Send transactions
    for i in range(10):
        packet = master.create_packet(
            addr=0x1000 + i*4,
            data=0x12340000 + i
        )
        await master.send(packet)
        
    # Get statistics
    stats = master.get_stats()
    print(f"Sent {stats['master_stats']['transactions_completed']} transactions")
```

### Advanced Configuration

```python
from CocoTBFramework.shared.flex_randomizer import FlexRandomizer
from CocoTBFramework.shared.memory_model import MemoryModel

# Create randomizer for timing
randomizer = FlexRandomizer({
    'valid_delay': ([(0, 0), (1, 5), (10, 20)], [0.6, 0.3, 0.1])
})

# Create memory model
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)

# Create master with advanced configuration
master = GAXIMaster(
    dut=dut,
    title="AdvancedMaster",
    prefix="m_",
    clock=clock,
    field_config=field_config,
    randomizer=randomizer,
    memory_model=memory,
    timeout_cycles=5000,
    pipeline_debug=True,
    multi_sig=True
)
```

### Memory-Integrated Testing

```python
@cocotb.test()
async def test_memory_operations(dut):
    master = GAXIMaster(dut, "MemMaster", "", clock, field_config,
                       memory_model=memory)
    
    # Write to memory
    write_packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
    success = await master.write_to_memory(write_packet)
    assert success, "Memory write failed"
    
    # Read from memory
    read_packet = master.create_packet(addr=0x1000)
    success, data = await master.read_from_memory(read_packet)
    assert success, "Memory read failed"
    assert data == 0xDEADBEEF, f"Data mismatch: expected 0xDEADBEEF, got 0x{data:X}"
    
    # Send read transaction
    await master.send(read_packet)
```

### Pipeline Debugging

```python
@cocotb.test()
async def test_with_pipeline_debug(dut):
    master = GAXIMaster(dut, "DebugMaster", "", clock, field_config,
                       pipeline_debug=True)
    
    # Send transaction with detailed logging
    packet = master.create_packet(addr=0x1000, data=0x12345678)
    await master.send(packet)
    
    # Analyze pipeline performance
    pipeline_stats = master.get_pipeline_stats()
    print(f"Pipeline Statistics:")
    print(f"  Phase 1 count: {pipeline_stats['phase1_count']}")
    print(f"  Phase 2 count: {pipeline_stats['phase2_count']}")
    print(f"  Phase 3 count: {pipeline_stats['phase3_count']}")
    print(f"  Timeouts: {pipeline_stats['timeout_count']}")
    print(f"  Errors: {pipeline_stats['error_count']}")
    
    # Get debug info
    debug_info = master.get_pipeline_debug_info()
    for state, timing in debug_info['phase_timings'].items():
        print(f"  {state}: {timing}ns")
```

### Burst Transactions

```python
async def send_burst_transactions(master, base_addr, count):
    """Send a burst of transactions"""
    for i in range(count):
        packet = master.create_packet(
            addr=base_addr + i*4,
            data=0x10000000 + i
        )
        await master.send(packet)
    
    # Get performance metrics
    stats = master.get_stats()
    master_stats = stats['master_stats']
    
    print(f"Burst complete:")
    print(f"  Transactions: {master_stats['transactions_completed']}")
    print(f"  Average latency: {master_stats['avg_latency']:.2f}ns")
    print(f"  Throughput: {master_stats['current_throughput_tps']:.1f} TPS")
```

### Error Handling and Recovery

```python
@cocotb.test()
async def test_error_recovery(dut):
    master = GAXIMaster(dut, "ErrorMaster", "", clock, field_config,
                       timeout_cycles=100,  # Short timeout for testing
                       pipeline_debug=True)
    
    try:
        # This might timeout if slave is not ready
        packet = master.create_packet(addr=0x1000, data=0x12345678)
        await master.send(packet)
        
    except Exception as e:
        log.error(f"Transaction failed: {e}")
        
        # Check pipeline state
        debug_info = master.get_pipeline_debug_info()
        print(f"Pipeline state: {debug_info['current_state']}")
        
        # Reset and try again
        await master.reset_bus()
        await master.send(packet)  # Should work after reset
```

### Performance Monitoring

```python
async def monitor_performance(master, duration_ms=1000):
    """Monitor master performance over time"""
    import asyncio
    
    start_time = get_sim_time('ns')
    end_time = start_time + duration_ms * 1e6  # Convert to ns
    
    while get_sim_time('ns') < end_time:
        # Send transaction
        packet = master.create_packet(
            addr=random.randint(0x1000, 0x8000),
            data=random.randint(0, 0xFFFFFFFF)
        )
        await master.send(packet)
        
        # Brief delay
        await asyncio.sleep(0.001)  # 1ms
    
    # Analyze performance
    stats = master.get_stats()
    master_stats = stats['master_stats']
    pipeline_stats = stats['pipeline_stats']
    
    print(f"Performance Analysis ({duration_ms}ms):")
    print(f"  Transactions sent: {master_stats['transactions_sent']}")
    print(f"  Success rate: {master_stats['success_rate_percent']:.1f}%")
    print(f"  Average latency: {master_stats['average_latency_ms']:.2f}ms")
    print(f"  Peak throughput: {master_stats['peak_throughput_tps']:.1f} TPS")
    print(f"  Pipeline errors: {pipeline_stats['error_count']}")
```

## Error Handling

### Timeout Handling
```python
# Timeouts are handled automatically with proper cleanup
try:
    await master.send(packet)
except TimeoutError:
    # Pipeline automatically recovers
    print("Transaction timed out but pipeline recovered")
```

### Signal Mapping Errors
```python
try:
    master = GAXIMaster(dut, "Master", "", clock, field_config)
except RuntimeError as e:
    # Try manual signal mapping
    signal_map = {'valid': 'custom_valid', 'ready': 'custom_ready'}
    master = GAXIMaster(dut, "Master", "", clock, field_config,
                       signal_map=signal_map)
```

### Memory Operation Errors
```python
success = await master.write_to_memory(packet)
if not success:
    # Memory operation failed
    stats = master.get_stats()
    if 'memory_stats' in stats:
        print(f"Memory errors: {stats['memory_stats']['boundary_violations']}")
```

## Best Practices

### 1. **Enable Pipeline Debugging During Development**
```python
master = GAXIMaster(..., pipeline_debug=True)  # Development
master = GAXIMaster(..., pipeline_debug=False) # Production
```

### 2. **Use Appropriate Timeout Values**
```python
# Short timeout for fast testing
master = GAXIMaster(..., timeout_cycles=100)

# Long timeout for realistic conditions  
master = GAXIMaster(..., timeout_cycles=10000)
```

### 3. **Monitor Statistics Regularly**
```python
# Check statistics periodically
if transaction_count % 100 == 0:
    stats = master.get_stats()
    check_performance_requirements(stats)
```

### 4. **Handle Reset Properly**
```python
# Reset before starting transactions
await master.reset_bus()

# Reset on error recovery
if error_detected:
    await master.reset_bus()
```

### 5. **Use Memory Model for Complex Testing**
```python
# Create memory model for transaction validation
memory = MemoryModel(1024, 4, log=log)
master = GAXIMaster(..., memory_model=memory)

# Validate transactions through memory
await master.write_to_memory(packet)
success, data = await master.read_from_memory(packet)
```

The GAXIMaster provides a robust, high-performance foundation for GAXI transaction generation with comprehensive debugging, error recovery, and performance monitoring capabilities.