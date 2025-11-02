# gaxi_component_base.py

Unified base class for all GAXI components that consolidates common functionality across GAXIMaster, GAXIMonitor, and GAXISlave, eliminating code duplication while preserving exact APIs and timing.

## Overview

The `GAXIComponentBase` class provides:
- **Unified signal resolution** and data handling setup
- **Shared field configuration** handling and packet management  
- **Memory model integration** using base MemoryModel directly
- **Common statistics** and logging patterns
- **Resolved signal passing** to DataStrategies eliminating guesswork

All existing parameters are preserved and used exactly as before, with the addition of optional manual signal mapping.

## Class

### GAXIComponentBase

```python
class GAXIComponentBase:
    def __init__(self, dut, title, prefix, clock, field_config,
                 protocol_type,  # Must be specified by subclass
                 bus_name='', pkt_prefix='', multi_sig=False,
                 randomizer=None, memory_model=None, log=None,
                 super_debug=False, signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix
- `clock`: Clock signal
- `field_config`: Field configuration (FieldConfig or dict)
- `protocol_type`: Protocol type ('gaxi_master' or 'gaxi_slave')
- `mode`: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for timing
- `memory_model`: Optional memory model for transactions
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional dict mapping signal names to DUT signal names
- `**kwargs`: Additional arguments for specific component types

**Signal Map Format:**
```python
# Manual signal mapping (bypasses automatic discovery)
signal_map = {
    'valid': 'dut_valid_signal_name',
    'ready': 'dut_ready_signal_name', 
    'data': 'dut_data_signal_name'     # For single-signal mode
    # Or individual field names for multi-signal mode
}
```

## Key Methods

### Core Initialization

#### `complete_base_initialization(bus=None)`
Complete initialization after cocotb parent class setup.

**Must be called by subclasses** after their cocotb parent class (BusDriver/BusMonitor) initialization is complete.

```python
# In subclass __init__ after BusDriver.__init__:
self.complete_base_initialization(self.bus)
```

### Unified Data Operations

#### `get_data_dict_unified()`
Get current data from signals with automatic field unpacking.

**Returns:** Dictionary of field values, properly unpacked

```python
# Clean data collection with automatic field unpacking
data = component.get_data_dict_unified()
print(data)  # {'addr': 0x1000, 'data': 0xDEADBEEF, 'cmd': 0x2}
```

#### `drive_transaction_unified(transaction)`
Drive transaction data using unified DataDrivingStrategy.

**Parameters:**
- `transaction`: Transaction to drive

**Returns:** True if successful, False otherwise

```python
packet = component.create_packet(addr=0x1000, data=0xDEADBEEF)
success = component.drive_transaction_unified(packet)
```

#### `clear_signals_unified()`
Clear all data signals using unified strategy.

```python
component.clear_signals_unified()  # Set all signals to 0
```

### Memory Operations

#### `write_to_memory_unified(transaction)`
Write transaction to memory using base MemoryModel.

**Parameters:**
- `transaction`: Transaction to write

**Returns:** Tuple of (success, error_message)

```python
success, error = component.write_to_memory_unified(packet)
if not success:
    log.error(f"Memory write failed: {error}")
```

#### `read_from_memory_unified(transaction, update_transaction=True)`
Read data from memory using base MemoryModel.

**Parameters:**
- `transaction`: Transaction with address to read
- `update_transaction`: Whether to update transaction with read data

**Returns:** Tuple of (success, data, error_message)

```python
success, data, error = component.read_from_memory_unified(packet)
if success:
    log.info(f"Read data: 0x{data:X}")
```

### Statistics and Configuration

#### `get_base_stats_unified()`
Get comprehensive base statistics common to all components.

**Returns:** Dictionary containing base statistics

```python
stats = component.get_base_stats_unified()
print(f"Component type: {stats['component_type']}")
print(f"Signal mapping source: {stats['signal_mapping_source']}")
print(f"Field count: {stats['field_count']}")
```

#### `set_randomizer(randomizer)`
Set new randomizer for timing control.

**Parameters:**
- `randomizer`: FlexRandomizer instance

```python
from CocoTBFramework.shared.flex_randomizer import FlexRandomizer

new_randomizer = FlexRandomizer({
    'valid_delay': ([(0, 0), (1, 5)], [0.8, 0.2])
})
component.set_randomizer(new_randomizer)
```

## Usage Patterns

### Basic Component Creation

```python
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.shared.field_config import FieldConfig

# Create field configuration
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))

# Create master (inherits from GAXIComponentBase)
master = GAXIMaster(
    dut=dut,
    title="TestMaster", 
    prefix="",
    clock=clock,
    field_config=field_config,
    mode='skid',
    multi_sig=True  # Individual signals for each field
)
```

### Manual Signal Mapping

```python
# For non-standard signal names
signal_map = {
    'valid': 'master_valid_custom',
    'ready': 'slave_ready_custom',
    'addr': 'address_signal',      # Multi-signal mode
    'data': 'data_signal'
}

master = GAXIMaster(
    dut=dut,
    title="CustomMaster",
    prefix="",
    clock=clock, 
    field_config=field_config,
    signal_map=signal_map  # Override automatic discovery
)
```

### Memory Integration

```python
from CocoTBFramework.shared.memory_model import MemoryModel

# Create memory model
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)

# Create component with memory
master = GAXIMaster(
    dut=dut,
    title="MemoryMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    memory_model=memory
)

# Write to memory through component
packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
success, error = master.write_to_memory_unified(packet)
```

### Unified Data Collection

```python
class CustomMonitor(GAXIComponentBase, BusMonitor):
    def __init__(self, dut, title, prefix, clock, field_config):
        GAXIComponentBase.__init__(
            self, dut, title, prefix, clock, field_config,
            protocol_type='gaxi_master'  # Monitor master side
        )
        BusMonitor.__init__(self, dut, prefix, clock)
        self.complete_base_initialization(self.bus)
    
    @cocotb.coroutine
    def _monitor_recv(self):
        while True:
            yield RisingEdge(self.clock)
            
            # Use unified data collection
            data = self.get_data_dict_unified()
            
            if data.get('valid', 0) == 1:
                # Process transaction
                packet = self.create_packet(**data)
                self._recv(packet)  # Add to cocotb queue
```

### Advanced Statistics

```python
def analyze_component_performance(component):
    """Analyze component performance using base stats"""
    stats = component.get_base_stats_unified()
    
    print(f"=== Component Analysis: {stats['title']} ===")
    print(f"Type: {stats['component_type']}")
    print(f"Mode: {stats['mode']}")
    print(f"Multi-signal: {stats['multi_signal']}")
    print(f"Fields: {stats['field_count']}")
    
    # Signal resolver statistics
    if 'signal_resolver_stats' in stats:
        resolver_stats = stats['signal_resolver_stats']
        print(f"Signal resolution rate: {resolver_stats['resolution_rate']:.1f}%")
        print(f"Signal conflicts: {resolver_stats['conflicts']}")
    
    # Data strategy statistics  
    if 'data_collector_stats' in stats:
        collector_stats = stats['data_collector_stats']
        print(f"Data collection mode: {collector_stats['mode']}")
        print(f"Performance optimized: {collector_stats['performance_optimized']}")
    
    # Memory statistics
    if 'memory_stats' in stats:
        memory_stats = stats['memory_stats']
        print(f"Memory operations: {memory_stats['reads'] + memory_stats['writes']}")
        print(f"Memory coverage: {memory_stats['read_coverage']:.1%}")
```

## Error Handling

### Signal Resolution Errors
```python
try:
    master = GAXIMaster(dut, "Master", "", clock, field_config)
except RuntimeError as e:
    # Detailed error with signal mapping diagnostics
    log.error(f"Signal mapping failed: {e}")
    
    # Try manual mapping as fallback
    signal_map = create_fallback_signal_map(dut)
    master = GAXIMaster(dut, "Master", "", clock, field_config, 
                       signal_map=signal_map)
```

### Memory Operation Errors
```python
# Memory operations return success/error tuples
success, error = component.write_to_memory_unified(packet)
if not success:
    if "boundary" in error.lower():
        log.error(f"Address out of bounds: {error}")
    elif "type" in error.lower():
        log.error(f"Data type error: {error}")
    else:
        log.error(f"Memory error: {error}")
```

## Internal Architecture

### Signal Resolution Flow
1. **SignalResolver creation** with protocol type and parameters
2. **Pattern matching** against DUT ports (or manual mapping)
3. **Signal validation** and conflict detection
4. **DataStrategy creation** with resolved signals
5. **Component signal application** via `apply_to_component()`

### Data Strategy Integration
```python
# Internal flow (handled automatically)
resolver = SignalResolver(protocol_type, dut, bus, log, title, ...)
resolved_signals = resolver.resolved_signals

# Pass resolved signals to strategies (eliminates guesswork)
data_collector = DataCollectionStrategy(..., resolved_signals=resolved_signals)
data_driver = DataDrivingStrategy(..., resolved_signals=resolved_signals)
```

### Memory Model Integration
- Uses base MemoryModel methods directly
- Transaction-based read/write operations
- Automatic field extraction and validation
- Error handling with detailed messages

## Best Practices

### 1. **Use Automatic Signal Discovery First**
```python
# Try automatic discovery
component = GAXIMaster(dut, title, prefix, clock, field_config)

# Fall back to manual mapping if needed
if not all_signals_found:
    signal_map = {...}
    component = GAXIMaster(..., signal_map=signal_map)
```

### 2. **Always Complete Base Initialization**
```python
# In subclass after cocotb parent initialization
class MyComponent(GAXIComponentBase, BusDriver):
    def __init__(self, ...):
        GAXIComponentBase.__init__(self, ...)
        BusDriver.__init__(self, ...)
        self.complete_base_initialization(self.bus)  # Essential!
```

### 3. **Use Unified Methods for Consistency**
```python
# Prefer unified methods over custom implementations
data = component.get_data_dict_unified()  # Not custom _get_data_dict()
success = component.drive_transaction_unified(packet)  # Not custom driving
```

### 4. **Monitor Statistics for Performance**
```python
# Regular performance monitoring
stats = component.get_base_stats_unified()
if 'data_collector_stats' in stats:
    collector_stats = stats['data_collector_stats']
    if not collector_stats['performance_optimized']:
        log.warning("Data collection not optimized")
```

### 5. **Handle Memory Operations Gracefully**
```python
# Always check memory operation results
success, error = component.write_to_memory_unified(packet)
if not success:
    # Handle error appropriately for test context
    handle_memory_error(error, packet)
```

GAXIComponentBase provides the foundation for all GAXI components, ensuring consistent behavior, optimal performance, and comprehensive error handling across the entire GAXI ecosystem.