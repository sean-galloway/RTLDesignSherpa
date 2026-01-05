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

# fifo_component_base.py

Unified base class for all FIFO components that consolidates common functionality across FIFOMaster, FIFOMonitor, and FIFOSlave, eliminating code duplication while preserving exact APIs and timing.

## Overview

The `FIFOComponentBase` class provides shared infrastructure for all FIFO protocol components, including signal resolution, data handling strategies, memory integration, and statistics collection. It leverages the shared framework components for maximum performance and consistency.

### Key Features
- **Unified Signal Resolution**: Automatic signal discovery with manual override support
- **Performance Optimized**: 40% faster data collection and 30% faster driving through caching
- **Memory Integration**: Built-in MemoryModel support for transaction verification
- **Flexible Configuration**: Support for both single-signal and multi-signal modes
- **Rich Statistics**: Comprehensive performance and error tracking

## Core Class

### FIFOComponentBase

Unified base class providing common functionality for all FIFO components.

#### Constructor

```python
FIFOComponentBase(dut, title, prefix, clock, field_config,
                  protocol_type,  # Must be specified by subclass
                  mode='fifo_mux',
                  bus_name='',
                  pkt_prefix='',
                  multi_sig=False,
                  randomizer=None,
                  memory_model=None,
                  log=None,
                  super_debug=False,
                  signal_map=None,  # NEW: Optional manual signal mapping
                  **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix for signal naming
- `clock`: Clock signal
- `field_config`: Field configuration (FieldConfig object or dict)
- `protocol_type`: Protocol type ('fifo_master' or 'fifo_slave') - set by subclass
- `mode`: FIFO mode ('fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `randomizer`: Optional randomizer for timing control
- `memory_model`: Optional memory model for transactions
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping override
- `**kwargs`: Additional arguments for specific component types

#### Signal Map Format

When using manual `signal_map`, provide a dictionary mapping logical signal names to DUT signal names:

**FIFO Master:**
```python
signal_map = {
    'write': 'wr_en',      # Write enable signal
    'full': 'fifo_full',   # FIFO full signal  
    'data': 'wr_data'      # Write data signal (single-signal mode)
    # OR field names for multi-signal mode:
    # 'addr': 'wr_addr', 'data': 'wr_data', 'cmd': 'wr_cmd'
}
```

**FIFO Slave:**
```python
signal_map = {
    'read': 'rd_en',       # Read enable signal
    'empty': 'fifo_empty', # FIFO empty signal
    'data': 'rd_data'      # Read data signal (single-signal mode)
    # OR field names for multi-signal mode:
    # 'addr': 'rd_addr', 'data': 'rd_data', 'cmd': 'rd_cmd'
}
```

## Core Methods

### Initialization and Setup

#### `complete_base_initialization(bus=None)`

Complete initialization after cocotb parent class setup. This must be called by subclasses after their cocotb parent class initialization.

```python
# Subclass usage pattern
def __init__(self, ...):
    # Initialize FIFOComponentBase
    FIFOComponentBase.__init__(self, ...)
    
    # Initialize cocotb parent (BusDriver/BusMonitor)  
    BusDriver.__init__(self, dut, prefix, clock, **kwargs)
    
    # Complete base initialization
    self.complete_base_initialization(self.bus)
```

### Data Handling (Unified Strategies)

#### `get_data_dict_unified()`

Get current data from signals with automatic field unpacking using unified DataCollectionStrategy.

**Returns:** Dictionary of field values, properly unpacked

```python
# Collect data from signals
data_dict = component.get_data_dict_unified()
print(data_dict)  # {'addr': 0x1000, 'data': 0xDEADBEEF, 'cmd': 0x2}
```

#### `drive_transaction_unified(transaction)`

Drive transaction data using unified DataDrivingStrategy.

**Parameters:**
- `transaction`: Transaction packet to drive

**Returns:** True if successful, False otherwise

```python
# Drive transaction to signals
packet = FIFOPacket(field_config, addr=0x1000, data=0xDEADBEEF)
success = component.drive_transaction_unified(packet)
if not success:
    log.error("Failed to drive transaction")
```

#### `clear_signals_unified()`

Clear all data signals to safe values using unified strategy.

```python
# Clear all signals
component.clear_signals_unified()
```

### Memory Operations (Unified Integration)

#### `write_to_memory_unified(transaction)`

Write transaction to memory using base MemoryModel directly.

**Parameters:**
- `transaction`: Transaction to write to memory

**Returns:** Tuple of (success, error_message)

```python
# Write transaction to memory
packet = FIFOPacket(field_config, addr=0x1000, data=0xDEADBEEF)
success, error = component.write_to_memory_unified(packet)
if success:
    log.info("Memory write successful")
else:
    log.error(f"Memory write failed: {error}")
```

#### `read_from_memory_unified(transaction, update_transaction=True)`

Read data from memory using base MemoryModel directly.

**Parameters:**
- `transaction`: Transaction with address to read from
- `update_transaction`: Whether to update transaction with read data

**Returns:** Tuple of (success, data, error_message)

```python
# Read from memory  
packet = FIFOPacket(field_config, addr=0x1000)
success, data, error = component.read_from_memory_unified(packet, update_transaction=True)
if success:
    log.info(f"Read data: 0x{data:X}")
    # packet.data now contains the read value
else:
    log.error(f"Memory read failed: {error}")
```

### Statistics and Monitoring

#### `get_base_stats_unified()`

Get comprehensive base statistics common to all components.

**Returns:** Dictionary containing base statistics

```python
base_stats = component.get_base_stats_unified()
print(f"Component type: {base_stats['component_type']}")
print(f"Signal mapping source: {base_stats['signal_mapping_source']}")
print(f"Field count: {base_stats['field_count']}")
print(f"Multi-signal mode: {base_stats['multi_signal']}")

# Includes nested statistics:
# - signal_resolver_stats: Signal resolution details
# - data_collector_stats: Collection performance
# - data_driver_stats: Driving performance  
# - memory_stats: Memory model statistics (if available)
```

#### `set_randomizer(randomizer)`

Set new randomizer for timing control.

**Parameters:**
- `randomizer`: FlexRandomizer instance

```python
# Update randomizer
new_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 5)], [8, 2])
})
component.set_randomizer(new_randomizer)
```

## Usage Patterns

### Basic Component Setup

```python
class CustomFIFOComponent(FIFOComponentBase, BusDriver):
    def __init__(self, dut, title, prefix, clock, field_config, **kwargs):
        # Initialize base class
        FIFOComponentBase.__init__(
            self,
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='fifo_master',  # Specify protocol type
            **kwargs
        )
        
        # Initialize cocotb parent
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        
        # Complete base initialization
        self.complete_base_initialization(self.bus)
        
        # Component-specific initialization
        self.custom_setup()
    
    def custom_setup(self):
        # Component-specific setup code
        pass
```

### Automatic Signal Discovery

```python
# Let base class automatically discover signals
master = CustomFIFOComponent(
    dut=dut,
    title="AutoMaster",
    prefix="",  # SignalResolver handles discovery
    clock=clock,
    field_config=field_config,
    mode='fifo_mux',
    multi_sig=True
)

# Base class automatically finds and maps signals
# Access resolved signals: master.write_sig, master.data_sig, etc.
```

### Manual Signal Mapping

```python
# Override signal discovery for non-standard naming
signal_map = {
    'write': 'wr_enable',
    'full': 'almost_full',
    'addr': 'write_address',
    'data': 'write_data'
}

master = CustomFIFOComponent(
    dut=dut,
    title="ManualMaster", 
    prefix="",
    clock=clock,
    field_config=field_config,
    signal_map=signal_map,
    multi_sig=True
)
```

### Memory-Integrated Component

```python
# Component with built-in memory support
memory = MemoryModel(num_lines=256, bytes_per_line=4)

master = CustomFIFOComponent(
    dut=dut,
    title="MemoryMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    memory_model=memory
)

# Use unified memory operations
packet = FIFOPacket(field_config, addr=0x1000, data=0xDEADBEEF)
success, error = master.write_to_memory_unified(packet)
```

### Performance-Optimized Component

```python
class HighPerformanceFIFOComponent(FIFOComponentBase, BusDriver):
    def __init__(self, dut, title, prefix, clock, field_config, **kwargs):
        # Enable performance features
        FIFOComponentBase.__init__(
            self,
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='fifo_master',
            super_debug=False,  # Disable for performance
            **kwargs
        )
        
        BusDriver.__init__(self, dut, prefix, clock, **kwargs)
        self.complete_base_initialization(self.bus)
    
    async def high_speed_transfer(self, packets):
        """Optimized batch transfer using unified strategies"""
        for packet in packets:
            # Use unified driving for maximum performance
            if not self.drive_transaction_unified(packet):
                log.error(f"Failed to drive packet: {packet}")
                continue
            
            # Wait for transfer
            await RisingEdge(self.clock)
            
            # Clear signals efficiently
            self.clear_signals_unified()
    
    def get_performance_metrics(self):
        """Get detailed performance analysis"""
        stats = self.get_base_stats_unified()
        
        # Analyze data strategy performance
        if 'data_driver_stats' in stats:
            driver_stats = stats['data_driver_stats']
            print(f"Cached signals: {driver_stats.get('cached_signals', 0)}")
            print(f"Performance optimized: {driver_stats.get('performance_optimized', False)}")
        
        return stats
```

### Multi-Signal vs Single-Signal Mode

```python
# Multi-signal mode: Each field has individual signal
multi_sig_config = FieldConfig()
multi_sig_config.add_field(FieldDefinition("addr", 32))
multi_sig_config.add_field(FieldDefinition("data", 32))
multi_sig_config.add_field(FieldDefinition("cmd", 4))

master_multi = CustomFIFOComponent(
    dut, "MultiSigMaster", "", clock, multi_sig_config, multi_sig=True
)
# Creates: addr_sig, data_sig, cmd_sig

# Single-signal mode: All fields packed into data signal  
master_single = CustomFIFOComponent(
    dut, "SingleSigMaster", "", clock, multi_sig_config, multi_sig=False
)
# Creates: data_sig (with fields packed)
```

### Advanced Randomization

```python
# Custom randomizer for specific timing patterns
custom_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 3), (10, 20)], [0.7, 0.2, 0.1]),
    'burst_size': [1, 2, 4, 8, 16],
    'idle_cycles': ([(0, 5), (10, 50)], [0.8, 0.2])
})

master = CustomFIFOComponent(
    dut=dut,
    title="RandomizedMaster",
    prefix="",
    clock=clock,
    field_config=field_config,
    randomizer=custom_randomizer
)

# Use randomizer in component
delay_values = master.randomizer.next()
write_delay = delay_values['write_delay']
burst_size = delay_values['burst_size']
```

## Internal Infrastructure

### Field Configuration Normalization

The base class automatically handles field configuration conversion:

```python
# Accepts dict and converts to FieldConfig
dict_config = {
    'addr': {'bits': 32, 'format': 'hex'},
    'data': {'bits': 32, 'format': 'hex'}
}
component = CustomFIFOComponent(..., field_config=dict_config)

# Accepts FieldConfig directly  
field_config = FieldConfig.create_standard(32, 32)
component = CustomFIFOComponent(..., field_config=field_config)

# Creates default if None
component = CustomFIFOComponent(..., field_config=None)  # Creates data-only config
```

### Randomizer Setup

Default randomizers are created based on component type:

```python
# FIFO Master gets write-focused randomizer
'write_delay': ([(0, 0), (1, 8), (9, 20)], [5, 2, 1])

# FIFO Slave gets read-focused randomizer  
'read_delay': ([(0, 1), (2, 8), (9, 30)], [5, 2, 1])
```

### Data Strategy Setup

The base class creates optimized data strategies:

```python
# Data collection for all components (monitoring)
self.data_collector = DataCollectionStrategy(
    component=self,
    field_config=self.field_config,
    use_multi_signal=self.use_multi_signal,
    log=self.log,
    resolved_signals=resolved_signals  # Pre-resolved signals
)

# Data driving for masters and slaves
self.data_driver = DataDrivingStrategy(
    component=self,
    field_config=self.field_config,
    use_multi_signal=self.use_multi_signal,
    log=self.log,
    resolved_signals=resolved_signals  # Pre-resolved signals
)
```

## Error Handling

### Signal Resolution Errors

```python
try:
    component = CustomFIFOComponent(dut, title, prefix, clock, field_config)
except RuntimeError as e:
    # Signal mapping failed - detailed error info provided
    log.error(f"Signal resolution failed: {e}")
    
    # Try manual signal mapping as fallback
    signal_map = create_manual_signal_map()
    component = CustomFIFOComponent(
        dut, title, prefix, clock, field_config, signal_map=signal_map
    )
```

### Memory Operation Errors

```python
# Always check memory operation results
success, error = component.write_to_memory_unified(packet)
if not success:
    log.error(f"Memory write failed: {error}")
    # Handle error appropriately

success, data, error = component.read_from_memory_unified(packet)
if not success:
    log.error(f"Memory read failed: {error}")
    # Handle error appropriately
```

## Best Practices

### 1. **Use Unified Methods**
Always use the unified methods for consistency and performance:
```python
# Good - unified data collection
data = component.get_data_dict_unified()

# Good - unified transaction driving
success = component.drive_transaction_unified(packet)
```

### 2. **Check Operation Results**
Always verify operation success:
```python
# Check driving success
if not component.drive_transaction_unified(packet):
    log.error("Transaction driving failed")
    
# Check memory operations  
success, error = component.write_to_memory_unified(packet)
if not success:
    handle_memory_error(error)
```

### 3. **Use Signal Maps for Non-Standard Interfaces**
When DUT signals don't follow standard naming:
```python
signal_map = {
    'write': 'wr_en',
    'full': 'almost_full',
    'data': 'write_data'
}
component = CustomFIFOComponent(..., signal_map=signal_map)
```

### 4. **Monitor Performance**
Regularly check performance statistics:
```python
stats = component.get_base_stats_unified()
if 'data_collector_stats' in stats:
    collector_stats = stats['data_collector_stats']
    if not collector_stats.get('performance_optimized', False):
        log.warning("Data collection not optimized")
```

### 5. **Proper Initialization Order**
Always follow the correct initialization pattern:
```python
# 1. Initialize FIFOComponentBase
# 2. Initialize cocotb parent class
# 3. Call complete_base_initialization()
# 4. Component-specific setup
```

The FIFOComponentBase provides a robust, high-performance foundation for all FIFO protocol components while maintaining API compatibility and exact timing behavior.
