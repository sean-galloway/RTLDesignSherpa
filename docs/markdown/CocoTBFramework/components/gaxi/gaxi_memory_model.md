# Enhanced Memory Integration for GAXI Components

## Overview

The `EnhancedMemoryIntegration` class provides improved memory integration utilities for GAXI master and slave components. It offers robust error handling, boundary checking, and comprehensive diagnostics to ensure reliable memory operations during verification.

## Key Features

- Safely reads and writes to memory models with automatic error handling
- Performs boundary checking to prevent invalid memory accesses
- Masks values to fit within field boundaries
- Provides detailed error messages for debugging
- Collects statistics on memory operations
- Integrates seamlessly with GAXIMaster and GAXISlave components
- Handles integer-to-bytearray and bytearray-to-integer conversions

## Class Definition

```python
class EnhancedMemoryIntegration:
    def __init__(self, memory_model, component_name="Component", log=None, memory_fields=None):
        # ...
```

## Parameters

- **memory_model**: Memory model to use for data storage
- **component_name**: Name of the component using this integration (for logging)
- **log**: Logger instance
- **memory_fields**: Dictionary mapping memory fields to packet field names

## Key Methods

### Memory Operations

```python
def write(self, transaction, check_required_fields=True):
    """Write transaction data to memory with enhanced error handling"""
    
def read(self, transaction, update_transaction=True, check_required_fields=True):
    """Read data from memory based on transaction address"""
```

### Data Conversion

```python
def _integer_to_bytearray(self, value, byte_length):
    """Convert an integer to a bytearray with safety checks"""
    
def _bytearray_to_integer(self, byte_array):
    """Convert a bytearray to an integer"""
```

### Statistics

```python
def get_stats(self):
    """Get memory operation statistics"""
    
def reset_stats(self):
    """Reset memory operation statistics"""
```

## Enhanced Memory Model

The framework also includes an `EnhancedMemoryModel` class that extends the basic memory model capabilities:

```python
class EnhancedMemoryModel:
    def __init__(self, num_lines, bytes_per_line, log=None, preset_values=None, debug=False):
        # ...
```

Key features of the Enhanced Memory Model:

- Improved boundary checking and error handling
- Access tracking for read/write operations
- Named memory regions for logical organization
- Comprehensive statistics collection
- Numpy-based implementation for better performance
- Visualization of memory contents
- Detection of uninitialized memory accesses

## Usage Example

```python
# Create a memory model
memory_model = MemoryModel(
    num_lines=1024,
    bytes_per_line=4
)

# Create memory integration for a master component
master_memory = EnhancedMemoryIntegration(
    memory_model,
    component_name="Master",
    memory_fields={
        'addr': 'addr',
        'data': 'data',
        'strb': 'strb'
    }
)

# Create a packet
packet = GAXIPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01
packet.strb = 0xF

# Write to memory using the integration
success, error_msg = master_memory.write(packet)
if not success:
    print(f"Write error: {error_msg}")
else:
    print(f"Write successful to address 0x{packet.addr:X}")

# Read from memory using the integration
success, data, error_msg = master_memory.read(packet, update_transaction=False)
if not success:
    print(f"Read error: {error_msg}")
else:
    print(f"Read data: 0x{data:X}")

# Check memory statistics
stats = master_memory.get_stats()
print(f"Reads: {stats['reads']}")
print(f"Writes: {stats['writes']}")
print(f"Read errors: {stats['read_errors']}")
print(f"Write errors: {stats['write_errors']}")
print(f"Overflow masked: {stats['overflow_masked']}")
```

## Integration with GAXI Components

```python
# Create a field configuration
field_config = FieldConfig()
field_config.add_field_dict('addr', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Address value'
})
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})
field_config.add_field_dict('strb', {
    'bits': 4,
    'default': 0xF,
    'format': 'bin',
    'display_width': 4,
    'active_bits': (3, 0),
    'description': 'Byte strobe'
})

# Create a memory model
memory_model = MemoryModel(
    num_lines=1024,
    bytes_per_line=4
)

# Create master and slave components with memory integration
master = GAXIMaster(
    dut, 'Master', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model,
    memory_fields={
        'addr': 'addr',
        'data': 'data',
        'strb': 'strb'
    }
)

slave = GAXISlave(
    dut, 'Slave', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model,
    memory_fields={
        'addr': 'addr',
        'data': 'data',
        'strb': 'strb'
    }
)

# Create and send a packet (memory operations happen automatically)
packet = GAXIPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01
packet.strb = 0xF
await master.send(packet)

# Access memory statistics
master_stats = master.get_memory_stats()
slave_stats = slave.get_memory_stats()

print(f"Master memory writes: {master_stats['writes']}")
print(f"Slave memory reads: {slave_stats['reads']}")
```

## Enhanced Memory Model Example

```python
# Create an enhanced memory model
memory_model = EnhancedMemoryModel(
    num_lines=1024,
    bytes_per_line=4,
    debug=True
)

# Define logical memory regions
memory_model.define_region("registers", 0x0000, 0x00FF, "Control Registers")
memory_model.define_region("buffer", 0x1000, 0x1FFF, "Data Buffer")
memory_model.define_region("status", 0x2000, 0x20FF, "Status Area")

# Write to memory
data = memory_model.integer_to_bytearray(0xABCDEF01, 4)
memory_model.write(0x1000, data)

# Read from memory
read_data = memory_model.read(0x1000, 4)
value = memory_model.bytearray_to_integer(read_data)
print(f"Read value: 0x{value:X}")

# Get memory dump
print(memory_model.dump(include_access_info=True))

# Get region statistics
reg_stats = memory_model.get_region_access_stats("registers")
buf_stats = memory_model.get_region_access_stats("buffer")

print(f"Register region reads: {reg_stats['total_reads']}")
print(f"Buffer region writes: {buf_stats['total_writes']}")
print(f"Untouched addresses in buffer: {buf_stats['untouched_addresses']}")
```

## Error Handling Example

```python
# Create memory integration
memory_integration = EnhancedMemoryIntegration(
    memory_model,
    component_name="ErrorTest",
    memory_fields={
        'addr': 'addr',
        'data': 'data',
        'strb': 'strb'
    }
)

# Create packets with potential errors
packet1 = GAXIPacket(field_config)
packet1.addr = 0xFFFFFFFF  # Address outside memory bounds
packet1.data = 0x12345678

packet2 = GAXIPacket(field_config)
packet2.addr = 0x1000
packet2.data = 0x123456789ABCDEF0  # Data too large for 32-bit field

# Try to write packet with invalid address
success, error_msg = memory_integration.write(packet1)
print(f"Write to invalid address: {'Success' if success else 'Failed'}")
print(f"Error message: {error_msg}")

# Try to write packet with oversized data (will be masked)
success, error_msg = memory_integration.write(packet2)
print(f"Write with oversized data: {'Success' if success else 'Failed'}")
print(f"Error message: {error_msg}")

# Try to read from invalid address
success, data, error_msg = memory_integration.read(packet1)
print(f"Read from invalid address: {'Success' if success else 'Failed'}")
print(f"Error message: {error_msg}")

# Check error statistics
stats = memory_integration.get_stats()
print(f"Write errors: {stats['write_errors']}")
print(f"Read errors: {stats['read_errors']}")
print(f"Overflow masked: {stats['overflow_masked']}")
```

## Tips and Best Practices

1. **Component Name**: Always provide a descriptive component name for clear error messages
2. **Memory Fields Mapping**: Define memory field mappings carefully to match your packet structure
3. **Error Handling**: Always check success return values from read/write operations
4. **Statistics Monitoring**: Regularly check memory statistics to detect issues
5. **Logical Regions**: Use named memory regions for better organization and diagnostics
6. **Debugging**: Enable debug mode for detailed logging of memory operations
7. **Boundary Checking**: Leverage automatic boundary checking to catch invalid accesses
8. **Access Tracking**: Use access tracking to verify memory coverage
9. **Uninitialized Access**: Monitor uninitialized_reads statistic to catch potential bugs
10. **Memory Dump**: Use memory dump feature for comprehensive memory state inspection

## Navigation

[↑ GAXI Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
