# Packet

## Overview

The `Packet` class provides a generic and extensible foundation for handling protocol transactions in verification environments. It uses the `FieldConfig` class to define its structure and offers advanced features like field masking, bit shifting for FIFO interfaces, caching optimizations for performance, and support for field encoding to display human-readable state names.

## Features

- Generic packet representation for any protocol
- Field-based structure with automatic masking to prevent overflow
- Support for field encoding to display human-readable state names
- Support for FIFO-style bit field transformations
- High-performance implementation with caching optimizations
- Rich formatting and display capabilities
- Built-in timing information for performance analysis
- Equality comparison with customizable field exclusion

## Classes

### Packet

The main packet class for protocol transactions with optimized performance.

#### Constructor

```python
def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]],
             skip_compare_fields: Optional[List[str]] = None, **kwargs)
```

- `field_config`: Either a `FieldConfig` object or a dictionary of field definitions
- `skip_compare_fields`: List of field names to skip during comparison operations
- `**kwargs`: Initial values for fields (e.g., `addr=0x123`, `data=0xABC`)

#### Attributes

- `field_config`: The field configuration defining the packet structure
- `fields`: Dictionary holding the actual field values
- `start_time`: Transaction start time (nanoseconds)
- `end_time`: Transaction end time (nanoseconds)
- `skip_compare_fields`: Fields to skip when comparing packets

#### Key Methods

- `mask_field_value(value, field_name)`: Mask a value to fit within a field's bit width
- `shift_for_fifo(value, field_name)`: Convert a field value to its FIFO representation
- `expand_from_fifo(value, field_name)`: Expand a FIFO value to its full field representation
- `pack_for_fifo()`: Pack the packet into a dictionary for FIFO transmission
- `unpack_from_fifo(fifo_data)`: Unpack FIFO data into full field values
- `get_total_bits()`: Calculate the total number of bits in the packet
- `_format_field(field_name, value)`: Format a field value according to its configuration
- `_get_basic_format(field_name, value)`: Get basic formatted value without encoding
- `formatted(compact=False, show_fifo=False)`: Return a formatted string representation
- `copy()`: Create a copy of this packet

### Caching Support

The module also includes a field cache for performance optimization:

- `_FieldCache`: Class that caches field operations to improve performance
- `get_field_cache_stats()`: Get field cache statistics
- `clear_field_cache()`: Clear the field cache

## Example Usage

### Basic Packet Creation

```python
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig

# Create a field configuration
config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create a packet with initial values
packet = Packet(config, addr=0x1000, data=0xABCD1234)

# Access field values directly
print(f"Address: 0x{packet.addr:X}")
print(f"Data: 0x{packet.data:X}")

# Set field values
packet.addr = 0x2000
packet.data = 0x98765432

# Print the packet
print(packet)
```

### Using Field Encoding

```python
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Create a field config with a state field
field_config = FieldConfig()
field_config.add_field(FieldDefinition(
    name="state", 
    bits=2, 
    format="bin",
    description="State Machine Status"
))

# Set an encoding for the state field
field_config.set_encoding("state", {
    0: "IDLE",
    1: "BUSY", 
    2: "ERROR",
    3: "COMPLETE"
})

# Create a packet with the state field
packet = Packet(field_config, state=2)
print(packet)
# Output:
# Packet:
#   State Machine Status: ERROR (0b10)
```

### Working with FIFO Interfaces

```python
# Create a packet with a field that has active bits
config = FieldConfig()
config.add_field(
    FieldDefinition(
        name="addr",
        bits=32,
        active_bits=(31, 2),  # Only bits 31:2 are active
        format="hex"
    )
)
config.add_field(
    FieldDefinition(
        name="data",
        bits=32,
        format="hex"
    )
)

# Create a packet
packet = Packet(config, addr=0x12345678, data=0xABCDEF01)

# Get the shifted (FIFO) representation of the address
addr_fifo = packet.shift_for_fifo(packet.addr, "addr")
print(f"Full address: 0x{packet.addr:X}")
print(f"FIFO address: 0x{addr_fifo:X}")  # Will be right-shifted by 2 bits

# Pack entire packet for FIFO
fifo_data = packet.pack_for_fifo()
print(f"FIFO data: {fifo_data}")

# Create a new packet from FIFO data
new_packet = Packet(config)
new_packet.unpack_from_fifo(fifo_data)
print(f"Reconstructed packet: {new_packet}")
```

### Error Type Encoding

```python
# Create a field config for an error reporting packet
field_config = FieldConfig()
field_config.add_field(FieldDefinition(
    name="error_type",
    bits=8,
    default=0,
    format="hex",
    display_width=1,
    description="Error type"
))
field_config.add_field(FieldDefinition(
    name="error_id",
    bits=8,
    format="hex",
    description="ID associated with error"
))
field_config.add_field(FieldDefinition(
    name="error_addr",
    bits=32,
    format="hex",
    description="Address associated with error"
))

# Set an encoding for the error_type field
field_config.set_encoding("error_type", {
    1: "AddrTO",   # Address timeout
    2: "DataTO",   # Data timeout
    4: "RespTO",   # Response timeout 
    8: "RespErr"   # Response error
})

# Create a packet with an error
packet = Packet(field_config, error_type=2, error_id=0x1A, error_addr=0x12345000)
print(packet)
# Output:
# Packet:
#   Error type: DataTO (0x02)
#   ID associated with error: 0x1A
#   Address associated with error: 0x12345000
```

### Packet Comparison

```python
# Create two packets
packet1 = Packet(config, addr=0x1000, data=0x12345678)
packet2 = Packet(config, addr=0x1000, data=0x12345678)
packet3 = Packet(config, addr=0x2000, data=0x12345678)

# Compare the packets
print(f"packet1 == packet2: {packet1 == packet2}")
print(f"packet1 == packet3: {packet1 == packet3}")

# Create a packet with skip_compare_fields
packet4 = Packet(config, skip_compare_fields=["addr"], addr=0x3000, data=0x12345678)

# This comparison will ignore the addr field
print(f"packet1 == packet4 (ignoring addr): {packet1 == packet4}")
```

### Timing Information

```python
import cocotb
from cocotb.triggers import Timer

@cocotb.test()
async def test_packet_timing(dut):
    packet = Packet(config, addr=0x1000, data=0xABCD)
    
    # Record start time
    packet.start_time = cocotb.utils.get_sim_time(units='ns')
    
    # Wait some time
    await Timer(100, units='ns')
    
    # Record end time
    packet.end_time = cocotb.utils.get_sim_time(units='ns')
    
    # Print the packet with timing information
    print(packet)
```

### Performance Optimization with Caching

```python
from CocoTBFramework.components.packet import get_field_cache_stats, clear_field_cache

# Create and process many packets
for i in range(1000):
    packet = Packet(config, addr=i, data=i*2)
    # Process packet...

# Check cache statistics
stats = get_field_cache_stats()
print(f"Cache statistics: {stats}")
print(f"Cache hit rate: {stats['hit_rate']:.2f}%")

# Clear cache if needed
clear_field_cache()
```

## Advanced Features

### Handling Undefined Values

The `Packet` class supports representing undefined values (X/Z in simulation) as -1:

```python
# Create a packet with an undefined data value
packet = Packet(config, addr=0x1000, data=-1)
print(packet)  # Will show X/Z for data field

# Equality comparison will fail with undefined values
packet2 = Packet(config, addr=0x1000, data=-1)
print(f"packet == packet2: {packet == packet2}")  # False due to undefined values
```

### Formatted Output Options

```python
packet = Packet(config, addr=0x1234ABCD, data=0x98765432)

# Full formatted output
print(packet)

# Compact representation
print(packet.formatted(compact=True))

# Show FIFO values in compact format
print(packet.formatted(compact=True, show_fifo=True))
```

## Performance Considerations

- Uses caching for repeatedly accessed field information
- Field masks, formatters, and encodings are cached for better performance
- Attribute access is optimized to reduce overhead
- Suitable for high-performance verification environments with many transactions

## Notes

- The `Packet` class provides a foundation for protocol-specific packet classes
- For most protocols, you can use this generic class without subclassing
- Field configuration can be defined once and reused across many packets
- Field encodings make debug output more readable by showing state names instead of raw values
- Performance optimizations are important for large verification environments

## See Also

- [FieldConfig](field_config.md) - Used to define packet structure
- [FieldDefinition](field_config.md) - Used to define individual fields
- [MemoryModel](memory_model.md) - Can be used with packets for memory transactions

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
