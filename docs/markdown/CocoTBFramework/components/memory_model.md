# MemoryModel

## Overview

The `MemoryModel` class provides a generic memory model for verification environments. It is optimized using NumPy for improved performance and offers a simple interface for reading and writing data with memory-mapped addressing.

## Features

- NumPy-based memory implementation for performance
- Support for byte-level addressing and strobed writes
- Configurable line sizes and byte counts
- Memory reset and expansion capabilities
- Memory dump for debugging
- Conversion utilities between integers and byte arrays

## Classes

### MemoryModel

The main class providing memory model functionality.

#### Constructor

```python
def __init__(self, num_lines, bytes_per_line, log, preset_values=None, debug=None)
```

- `num_lines`: Number of memory lines
- `bytes_per_line`: Number of bytes per line
- `log`: Logger instance for debugging
- `preset_values`: Optional preset values to initialize memory (must match total size)
- `debug`: Flag for enabling verbose debug output

#### Attributes

- `num_lines`: Number of memory lines
- `bytes_per_line`: Number of bytes per line
- `size`: Total memory size in bytes
- `mem`: NumPy array containing the memory data
- `preset_values`: NumPy array containing the preset values (for reset)

#### Key Methods

- `write(address, data, strobe)`: Write data to memory with byte-level strobe
- `read(address, length)`: Read data from memory
- `reset(to_preset=False)`: Reset memory to zeros or preset values
- `expand(additional_lines)`: Expand memory by adding lines
- `dump()`: Generate a formatted memory dump for debugging
- `integer_to_bytearray(value, byte_length=None)`: Convert integer to little-endian bytearray
- `bytearray_to_integer(byte_array)`: Convert bytearray to integer (little-endian)

## Example Usage

### Basic Memory Operations

```python
from CocoTBFramework.components.memory_model import MemoryModel
import logging

# Create a logger
log = logging.getLogger("memory_log")
log.setLevel(logging.DEBUG)

# Create a 1K memory model (16 lines x 64 bytes)
mem = MemoryModel(num_lines=16, bytes_per_line=64, log=log)

# Write data
address = 0x40
data = bytearray([0xAA, 0xBB, 0xCC, 0xDD])
strobe = 0b1111  # Write all bytes

mem.write(address, data, strobe)

# Read data back
read_data = mem.read(address, 4)
print(f"Read data: {' '.join([f'0x{b:02X}' for b in read_data])}")

# Dump memory content
print(mem.dump())
```

### Strobed Writes

```python
# Write with selective byte strobing
address = 0x100
data = bytearray([0x11, 0x22, 0x33, 0x44])
strobe = 0b1010  # Write only bytes 0 and 2 (bits 1 and 3)

mem.write(address, data, strobe)

# Read the result
read_data = mem.read(address, 4)
print(f"Strobed write result: {' '.join([f'0x{b:02X}' for b in read_data])}")
# Only bytes 0 and 2 should be written, others remain as 0
```

### Memory Reset and Expansion

```python
# Reset the memory to zeros
mem.reset()

# Expand memory by 8 additional lines
mem.expand(additional_lines=8)
print(f"New memory size: {mem.size} bytes ({mem.num_lines} lines)")

# Create a memory with preset values
preset = bytearray([i % 256 for i in range(16 * 64)])
preset_mem = MemoryModel(num_lines=16, bytes_per_line=64, log=log, preset_values=preset)

# Read preset data
read_data = preset_mem.read(0x100, 16)
print(f"Preset data: {' '.join([f'0x{b:02X}' for b in read_data])}")

# Reset to preset values
preset_mem.reset(to_preset=True)
```

### Integer Conversion Utilities

```python
# Convert an integer to bytearray
value = 0x12345678
byte_array = mem.integer_to_bytearray(value, byte_length=4)
print(f"Integer 0x{value:X} as bytearray: {' '.join([f'0x{b:02X}' for b in byte_array])}")

# Convert bytearray back to integer
int_value = mem.bytearray_to_integer(byte_array)
print(f"Bytearray converted back to integer: 0x{int_value:X}")
```

### Integration with Protocol Components

```python
from CocoTBFramework.components.memory_model import MemoryModel
from CocoTBFramework.components.packet import Packet
from CocoTBFramework.components.field_config import FieldConfig

# Create a field configuration for address/data packets
config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create a memory model
mem = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)

# Process a write packet
write_packet = Packet(config, addr=0x1000, data=0xABCD1234)
addr = write_packet.addr
data = mem.integer_to_bytearray(write_packet.data, byte_length=4)
strobe = 0b1111  # Write all bytes

mem.write(addr, data, strobe)

# Process a read packet
read_packet = Packet(config, addr=0x1000, data=0)
addr = read_packet.addr
read_data = mem.read(addr, 4)
read_packet.data = mem.bytearray_to_integer(read_data)

print(f"Read packet data: 0x{read_packet.data:08X}")
```

## Performance Considerations

- Uses NumPy for efficient memory operations
- Vectorized operations for improved performance
- Efficient memory expansion without full reallocation
- Optimized memory reset operations

## Notes

- The `MemoryModel` class is designed to be integrated with protocol-specific verification components
- It can be used as a reference model for checking DUT memory accesses
- The model supports arbitrary byte-addressable memory configurations
- NumPy implementation provides better performance than pure Python approaches

## See Also

- [Packet](packet.md) - Can be used to represent memory transactions
- [FieldConfig](field_config.md) - For defining packet fields to use with MemoryModel

## Navigation

[↑ Components Index](index.md) | [↑ CocoTBFramework Index](../index.md)
