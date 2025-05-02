# Memory Model Documentation

## Overview
The `MemoryModel` class provides a high-performance memory model for verification environments, using NumPy arrays for efficient storage and manipulation. This implementation serves as a "golden reference" for memory operations in verification components.

## Key Features
- NumPy-based implementation for performance
- Support for byte-addressable memory operations
- Strobe/mask-based write operations
- Memory reset and expansion capabilities
- Efficient data conversion utilities
- Comprehensive memory dumping for debugging

## Class Definition

```python
class MemoryModel:
    """
    NumPy-based memory model for high-performance verification.
    """

    def __init__(self, num_lines, bytes_per_line, log, preset_values=None, debug=None):
        """
        Initialize the memory model.

        Args:
            num_lines: Number of memory lines
            bytes_per_line: Number of bytes per line
            log: Logger instance
            preset_values: Optional initial memory values
            debug: Optional debug flag
        """
```

## Core Methods

### Memory Operations

```python
def write(self, address, data, strobe):
    """
    Write data to memory with strobe masking.

    Args:
        address: Start address for write
        data: Data to write as bytearray
        strobe: Byte mask where 1 enables write for corresponding byte
    
    Raises:
        TypeError: If data is not a bytearray
        ValueError: If write exceeds memory bounds or data/strobe lengths don't match
    """
```
Writes data to memory with strobe (mask) control for selective byte writing.

```python
def read(self, address, length):
    """
    Read data from memory.

    Args:
        address: Start address for read
        length: Number of bytes to read

    Returns:
        bytearray containing the read data
    """
```
Reads data from memory at the specified address.

### Memory Management

```python
def reset(self, to_preset=False):
    """
    Reset memory contents.

    Args:
        to_preset: If True, reset to preset values; otherwise, reset to zeros
    """
```
Resets memory contents either to zeros or to preset values.

```python
def expand(self, additional_lines):
    """
    Expand memory by adding more lines.

    Args:
        additional_lines: Number of lines to add
    """
```
Expands memory by adding additional lines.

```python
def dump(self):
    """
    Generate a formatted dump of memory contents.

    Returns:
        String containing the formatted memory dump
    """
```
Generates a formatted dump of memory contents for debugging.

### Data Conversion

```python
def integer_to_bytearray(self, value, byte_length=None):
    """
    Convert an integer to a bytearray.

    Args:
        value: Integer value to convert
        byte_length: Optional length of resulting bytearray (auto-calculated if None)

    Returns:
        bytearray representation of the integer

    Raises:
        TypeError: If value is not an integer
        ValueError: If value is negative
        OverflowError: If value is too large for the specified byte_length
    """
```
Converts an integer to a bytearray representation.

```python
def bytearray_to_integer(self, byte_array):
    """
    Convert a bytearray to an integer.

    Args:
        byte_array: bytearray to convert

    Returns:
        Integer representation of the bytearray
    """
```
Converts a bytearray to an integer representation.

## Usage Examples

### Basic Memory Operations

```python
# Create logger
import logging
logger = logging.getLogger("memory_model")

# Create memory model with 1024 lines of 4 bytes each (4KB total)
mem = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Write data
address = 0x100
data = bytearray([0xAA, 0xBB, 0xCC, 0xDD])
strobe = 0xF  # All bytes enabled
mem.write(address, data, strobe)

# Read data
read_data = mem.read(address, 4)
print([hex(b) for b in read_data])  # ['0xaa', '0xbb', '0xcc', '0xdd']

# Partial write with strobe
address = 0x104
data = bytearray([0x11, 0x22, 0x33, 0x44])
strobe = 0x5  # Only bytes 0 and 2 enabled
mem.write(address, data, strobe)

# Read back partially written data
read_data = mem.read(address, 4)
print([hex(b) for b in read_data])  # ['0x11', '0x0', '0x33', '0x0']
```

### Memory Reset and Expansion

```python
# Create memory with preset values
preset_data = bytearray([0xFF] * 1024)
mem = MemoryModel(num_lines=256, bytes_per_line=4, log=logger, preset_values=preset_data)

# Write some data
mem.write(0x0, bytearray([0x12, 0x34, 0x56, 0x78]), 0xF)

# Reset to zeros
mem.reset()
read_data = mem.read(0x0, 4)
print([hex(b) for b in read_data])  # ['0x0', '0x0', '0x0', '0x0']

# Reset to preset values
mem.reset(to_preset=True)
read_data = mem.read(0x0, 4)
print([hex(b) for b in read_data])  # ['0xff', '0xff', '0xff', '0xff']

# Expand memory
mem.expand(additional_lines=256)  # Now 512 lines total
print(f"New memory size: {mem.size} bytes")  # 2048 bytes
```

### Data Conversion

```python
# Integer to bytearray conversion
value = 0x12345678
byte_arr = mem.integer_to_bytearray(value, byte_length=4)
print([hex(b) for b in byte_arr])  # ['0x78', '0x56', '0x34', '0x12'] (little-endian)

# Bytearray to integer conversion
int_value = mem.bytearray_to_integer(byte_arr)
print(hex(int_value))  # '0x12345678'

# Auto-calculate byte length
value = 0xABCD
byte_arr = mem.integer_to_bytearray(value)  # byte_length auto-calculated to 2
print([hex(b) for b in byte_arr])  # ['0xcd', '0xab']
```

### Memory Debugging

```python
# Initialize memory with some values
mem = MemoryModel(num_lines=4, bytes_per_line=4, log=logger)
mem.write(0x0, bytearray([0x11, 0x22, 0x33, 0x44]), 0xF)
mem.write(0x4, bytearray([0x55, 0x66, 0x77, 0x88]), 0xF)
mem.write(0x8, bytearray([0x99, 0xAA, 0xBB, 0xCC]), 0xF)
mem.write(0xC, bytearray([0xDD, 0xEE, 0xFF, 0x00]), 0xF)

# Dump memory contents
dump = mem.dump()
print(dump)
# Output:
# ------------------------------------------------------------
# Register    0: Address 0x00000000 - Value 0x44332211
# Register    1: Address 0x00000004 - Value 0x88776655
# Register    2: Address 0x00000008 - Value 0xCCBBAA99
# Register    3: Address 0x0000000C - Value 0x00FFEEDD
# ------------------------------------------------------------
```

### Integration with Verification Components

```python
# Create memory model for a testbench
class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        
        # Create memory model
        self.mem_model = MemoryModel(
            num_lines=1024, 
            bytes_per_line=4,
            log=self.log
        )
        
        # Create memory adapter for protocol interface
        self.mem_adapter = GAXItoMemoryAdapter(self.mem_model, log=self.log)
        
        # Create scoreboard with memory model
        self.scoreboard = AXI4MemoryScoreboard(
            name="AXI4_MEM_SB",
            memory_model=self.mem_model,
            log=self.log
        )
    
    async def init_memory(self):
        """Initialize memory with test data"""
        # Write test pattern
        for i in range(10):
            addr = i * 4
            data = bytearray([(i*4) + j for j in range(4)])
            self.mem_model.write(addr, data, 0xF)
            
        self.log.info("Memory initialized with test pattern")
        self.log.debug(self.mem_model.dump())
```

## Performance Considerations

The `MemoryModel` uses NumPy arrays for high-performance memory operations, offering several advantages:

1. **Vectorized Operations**: The write method uses NumPy's vectorized operations for efficient bulk updates.
2. **Memory Efficiency**: NumPy arrays are more memory-efficient than Python lists for large memory models.
3. **Fast Data Conversion**: NumPy's buffer protocol allows efficient conversion between bytearrays and arrays.

For best performance:

1. **Batch Operations**: Combine small writes into larger operations when possible.
2. **Use Appropriate Data Types**: Use bytearrays for all data operations.
3. **Preallocate Memory**: Create the memory model with sufficient initial size to minimize expansions.
4. **Consider Debug Level**: Set debug=False for performance-critical simulations.

## Error Handling

The `MemoryModel` includes comprehensive error handling for common issues:

1. **Type Errors**: Validates input types (e.g., bytearray for data).
2. **Bounds Checking**: Prevents out-of-bounds memory access.
3. **Size Matching**: Ensures data and strobe sizes are compatible.
4. **Overflow Detection**: Detects when integer values exceed specified byte lengths.

Example of handling memory errors:

```python
try:
    # Attempt to write beyond memory bounds
    mem.write(0x10000, bytearray([0x1, 0x2, 0x3, 0x4]), 0xF)
except ValueError as e:
    logger.error(f"Memory error: {e}")
    # Handle the error, e.g., resize memory or log for debug
    mem.expand(additional_lines=256)
    mem.write(0x10000, bytearray([0x1, 0x2, 0x3, 0x4]), 0xF)
```

## Integration Patterns

### With Protocol Adapters

Memory models are commonly used with protocol adapters that translate between protocol-specific transactions and memory operations:

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Create protocol adapter
adapter = GAXItoMemoryAdapter(mem_model, log=logger)

# Protocol transaction
tx = GAXIPacket(field_config, addr=0x1000, data=0xABCD1234, cmd=1)  # Write

# Write to memory through adapter
adapter.write_to_memory(tx)

# Create read transaction
read_tx = GAXIPacket(field_config, addr=0x1000, cmd=0)  # Read

# Verify read data
expected_data = adapter.read_from_memory(read_tx)
assert expected_data == 0xABCD1234
```

### With Memory Scoreboards

Memory models serve as reference models for scoreboards that verify memory operations:

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Create memory scoreboard
mem_sb = AXI4MemoryScoreboard("MEM_SB", memory_model=mem_model, log=logger)

# Record expected memory write
mem_sb.add_write(addr=0x1000, data=0xABCD1234)

# Verify actual memory read
result = mem_sb.verify_read(addr=0x1000, data=0xABCD1234)
assert result, "Memory read verification failed"
```

## Best Practices

1. **Initialize with Appropriate Size**: Size your memory model based on the expected memory range to be accessed.

2. **Use Strobes for Partial Writes**: Always specify the correct strobe mask for byte-selective writes:
   ```python
   # Write only bytes 0 and 2
   mem.write(addr, data, 0x5)  # 0b0101
   ```

3. **Consistent Byte Ordering**: Be consistent with byte ordering; the model uses little-endian internally.

4. **Regular Memory Dumps**: For debugging, regularly dump and log memory contents:
   ```python
   logger.debug(mem.dump())
   ```

5. **Reset Between Tests**: Reset the memory between test cases:
   ```python
   # Reset to zeros for clean start
   mem.reset()
   ```

6. **Efficient Data Conversion**: Use the provided conversion utilities for consistent handling:
   ```python
   # Convert integer to bytearray
   data = mem.integer_to_bytearray(0x12345678, 4)
   
   # Convert bytearray to integer
   value = mem.bytearray_to_integer(data)
   ```

7. **Error Handling**: Implement proper error handling for out-of-bounds access and other exceptions.

8. **Memory Expansion**: Use expansion judiciously, as it requires memory reallocation:
   ```python
   # Expand only when necessary
   if address >= mem.size:
       mem.expand(additional_lines=(address // mem.bytes_per_line) + 10)
   ```

9. **Integration with Verification Components**: Use adapters to connect with protocol-specific verification components.

10. **Performance Monitoring**: Monitor memory performance, especially for large models or high-frequency operations.
