# memory_model.py

High-performance memory model with integrated diagnostics and access tracking for hardware verification. Provides comprehensive memory operations using NumPy with debugging capabilities, boundary checking, and memory organization features.

## Overview

The `memory_model.py` module provides a sophisticated memory modeling system designed for verification environments. It uses NumPy for high-performance operations while providing extensive diagnostics, access tracking, and memory organization features.

### Key Features
- High-performance NumPy backend for memory operations
- Comprehensive access tracking (read/write operations per address)
- Memory region management for logical organization
- Boundary checking and validation
- Coverage analysis and statistics
- Transaction-based read/write operations
- Detailed memory dumps with access information
- Integration with packet-based protocols

## Core Class

### MemoryModel

High-performance memory model with integrated diagnostics, access tracking, and region management.

#### Constructor

```python
MemoryModel(num_lines, bytes_per_line, log=None, preset_values=None, debug=False)
```

**Parameters:**
- `num_lines`: Number of memory lines
- `bytes_per_line`: Bytes per memory line
- `log`: Logger instance (optional)
- `preset_values`: Optional initial values for memory (list of integers)
- `debug`: Enable detailed debug logging (default: False)

```python
# Create 256-line memory with 4 bytes per line (1KB total)
memory = MemoryModel(num_lines=256, bytes_per_line=4, log=log, debug=True)

# Create memory with preset values
preset_data = [0xFF] * 1024  # Initialize all to 0xFF
memory = MemoryModel(256, 4, preset_values=preset_data)
```

#### Core Properties

- `num_lines`: Number of memory lines
- `bytes_per_line`: Bytes per memory line  
- `size`: Total memory size in bytes
- `mem`: NumPy array containing memory data
- `preset_values`: Original preset values (for reset operations)
- `read_access_map`: NumPy array tracking read counts per address
- `write_access_map`: NumPy array tracking write counts per address
- `regions`: Dictionary of named memory regions
- `stats`: Dictionary containing operation statistics

## Basic Memory Operations

### `write(address, data, strobe=None)`

Write data to memory with error handling and diagnostics.

**Parameters:**
- `address`: Target memory address
- `data`: Data to write (bytearray)
- `strobe`: Optional write strobe (bit mask for byte enables)

**Raises:**
- `TypeError`: If data is not a bytearray
- `ValueError`: If address or data is invalid, or write exceeds bounds

```python
# Basic write operation
data = bytearray([0xDE, 0xAD, 0xBE, 0xEF])
memory.write(address=0x1000, data=data)

# Write with strobe (selective byte writing)
data = bytearray([0x12, 0x34, 0x56, 0x78])
strobe = 0b1010  # Write bytes 1 and 3 only
memory.write(address=0x2000, data=data, strobe=strobe)
```

### `read(address, length)`

Read data from memory with error checking and access tracking.

**Parameters:**
- `address`: Memory address to read from
- `length`: Number of bytes to read

**Returns:** Bytearray containing the read data

**Raises:**
- `ValueError`: If address or length is invalid, or read exceeds bounds

```python
# Read 4 bytes from address 0x1000
data = memory.read(address=0x1000, length=4)
print(f"Read data: {[hex(b) for b in data]}")

# Read entire memory line
line_data = memory.read(address=0x2000, length=memory.bytes_per_line)
```

### `reset(to_preset=False)`

Reset memory to initial state.

**Parameters:**
- `to_preset`: If True, reset to preset values; if False, reset to all zeros

```python
memory.reset()  # Reset to all zeros
memory.reset(to_preset=True)  # Reset to original preset values
```

### `expand(additional_lines)`

Expand memory by adding additional lines.

**Parameters:**
- `additional_lines`: Number of lines to add

```python
# Add 128 more lines to existing memory
memory.expand(additional_lines=128)
print(f"New memory size: {memory.size} bytes")
```

## Memory Regions

### `define_region(name, start_addr, end_addr, description=None)`

Define a named memory region for better organization and diagnostics.

**Parameters:**
- `name`: Region name
- `start_addr`: Starting address (inclusive)
- `end_addr`: Ending address (inclusive)
- `description`: Optional description of the region

**Returns:** Self for method chaining

```python
# Define memory regions
memory.define_region("bootrom", 0x0000, 0x0FFF, "Boot ROM region")
memory.define_region("ram", 0x1000, 0x8FFF, "Main RAM")
memory.define_region("peripherals", 0x9000, 0x9FFF, "Peripheral registers")
memory.define_region("flash", 0xA000, 0xFFFF, "Flash memory")
```

### `get_region_access_stats(name)`

Get access statistics for a named region.

**Parameters:**
- `name`: Region name

**Returns:** Dictionary with region access statistics or None if region doesn't exist

```python
stats = memory.get_region_access_stats("ram")
if stats:
    print(f"RAM region: {stats['total_reads']} reads, {stats['total_writes']} writes")
    print(f"Coverage: {stats['read_percentage']:.1f}% read, {stats['write_percentage']:.1f}% written")
    print(f"Untouched addresses: {stats['untouched_addresses']}")
```

## Transaction-Based Operations

### `write_transaction(transaction, check_required_fields=True, component_name="Component")`

Write transaction data to memory with error handling.

**Parameters:**
- `transaction`: The transaction to write to memory
- `check_required_fields`: If True, validate that required fields exist
- `component_name`: Component name for error messages

**Returns:** Tuple of (success, error_message)

```python
# Write transaction to memory
success, error = memory.write_transaction(packet, component_name="TestMaster")
if success:
    log.info("Transaction written successfully")
else:
    log.error(f"Write failed: {error}")
```

### `read_transaction(transaction, update_transaction=True, check_required_fields=True, component_name="Component")`

Read data from memory based on transaction address.

**Parameters:**
- `transaction`: The transaction containing the address to read from
- `update_transaction`: If True, update the transaction's data field with read value
- `check_required_fields`: If True, validate that required fields exist
- `component_name`: Component name for error messages

**Returns:** Tuple of (success, data, error_message)

```python
# Read transaction from memory
success, data, error = memory.read_transaction(packet, component_name="TestSlave")
if success:
    log.info(f"Read data: 0x{data:X}")
else:
    log.error(f"Read failed: {error}")
```

## Diagnostics and Analysis

### `dump(include_access_info=False)`

Generate a detailed memory dump.

**Parameters:**
- `include_access_info`: If True, include read/write access information

**Returns:** String with the memory dump

```python
# Basic memory dump
dump_str = memory.dump()
print(dump_str)

# Dump with access information
detailed_dump = memory.dump(include_access_info=True)
print(detailed_dump)
```

### `get_stats()`

Get comprehensive memory operation statistics.

**Returns:** Dictionary with statistics including coverage information

```python
stats = memory.get_stats()
print(f"Total reads: {stats['reads']}")
print(f"Total writes: {stats['writes']}")
print(f"Read coverage: {stats['read_coverage']:.1%}")
print(f"Write coverage: {stats['write_coverage']:.1%}")
print(f"Boundary violations: {stats['boundary_violations']}")
```

## Utility Methods

### `integer_to_bytearray(value, byte_length=None)`

Convert an integer to a bytearray with error checking.

**Parameters:**
- `value`: Integer value to convert
- `byte_length`: Length of resulting bytearray (auto-calculated if None)

**Returns:** Bytearray representation of the value

**Raises:**
- `TypeError`: If value is not an integer
- `ValueError`: If value is negative
- `OverflowError`: If value is too large for the specified byte_length

```python
# Convert integer to bytearray
data = memory.integer_to_bytearray(0xDEADBEEF, 4)
print(f"Bytearray: {[hex(b) for b in data]}")

# Auto-calculate length
data = memory.integer_to_bytearray(0x1234)  # Will be 2 bytes
```

### `bytearray_to_integer(byte_array)`

Convert a bytearray to an integer.

**Parameters:**
- `byte_array`: Bytearray to convert

**Returns:** Integer representation of the bytearray

```python
data = bytearray([0xEF, 0xBE, 0xAD, 0xDE])  # Little-endian
value = memory.bytearray_to_integer(data)
print(f"Integer value: 0x{value:X}")  # 0xDEADBEEF
```

## Usage Patterns

### Basic Memory Operations

```python
# Initialize memory
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log, debug=True)

# Write some data
test_data = bytearray([0x12, 0x34, 0x56, 0x78])
memory.write(0x1000, test_data)

# Read it back
read_data = memory.read(0x1000, 4)
assert read_data == test_data

# Check statistics
stats = memory.get_stats()
print(f"Operations: {stats['writes']} writes, {stats['reads']} reads")
```

### Memory Region Management

```python
# Define logical memory regions
memory = MemoryModel(4096, 4, log=log)

# Set up memory map
memory.define_region("vectors", 0x0000, 0x00FF, "Interrupt vectors")
memory.define_region("code", 0x0100, 0x7FFF, "Program code")
memory.define_region("data", 0x8000, 0xEFFF, "Data memory")
memory.define_region("io", 0xF000, 0xFFFF, "I/O registers")

# Use regions in testing
for addr in range(0x8000, 0x8100, 4):  # Write to data region
    data = bytearray([addr & 0xFF, (addr >> 8) & 0xFF, 0x00, 0x00])
    memory.write(addr, data)

# Analyze region usage
data_stats = memory.get_region_access_stats("data")
print(f"Data region usage: {data_stats}")
```

### Transaction-Based Testing

```python
class MemoryTestBench:
    def __init__(self):
        self.memory = MemoryModel(1024, 4, log=log)
        self.memory.define_region("test_area", 0x1000, 0x1FFF, "Test region")
    
    def test_write_read_sequence(self, packets):
        """Test a sequence of write/read transactions"""
        for packet in packets:
            if packet.cmd == 'WRITE':
                success, error = self.memory.write_transaction(packet, component_name="TestMaster")
                assert success, f"Write failed: {error}"
            
            elif packet.cmd == 'READ':
                success, data, error = self.memory.read_transaction(packet, component_name="TestMaster")
                assert success, f"Read failed: {error}"
                
                # Verify data matches expected
                if hasattr(packet, 'expected_data'):
                    assert data == packet.expected_data
    
    def generate_coverage_report(self):
        """Generate detailed coverage analysis"""
        stats = self.memory.get_stats()
        
        # Overall coverage
        print(f"Memory Coverage Report:")
        print(f"  Read coverage: {stats['read_coverage']:.1%}")
        print(f"  Write coverage: {stats['write_coverage']:.1%}")
        print(f"  Untouched bytes: {stats['untouched_bytes']}")
        
        # Per-region coverage
        region_stats = self.memory.get_region_access_stats("test_area")
        if region_stats:
            print(f"Test Area Coverage:")
            print(f"  Total accesses: {region_stats['total_reads'] + region_stats['total_writes']}")
            print(f"  Untouched: {region_stats['untouched_addresses']} addresses")
```

### Advanced Memory Patterns

```python
class AdvancedMemoryModel(MemoryModel):
    """Extended memory model with additional features"""
    
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.access_patterns = {}
        self.hotspots = []
    
    def write(self, address, data, strobe=None):
        """Override write to track access patterns"""
        super().write(address, data, strobe)
        self._track_access_pattern(address, 'write')
    
    def read(self, address, length):
        """Override read to track access patterns"""
        data = super().read(address, length)
        self._track_access_pattern(address, 'read')
        return data
    
    def _track_access_pattern(self, address, operation):
        """Track access patterns for analysis"""
        if address not in self.access_patterns:
            self.access_patterns[address] = {'reads': 0, 'writes': 0, 'sequence': []}
        
        self.access_patterns[address][f'{operation}s'] += 1
        self.access_patterns[address]['sequence'].append(operation)
    
    def find_hotspots(self, min_accesses=10):
        """Find memory hotspots (frequently accessed addresses)"""
        hotspots = []
        for addr, pattern in self.access_patterns.items():
            total_accesses = pattern['reads'] + pattern['writes']
            if total_accesses >= min_accesses:
                hotspots.append((addr, total_accesses, pattern))
        
        # Sort by access count
        hotspots.sort(key=lambda x: x[1], reverse=True)
        self.hotspots = hotspots
        return hotspots
    
    def analyze_access_patterns(self):
        """Analyze memory access patterns"""
        patterns = {
            'sequential_reads': 0,
            'sequential_writes': 0,
            'read_after_write': 0,
            'write_after_read': 0
        }
        
        for addr, pattern in self.access_patterns.items():
            sequence = pattern['sequence']
            for i in range(len(sequence) - 1):
                current = sequence[i]
                next_op = sequence[i + 1]
                
                if current == 'read' and next_op == 'read':
                    patterns['sequential_reads'] += 1
                elif current == 'write' and next_op == 'write':
                    patterns['sequential_writes'] += 1
                elif current == 'write' and next_op == 'read':
                    patterns['read_after_write'] += 1
                elif current == 'read' and next_op == 'write':
                    patterns['write_after_read'] += 1
        
        return patterns
```

### Performance Testing

```python
def benchmark_memory_performance():
    """Benchmark memory model performance"""
    import time
    
    # Create large memory
    memory = MemoryModel(num_lines=65536, bytes_per_line=64)  # 4MB
    
    # Benchmark writes
    start_time = time.time()
    for i in range(10000):
        addr = i * 64
        data = bytearray([i & 0xFF] * 64)
        memory.write(addr, data)
    write_time = time.time() - start_time
    
    # Benchmark reads
    start_time = time.time()
    for i in range(10000):
        addr = i * 64
        data = memory.read(addr, 64)
    read_time = time.time() - start_time
    
    print(f"Performance Results:")
    print(f"  Writes: {10000/write_time:.0f} ops/sec")
    print(f"  Reads: {10000/read_time:.0f} ops/sec")
    
    # Memory usage analysis
    stats = memory.get_stats()
    print(f"  Coverage: {stats['write_coverage']:.1%}")
```

## Error Handling

The MemoryModel includes comprehensive error handling:

### Boundary Checking
```python
try:
    # This will raise ValueError
    memory.write(address=memory.size, data=bytearray([0xFF]))
except ValueError as e:
    print(f"Boundary violation: {e}")
```

### Data Validation
```python
try:
    # This will raise TypeError
    memory.write(address=0x1000, data="not a bytearray")
except TypeError as e:
    print(f"Invalid data type: {e}")
```

### Transaction Error Handling
```python
success, error = memory.write_transaction(invalid_packet)
if not success:
    print(f"Transaction failed: {error}")
    # Handle error gracefully
```

## Integration with Protocols

### GAXI Integration

```python
class GAXIMemorySlave:
    def __init__(self, memory_lines=1024, line_size=4):
        self.memory = MemoryModel(memory_lines, line_size, log=self.log)
        
        # Define GAXI-specific regions
        self.memory.define_region("cacheable", 0x0000, 0x7FFF, "Cacheable memory")
        self.memory.define_region("device", 0x8000, 0xFFFF, "Device memory")
    
    @cocotb.coroutine
    def handle_write(self, packet):
        """Handle GAXI write transaction"""
        success, error = self.memory.write_transaction(packet, component_name="GAXISlave")
        if not success:
            packet.resp = 2  # SLVERR
            self.log.error(f"Write failed: {error}")
        else:
            packet.resp = 0  # OKAY
```

### FIFO Integration

```python
class FIFOMemoryBuffer:
    def __init__(self, depth=256, width=4):
        self.memory = MemoryModel(depth, width, log=self.log)
        self.write_ptr = 0
        self.read_ptr = 0
        self.count = 0
    
    def write_data(self, data):
        """Write data to FIFO buffer"""
        if self.count >= self.memory.num_lines:
            return False  # FIFO full
        
        self.memory.write(self.write_ptr * self.memory.bytes_per_line, data)
        self.write_ptr = (self.write_ptr + 1) % self.memory.num_lines
        self.count += 1
        return True
    
    def read_data(self):
        """Read data from FIFO buffer"""
        if self.count == 0:
            return None  # FIFO empty
        
        data = self.memory.read(self.read_ptr * self.memory.bytes_per_line, self.memory.bytes_per_line)
        self.read_ptr = (self.read_ptr + 1) % self.memory.num_lines
        self.count -= 1
        return data
```

## Best Practices

### 1. **Choose Appropriate Memory Sizes**
```python
# For small tests
memory = MemoryModel(256, 4)  # 1KB

# For comprehensive tests
memory = MemoryModel(16384, 4)  # 64KB

# For stress tests
memory = MemoryModel(262144, 4)  # 1MB
```

### 2. **Use Memory Regions for Organization**
```python
# Define logical memory layout
memory.define_region("boot", 0x0000, 0x0FFF)
memory.define_region("app", 0x1000, 0x7FFF)
memory.define_region("data", 0x8000, 0xEFFF)
memory.define_region("regs", 0xF000, 0xFFFF)
```

### 3. **Monitor Memory Coverage**
```python
# Regular coverage analysis
def check_coverage():
    stats = memory.get_stats()
    if stats['write_coverage'] < 0.8:
        log.warning("Low write coverage detected")
```

### 4. **Handle Errors Gracefully**
```python
# Always check transaction results
success, error = memory.write_transaction(packet)
if not success:
    # Handle error appropriately
    packet.response = 'ERROR'
    log.error(f"Memory operation failed: {error}")
```

### 5. **Use Debug Mode During Development**
```python
# Enable debug for development
memory = MemoryModel(1024, 4, debug=True, log=log)

# Disable for production runs
memory = MemoryModel(1024, 4, debug=False)
```

The MemoryModel provides a robust foundation for memory-centric verification, combining high performance with comprehensive diagnostics and analysis capabilities.
