# AXI4 Memory Model Documentation

## Introduction

Memory models are essential components in the AXI4 verification environment, providing storage for data and enabling verification of read and write operations. This document details the memory model interface, available implementations, and how to use them in AXI4 verification.

## Memory Model Interface

Memory models implement a common interface with these key methods:

```python
class MemoryModelInterface:
    def read(self, address, size):
        """Read data from the specified address"""
        pass
    
    def write(self, address, data, mask=0xFF):
        """Write data to the specified address with optional byte mask"""
        pass
    
    def get_size(self):
        """Get the size of the memory in bytes"""
        pass
    
    def clear(self):
        """Clear all memory contents"""
        pass
```

## SimpleMemoryModel

The `SimpleMemoryModel` is the standard memory model implementation:

### Instantiation

```python
from CocoTBFramework.memory_models import SimpleMemoryModel

# Create a memory model with 64KB of memory, 4 bytes per line
memory = SimpleMemoryModel(
    size=0x10000,           # Memory size in bytes
    byte_width=4            # Bytes per line (typically matches data width/8)
)
```

### Basic Operations

```python
# Write 32-bit value to memory
memory.write(
    address=0x1000,
    data=bytearray([0xDE, 0xAD, 0xBE, 0xEF]),  # Data as bytearray
    mask=0xFF                                   # Byte mask (0xFF = all bytes)
)

# Read 32-bit value from memory
data = memory.read(
    address=0x1000,
    size=4                  # Size in bytes
)

# Clear memory
memory.clear()
```

### Conversion Utilities

```python
# Convert integer to bytearray
data_bytes = memory.integer_to_bytearray(
    value=0xDEADBEEF,
    size=4                  # Size in bytes
)

# Convert bytearray to integer
value = memory.bytearray_to_integer(data_bytes)
```

### Byte Masks

Byte masks control which bytes are written:

```python
# Write with specific byte mask
memory.write(
    address=0x1000,
    data=bytearray([0x11, 0x22, 0x33, 0x44]),
    mask=0x5                # Binary 0101 - only write bytes 0 and 2
)

# Result at 0x1000: [0x11, unchanged, 0x33, unchanged]
```

## SparseMemoryModel

For large or sparse memory spaces, `SparseMemoryModel` is more efficient:

```python
from CocoTBFramework.memory_models import SparseMemoryModel

# Create a sparse memory model with 4GB address space
memory = SparseMemoryModel(
    size=0x100000000,        # 4GB address space
    byte_width=4,            # 4 bytes per line
    page_size=0x1000         # 4KB pages
)
```

The sparse model only allocates memory for pages that are actually accessed.

## MemoryModelWithDelay

For modeling realistic memory behavior:

```python
from CocoTBFramework.memory_models import MemoryModelWithDelay

# Create a memory model with access delays
memory = MemoryModelWithDelay(
    base_model=SimpleMemoryModel(size=0x10000, byte_width=4),
    read_delay_range=(5, 10),   # Random read delay between 5-10 ns
    write_delay_range=(3, 8)    # Random write delay between 3-8 ns
)

# Asynchronous read with delay
await memory.async_read(
    address=0x1000,
    size=4
)

# Asynchronous write with delay
await memory.async_write(
    address=0x1000,
    data=bytearray([0xDE, 0xAD, 0xBE, 0xEF]),
    mask=0xFF
)
```

## Integration with AXI4 Components

### Creating a Slave with Memory Model

```python
from axi4_factory_specialized import create_memory_axi4_slave

# Create a memory-backed slave
slave = create_memory_axi4_slave(
    dut=dut,
    title="memory_slave",
    prefix="s_axi",
    clock=dut.clk,
    memory_model=memory,
    data_width=32,
    log=logger
)
```

### Creating a Memory Scoreboard

```python
from axi4_factory import create_axi4_memory_scoreboard

# Create a scoreboard that uses the memory model for expected values
scoreboard = create_axi4_memory_scoreboard(
    name="memory_scoreboard",
    memory_model=memory,
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    log=logger
)
```

## Memory Initialization Patterns

### Initializing Memory

```python
# Initialize a range with constant pattern
def init_memory_constant(memory, start_addr, size, value):
    for addr in range(start_addr, start_addr + size, memory.bytes_per_line):
        data = memory.integer_to_bytearray(value, memory.bytes_per_line)
        memory.write(addr, data)

# Initialize with address pattern (addr = data)
def init_memory_address(memory, start_addr, size):
    for addr in range(start_addr, start_addr + size, memory.bytes_per_line):
        data = memory.integer_to_bytearray(addr, memory.bytes_per_line)
        memory.write(addr, data)

# Initialize with incrementing pattern
def init_memory_incrementing(memory, start_addr, size, start_value=0):
    value = start_value
    for addr in range(start_addr, start_addr + size, memory.bytes_per_line):
        data = memory.integer_to_bytearray(value, memory.bytes_per_line)
        memory.write(addr, data)
        value += 1

# Initialize with random data
def init_memory_random(memory, start_addr, size, seed=None):
    import random
    if seed is not None:
        random.seed(seed)
    
    for addr in range(start_addr, start_addr + size, memory.bytes_per_line):
        value = random.randint(0, (1 << (memory.bytes_per_line * 8)) - 1)
        data = memory.integer_to_bytearray(value, memory.bytes_per_line)
        memory.write(addr, data)
```

## Memory Access Patterns

### Sequential Access

```python
async def sequential_access(master, memory, start_addr, size, burst_len=15):
    """Perform sequential access to memory"""
    bytes_per_word = 4
    words_per_burst = burst_len + 1
    
    # Calculate number of bursts needed
    word_count = size // bytes_per_word
    burst_count = (word_count + words_per_burst - 1) // words_per_burst
    
    for i in range(burst_count):
        addr = start_addr + (i * words_per_burst * bytes_per_word)
        
        # Calculate burst length for this burst
        remaining_words = word_count - (i * words_per_burst)
        actual_burst_len = min(burst_len, remaining_words - 1)
        if actual_burst_len < 0:
            actual_burst_len = 0
        
        # Read burst
        read_result = await master.read(
            addr=addr,
            burst_type=1,  # INCR
            length=actual_burst_len,
            size=2  # log2(bytes_per_word)
        )
        
        # Verify data
        for j, data in enumerate(read_result['data']):
            mem_addr = addr + (j * bytes_per_word)
            expected_data = memory.bytearray_to_integer(memory.read(mem_addr, bytes_per_word))
            assert data == expected_data, f"Data mismatch at address 0x{mem_addr:08X}: got 0x{data:08X}, expected 0x{expected_data:08X}"
```

### Random Access

```python
async def random_access(master, memory, addr_range, count, seed=None):
    """Perform random access to memory"""
    import random
    if seed is not None:
        random.seed(seed)
    
    start_addr, end_addr = addr_range
    bytes_per_word = 4
    
    # Align addresses to word boundaries
    start_addr = (start_addr // bytes_per_word) * bytes_per_word
    end_addr = (end_addr // bytes_per_word) * bytes_per_word
    
    for _ in range(count):
        # Generate random aligned address
        addr = random.randrange(start_addr, end_addr, bytes_per_word)
        
        # Read data
        read_result = await master.read(
            addr=addr,
            burst_type=1,  # INCR
            length=0,      # Single beat
            size=2         # log2(bytes_per_word)
        )
        
        # Verify data
        expected_data = memory.bytearray_to_integer(memory.read(addr, bytes_per_word))
        assert read_result['data'][0] == expected_data, f"Data mismatch at address 0x{addr:08X}: got 0x{read_result['data'][0]:08X}, expected 0x{expected_data:08X}"
```

## Advanced Memory Models

### Memory Map Model

For modeling memory-mapped registers:

```python
from CocoTBFramework.memory_models import MemoryMapModel

# Define register map
register_map = {
    0x0000: {'name': 'CONTROL', 'reset': 0x00000000, 'mask': 0x0000000F},
    0x0004: {'name': 'STATUS', 'reset': 0x00000001, 'mask': 0x00000007, 'read_only': True},
    0x0008: {'name': 'DATA', 'reset': 0x00000000, 'mask': 0xFFFFFFFF}
}

# Create memory map model
mem_map = MemoryMapModel(
    register_map=register_map,
    base_address=0x1000,
    byte_width=4
)

# Read register
status = mem_map.read(0x1004, 4)  # Read STATUS register

# Write register
mem_map.write(0x1000, bytearray([0x01, 0x00, 0x00, 0x00]))  # Write CONTROL register

# Register callback for read/write events
def control_write_callback(addr, data, mask):
    print(f"CONTROL register written: 0x{data[0]:02X}")

mem_map.set_write_callback(0x1000, control_write_callback)
```

### Memory with Side Effects

For memory with side effects on read/write:

```python
class MemoryWithSideEffects(SimpleMemoryModel):
    def __init__(self, size=0x10000, byte_width=4):
        super().__init__(size, byte_width)
        self.read_callbacks = {}
        self.write_callbacks = {}
    
    def register_read_side_effect(self, addr, callback):
        """Register a callback for read side effect"""
        self.read_callbacks[addr] = callback
    
    def register_write_side_effect(self, addr, callback):
        """Register a callback for write side effect"""
        self.write_callbacks[addr] = callback
    
    def read(self, address, size):
        """Read with side effects"""
        # Call side effect callback if registered
        if address in self.read_callbacks:
            self.read_callbacks[address](address, size)
        
        # Perform normal read
        return super().read(address, size)
    
    def write(self, address, data, mask=0xFF):
        """Write with side effects"""
        # Call side effect callback if registered
        if address in self.write_callbacks:
            self.write_callbacks[address](address, data, mask)
        
        # Perform normal write
        super().write(address, data, mask)

# Usage
memory = MemoryWithSideEffects()

# Register side effects
def trigger_interrupt(addr, data, mask):
    print("Interrupt triggered!")

memory.register_write_side_effect(0x1000, trigger_interrupt)
```

### Cached Memory Model

For simulating cache behavior:

```python
class CachedMemoryModel:
    def __init__(self, backing_memory, cache_size=1024, line_size=64):
        self.backing_memory = backing_memory
        self.cache_size = cache_size
        self.line_size = line_size
        self.byte_width = backing_memory.bytes_per_line
        
        # Initialize cache lines
        self.cache = {}
        self.line_addresses = []
        self.dirty_lines = set()
    
    def read(self, address, size):
        """Read data from cache or backing memory"""
        # Align address to cache line
        line_addr = (address // self.line_size) * self.line_size
        
        # Check if line is in cache
        if line_addr not in self.cache:
            # Cache miss - read from backing memory
            line_data = bytearray()
            for offset in range(0, self.line_size, self.byte_width):
                line_data.extend(self.backing_memory.read(line_addr + offset, self.byte_width))
            
            # Add to cache
            self._add_to_cache(line_addr, line_data)
        
        # Calculate offset within cache line
        offset = address - line_addr
        
        # Return requested data from cache line
        return self.cache[line_addr][offset:offset+size]
    
    def write(self, address, data, mask=0xFF):
        """Write data to cache and mark line as dirty"""
        # Align address to cache line
        line_addr = (address // self.line_size) * self.line_size
        
        # Check if line is in cache
        if line_addr not in self.cache:
            # Cache miss - read from backing memory first
            self.read(line_addr, self.byte_width)
        
        # Calculate offset within cache line
        offset = address - line_addr
        
        # Apply write with mask
        for i, b in enumerate(data):
            if (mask >> i) & 0x1:
                self.cache[line_addr][offset + i] = b
        
        # Mark line as dirty
        self.dirty_lines.add(line_addr)
    
    def flush(self):
        """Flush dirty cache lines to backing memory"""
        for line_addr in list(self.dirty_lines):
            line_data = self.cache[line_addr]
            
            # Write back to backing memory
            for offset in range(0, self.line_size, self.byte_width):
                chunk = line_data[offset:offset+self.byte_width]
                if len(chunk) == self.byte_width:  # Only write complete chunks
                    self.backing_memory.write(line_addr + offset, chunk)
            
            # Clear dirty flag
            self.dirty_lines.remove(line_addr)
    
    def invalidate(self, address, size=None):
        """Invalidate cache line(s)"""
        if size is None:
            # Invalidate single line
            line_addr = (address // self.line_size) * self.line_size
            if line_addr in self.cache:
                if line_addr in self.dirty_lines:
                    # Flush before invalidating
                    line_data = self.cache[line_addr]
                    for offset in range(0, self.line_size, self.byte_width):
                        chunk = line_data[offset:offset+self.byte_width]
                        if len(chunk) == self.byte_width:
                            self.backing_memory.write(line_addr + offset, chunk)
                    self.dirty_lines.remove(line_addr)
                
                # Remove from cache
                del self.cache[line_addr]
                self.line_addresses.remove(line_addr)
        else:
            # Invalidate range of lines
            start_line = (address // self.line_size) * self.line_size
            end_addr = address + size
            end_line = ((end_addr + self.line_size - 1) // self.line_size) * self.line_size
            
            for line_addr in range(start_line, end_line, self.line_size):
                self.invalidate(line_addr)
    
    def _add_to_cache(self, line_addr, line_data):
        """Add line to cache, evicting if necessary"""
        # Check if cache is full
        if len(self.line_addresses) >= self.cache_size // self.line_size:
            # Evict oldest line (simple LRU policy)
            evict_addr = self.line_addresses.pop(0)
            
            # If dirty, write back to backing memory
            if evict_addr in self.dirty_lines:
                evict_data = self.cache[evict_addr]
                for offset in range(0, self.line_size, self.byte_width):
                    chunk = evict_data[offset:offset+self.byte_width]
                    if len(chunk) == self.byte_width:
                        self.backing_memory.write(evict_addr + offset, chunk)
                self.dirty_lines.remove(evict_addr)
            
            # Remove from cache
            del self.cache[evict_addr]
        
        # Add new line
        self.cache[line_addr] = line_data
        self.line_addresses.append(line_addr)

# Usage
backing_memory = SimpleMemoryModel(size=0x10000, byte_width=4)
cached_memory = CachedMemoryModel(backing_memory, cache_size=1024, line_size=64)
```

## Hierarchical Memory Model

For modeling memory hierarchies:

```python
class HierarchicalMemoryModel:
    def __init__(self):
        self.regions = []
        self.default_handler = None
        self.byte_width = 4  # Default byte width
    
    def add_region(self, start_addr, end_addr, memory_model):
        """Add a memory region with specific memory model"""
        self.regions.append({
            'start': start_addr,
            'end': end_addr,
            'model': memory_model
        })
        
        # Update byte width if not set
        if self.byte_width is None:
            self.byte_width = memory_model.bytes_per_line
    
    def set_default_handler(self, memory_model):
        """Set default memory model for unmapped regions"""
        self.default_handler = memory_model
    
    def read(self, address, size):
        """Read from appropriate memory region"""
        # Find appropriate region
        for region in self.regions:
            if region['start'] <= address <= region['end']:
                return region['model'].read(address - region['start'], size)
        
        # Use default handler if available
        if self.default_handler:
            return self.default_handler.read(address, size)
        
        # Address not mapped
        raise ValueError(f"Address 0x{address:08X} not mapped in memory model")
    
    def write(self, address, data, mask=0xFF):
        """Write to appropriate memory region"""
        # Find appropriate region
        for region in self.regions:
            if region['start'] <= address <= region['end']:
                region['model'].write(address - region['start'], data, mask)
                return
        
        # Use default handler if available
        if self.default_handler:
            self.default_handler.write(address, data, mask)
            return
        
        # Address not mapped
        raise ValueError(f"Address 0x{address:08X} not mapped in memory model")
    
    def clear(self):
        """Clear all memory regions"""
        for region in self.regions:
            region['model'].clear()
        
        if self.default_handler:
            self.default_handler.clear()

# Usage
hierarchical_memory = HierarchicalMemoryModel()

# Add RAM region at 0x00000000
ram = SimpleMemoryModel(size=0x10000, byte_width=4)
hierarchical_memory.add_region(0x00000000, 0x0000FFFF, ram)

# Add ROM region at 0x10000000
rom = SimpleMemoryModel(size=0x1000, byte_width=4)
hierarchical_memory.add_region(0x10000000, 0x10000FFF, rom)

# Add memory-mapped registers at 0x20000000
registers = MemoryMapModel(register_map, base_address=0, byte_width=4)
hierarchical_memory.add_region(0x20000000, 0x2000FFFF, registers)

# Set default handler for unmapped regions
hierarchical_memory.set_default_handler(
    MemoryWithSideEffects(size=0x1000, byte_width=4)
)
```

## Multi-Port Memory Model

For modeling memories with multiple access ports:

```python
class MultiPortMemoryModel:
    def __init__(self, size=0x10000, byte_width=4, port_count=2):
        self.backing_memory = SimpleMemoryModel(size, byte_width)
        self.port_count = port_count
        self.byte_width = byte_width
        self.ports = [{
            'busy': False,
            'access_count': 0,
            'last_access_time': 0
        } for _ in range(port_count)]
    
    def get_available_port(self):
        """Get next available port number"""
        for i, port in enumerate(self.ports):
            if not port['busy']:
                return i
        
        # All ports busy
        return None
    
    def read(self, address, size, port=None):
        """Read from memory using specified or next available port"""
        if port is None:
            port = self.get_available_port()
            if port is None:
                raise RuntimeError("All memory ports are busy")
        
        # Check port is valid
        if port < 0 or port >= self.port_count:
            raise ValueError(f"Invalid port number: {port}")
        
        # Mark port as busy
        self.ports[port]['busy'] = True
        self.ports[port]['access_count'] += 1
        self.ports[port]['last_access_time'] = get_sim_time('ns')
        
        # Perform read
        result = self.backing_memory.read(address, size)
        
        # Mark port as free
        self.ports[port]['busy'] = False
        
        return result
    
    def write(self, address, data, mask=0xFF, port=None):
        """Write to memory using specified or next available port"""
        if port is None:
            port = self.get_available_port()
            if port is None:
                raise RuntimeError("All memory ports are busy")
        
        # Check port is valid
        if port < 0 or port >= self.port_count:
            raise ValueError(f"Invalid port number: {port}")
        
        # Mark port as busy
        self.ports[port]['busy'] = True
        self.ports[port]['access_count'] += 1
        self.ports[port]['last_access_time'] = get_sim_time('ns')
        
        # Perform write
        self.backing_memory.write(address, data, mask)
        
        # Mark port as free
        self.ports[port]['busy'] = False
    
    def get_port_stats(self):
        """Get statistics for all ports"""
        return self.ports
    
    def clear(self):
        """Clear memory contents"""
        self.backing_memory.clear()
        
        # Reset port statistics
        for port in self.ports:
            port['access_count'] = 0
            port['last_access_time'] = 0

# Usage
multi_port_memory = MultiPortMemoryModel(size=0x10000, byte_width=4, port_count=2)

# Read/write using specific ports
data = multi_port_memory.read(0x1000, 4, port=0)  # Read from port 0
multi_port_memory.write(0x2000, bytearray([0x11, 0x22, 0x33, 0x44]), port=1)  # Write to port 1

# Get port statistics
stats = multi_port_memory.get_port_stats()
print(f"Port 0 accesses: {stats[0]['access_count']}")
print(f"Port 1 accesses: {stats[1]['access_count']}")
```

## Memory Model with ECC

For modeling memories with error correction:

```python
class ECCMemoryModel:
    def __init__(self, backing_memory, ecc_type='secded'):
        self.backing_memory = backing_memory
        self.byte_width = backing_memory.bytes_per_line
        self.ecc_type = ecc_type
        self.error_injection = {
            'enabled': False,
            'addresses': [],
            'error_type': 'single'  # 'single', 'double', or 'multi'
        }
        self.error_stats = {
            'detected': 0,
            'corrected': 0,
            'uncorrectable': 0
        }
    
    def enable_error_injection(self, addresses, error_type='single'):
        """Enable error injection at specified addresses"""
        self.error_injection['enabled'] = True
        self.error_injection['addresses'] = addresses
        self.error_injection['error_type'] = error_type
    
    def disable_error_injection(self):
        """Disable error injection"""
        self.error_injection['enabled'] = False
    
    def read(self, address, size):
        """Read with ECC checking/correction"""
        data = self.backing_memory.read(address, size)
        
        # Check for injected errors
        if (self.error_injection['enabled'] and 
            address in self.error_injection['addresses']):
            
            # Inject error based on type
            if self.error_injection['error_type'] == 'single':
                # Flip a single bit (bit 0 in first byte)
                data[0] ^= 0x01
                self.error_stats['detected'] += 1
                
                # For SECDED, we can correct single bit errors
                if self.ecc_type == 'secded':
                    data[0] ^= 0x01  # Fix the error
                    self.error_stats['corrected'] += 1
            
            elif self.error_injection['error_type'] == 'double':
                # Flip two bits (bits 0 and 1 in first byte)
                data[0] ^= 0x03
                self.error_stats['detected'] += 1
                self.error_stats['uncorrectable'] += 1
                
                # For SECDED, we can detect but not correct double bit errors
                if self.ecc_type == 'secded':
                    # Raise exception for uncorrectable error
                    raise RuntimeError(f"Uncorrectable ECC error at address 0x{address:08X}")
            
            elif self.error_injection['error_type'] == 'multi':
                # Flip multiple bits
                data[0] ^= 0x0F
                self.error_stats['detected'] += 1
                self.error_stats['uncorrectable'] += 1
                
                # Raise exception for uncorrectable error
                raise RuntimeError(f"Uncorrectable ECC error at address 0x{address:08X}")
        
        return data
    
    def write(self, address, data, mask=0xFF):
        """Write with ECC generation"""
        # For a real ECC implementation, we would calculate and store ECC bits here
        # For this example, we just pass through to backing memory
        self.backing_memory.write(address, data, mask)
    
    def get_error_stats(self):
        """Get ECC error statistics"""
        return self.error_stats

# Usage
backing_memory = SimpleMemoryModel(size=0x10000, byte_width=4)
ecc_memory = ECCMemoryModel(backing_memory, ecc_type='secded')

# Enable error injection
ecc_memory.enable_error_injection([0x1000, 0x2000], error_type='single')

# Read/write
try:
    data = ecc_memory.read(0x1000, 4)  # Will detect and correct error
    print("Read successful after error correction")
except RuntimeError as e:
    print(f"Error: {e}")

# Check error statistics
stats = ecc_memory.get_error_stats()
print(f"Detected errors: {stats['detected']}")
print(f"Corrected errors: {stats['corrected']}")
print(f"Uncorrectable errors: {stats['uncorrectable']}")
```

## Custom Memory Tester

This utility class helps test memory models:

```python
class MemoryModelTester:
    def __init__(self, memory_model, master):
        self.memory = memory_model
        self.master = master
        self.test_results = {
            'tests_run': 0,
            'passed': 0,
            'failed': 0,
            'errors': []
        }
    
    async def test_sequential_access(self, start_addr, size, burst_len=7):
        """Test sequential memory access"""
        self.test_results['tests_run'] += 1
        
        try:
            # Initialize memory with test pattern
            for i in range(size // self.memory.byte_width):
                addr = start_addr + (i * self.memory.byte_width)
                value = 0xA0000000 + i
                data = self.memory.integer_to_bytearray(value, self.memory.byte_width)
                self.memory.write(addr, data)
            
            # Perform sequential access
            bytes_per_word = self.memory.byte_width
            words_per_burst = burst_len + 1
            
            # Calculate number of bursts needed
            word_count = size // bytes_per_word
            burst_count = (word_count + words_per_burst - 1) // words_per_burst
            
            for i in range(burst_count):
                addr = start_addr + (i * words_per_burst * bytes_per_word)
                
                # Calculate burst length for this burst
                remaining_words = word_count - (i * words_per_burst)
                actual_burst_len = min(burst_len, remaining_words - 1)
                if actual_burst_len < 0:
                    actual_burst_len = 0
                
                # Read burst
                read_result = await self.master.read(
                    addr=addr,
                    burst_type=1,  # INCR
                    length=actual_burst_len,
                    size=2 if bytes_per_word == 4 else 3  # log2(bytes_per_word)
                )
                
                # Verify data
                for j, data in enumerate(read_result['data']):
                    mem_addr = addr + (j * bytes_per_word)
                    expected_data = 0xA0000000 + ((mem_addr - start_addr) // bytes_per_word)
                    assert data == expected_data, f"Data mismatch at address 0x{mem_addr:08X}: got 0x{data:08X}, expected 0x{expected_data:08X}"
            
            self.test_results['passed'] += 1
            return True
        
        except Exception as e:
            self.test_results['failed'] += 1
            self.test_results['errors'].append(str(e))
            return False
    
    async def test_random_access(self, addr_range, count, seed=None):
        """Test random memory access"""
        self.test_results['tests_run'] += 1
        
        try:
            import random
            if seed is not None:
                random.seed(seed)
            
            start_addr, end_addr = addr_range
            bytes_per_word = self.memory.byte_width
            
            # Align addresses to word boundaries
            start_addr = (start_addr // bytes_per_word) * bytes_per_word
            end_addr = (end_addr // bytes_per_word) * bytes_per_word
            
            # Initialize memory with address pattern
            for addr in range(start_addr, end_addr, bytes_per_word):
                value = addr  # Address as data
                data = self.memory.integer_to_bytearray(value, bytes_per_word)
                self.memory.write(addr, data)
            
            # Perform random access
            for _ in range(count):
                # Generate random aligned address
                addr = random.randrange(start_addr, end_addr, bytes_per_word)
                
                # Read data
                read_result = await self.master.read(
                    addr=addr,
                    burst_type=1,  # INCR
                    length=0,      # Single beat
                    size=2 if bytes_per_word == 4 else 3  # log2(bytes_per_word)
                )
                
                # Verify data
                expected_data = addr  # Address as data
                assert read_result['data'][0] == expected_data, f"Data mismatch at address 0x{addr:08X}: got 0x{read_result['data'][0]:08X}, expected 0x{expected_data:08X}"
            
            self.test_results['passed'] += 1
            return True
        
        except Exception as e:
            self.test_results['failed'] += 1
            self.test_results['errors'].append(str(e))
            return False
    
    async def test_burst_types(self, start_addr):
        """Test different burst types"""
        self.test_results['tests_run'] += 1
        
        try:
            bytes_per_word = self.memory.byte_width
            
            # Test FIXED burst
            fixed_addr = start_addr
            fixed_data = [0xF0000001, 0xF0000002, 0xF0000003, 0xF0000004]
            
            # Initialize memory
            for i, value in enumerate(fixed_data):
                addr = fixed_addr + (i * bytes_per_word)
                data = self.memory.integer_to_bytearray(value, bytes_per_word)
                self.memory.write(addr, data)
            
            # Read with FIXED burst
            fixed_result = await self.master.read(
                addr=fixed_addr,
                burst_type=0,  # FIXED
                length=3,      # 4 beats
                size=2 if bytes_per_word == 4 else 3
            )
            
            # For FIXED burst, all beats should return data from same address
            for data in fixed_result['data']:
                assert data == fixed_data[0], f"FIXED burst data mismatch: got 0x{data:08X}, expected 0x{fixed_data[0]:08X}"
            
            # Test INCR burst
            incr_addr = start_addr + 0x100
            incr_data = [0xF1000001, 0xF1000002, 0xF1000003, 0xF1000004]
            
            # Initialize memory
            for i, value in enumerate(incr_data):
                addr = incr_addr + (i * bytes_per_word)
                data = self.memory.integer_to_bytearray(value, bytes_per_word)
                self.memory.write(addr, data)
            
            # Read with INCR burst
            incr_result = await self.master.read(
                addr=incr_addr,
                burst_type=1,  # INCR
                length=3,      # 4 beats
                size=2 if bytes_per_word == 4 else 3
            )
            
            # For INCR burst, each beat should return data from sequential addresses
            for i, data in enumerate(incr_result['data']):
                assert data == incr_data[i], f"INCR burst data mismatch at beat {i}: got 0x{data:08X}, expected 0x{incr_data[i]:08X}"
            
            # Test WRAP burst
            wrap_addr = start_addr + 0x200
            wrap_data = [0xF2000001, 0xF2000002, 0xF2000003, 0xF2000004]
            
            # Initialize memory
            for i, value in enumerate(wrap_data):
                addr = wrap_addr + (i * bytes_per_word)
                data = self.memory.integer_to_bytearray(value, bytes_per_word)
                self.memory.write(addr, data)
            
            # Read with WRAP burst
            wrap_result = await self.master.read(
                addr=wrap_addr + (2 * bytes_per_word),  # Start in middle of wrap boundary
                burst_type=2,  # WRAP
                length=3,      # 4 beats
                size=2 if bytes_per_word == 4 else 3
            )
            
            # For WRAP burst starting at index 2, expected order is: 2, 3, 0, 1
            expected_order = [2, 3, 0, 1]
            for i, data in enumerate(wrap_result['data']):
                expected_idx = expected_order[i]
                assert data == wrap_data[expected_idx], f"WRAP burst data mismatch at beat {i}: got 0x{data:08X}, expected 0x{wrap_data[expected_idx]:08X}"
            
            self.test_results['passed'] += 1
            return True
        
        except Exception as e:
            self.test_results['failed'] += 1
            self.test_results['errors'].append(str(e))
            return False
    
    def get_results(self):
        """Get test results"""
        return self.test_results

# Usage
async def run_memory_tests(dut):
    # Create memory and master
    memory = SimpleMemoryModel(size=0x10000, byte_width=4)
    master = create_simple_axi4_master(dut, "master", "m_axi", dut.clk)
    slave = create_memory_axi4_slave(dut, "slave", "s_axi", dut.clk, memory)
    
    # Create tester
    tester = MemoryModelTester(memory, master)
    
    # Start slave
    await slave.start_processor()
    
    # Run tests
    await tester.test_sequential_access(0x1000, 0x100)
    await tester.test_random_access((0x2000, 0x3000), 20)
    await tester.test_burst_types(0x4000)
    
    # Get results
    results = tester.get_results()
    print(f"Tests run: {results['tests_run']}")
    print(f"Passed: {results['passed']}")
    print(f"Failed: {results['failed']}")
    
    if results['failed'] > 0:
        print("Errors:")
        for error in results['errors']:
            print(f"  {error}")
    
    # Stop slave
    await slave.stop_processor()
```

## Conclusion

Memory models are a crucial part of the AXI4 verification environment, providing the foundation for data storage and retrieval. This document has covered the basic memory model interface, the standard SimpleMemoryModel implementation, and more specialized memory models for various use cases.

By choosing the appropriate memory model for your verification needs, you can accurately model the behavior of real memory subsystems, detect issues in memory access patterns, and ensure that your AXI4 implementation correctly handles a wide range of memory scenarios.

Whether you need a simple memory for basic testing, a hierarchical memory for complex systems, or specialized models with cache, multi-port, or ECC features, the memory model components in this environment provide the flexibility and capability to meet your verification requirements.
