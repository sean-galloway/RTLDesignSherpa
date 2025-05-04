# FIFO Memory Integration Documentation

## Overview

`fifo_memory_integ.py` provides enhanced memory model integration for FIFO components with robust error handling, boundary checking, and improved diagnostics. It consists of two main classes:

1. **FIFOMemoryInteg**: Utilities for integrating memory models with FIFO components
2. **EnhancedMemoryModel**: Extended memory model with comprehensive features

These classes enable FIFO components to safely interact with memory models while providing detailed diagnostics and preventing common errors.

## Class: FIFOMemoryInteg

```python
class FIFOMemoryInteg:
    """
    Utilities for integrating memory models with FIFO components.
    
    This class provides methods for safely reading and writing to memory models
    with improved error handling, boundary checking, and diagnostics.
    
    It can be used by both master and slave components to standardize memory
    operations and provide better debugging information.
    """
```

### Key Features

- **Safe Memory Operations**:
  - Boundary checking for memory accesses
  - Type validation for data values
  - Size verification for memory operations
  
- **Automatic Field Mapping**:
  - Maps packet fields to memory model fields
  - Supports different field naming conventions
  
- **Enhanced Error Handling**:
  - Detailed error messages
  - Error statistics tracking
  - Overflow and boundary violation detection
  
- **Comprehensive Statistics**:
  - Tracks reads and writes
  - Records error counts by type
  - Monitors boundary violations

### Initialization

```python
def __init__(self, memory_model, component_name="Component", log=None, memory_fields=None):
    """
    Initialize the memory integration.
    
    Args:
        memory_model: Memory model to use
        component_name: Name of the component using this integration (for logging)
        log: Logger instance
        memory_fields: Dictionary mapping memory fields to packet field names
    """
```

### Key Methods

#### Memory Operations

- **write(transaction, check_required_fields=True)**:
  Write transaction data to memory with enhanced error handling.
  
- **read(transaction, update_transaction=True, check_required_fields=True)**:
  Read data from memory based on transaction address.

#### Data Conversion

- **_integer_to_bytearray(value, byte_length)**:
  Convert an integer to a bytearray with safety checks.
  
- **_bytearray_to_integer(byte_array)**:
  Convert a bytearray to an integer.

#### Statistics

- **get_stats()**:
  Get memory operation statistics.
  
- **reset_stats()**:
  Reset memory operation statistics.

### Statistics Tracking

```python
self.stats = {
    'reads': 0,
    'writes': 0,
    'read_errors': 0,
    'write_errors': 0,
    'overflow_masked': 0,
    'boundary_violations': 0
}
```

### Default Memory Field Mapping

```python
self.memory_fields = memory_fields or {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}
```

## Class: EnhancedMemoryModel

```python
class EnhancedMemoryModel:
    """
    Enhanced memory model with improved boundary checking and diagnostics.
    
    This class extends the basic memory model capabilities with better error handling,
    diagnostics, and memory organization features for hardware verification.
    """
```

### Key Features

- **Robust Memory Management**:
  - NumPy-based memory storage for performance
  - Boundary checking for all accesses
  - Support for preset values
  
- **Access Tracking**:
  - Records reads and writes per address
  - Detects uninitialized memory reads
  - Tracks coverage statistics
  
- **Memory Organization**:
  - Logical memory regions with descriptions
  - Per-region statistics and coverage
  - Detailed memory dumps
  
- **Error Prevention**:
  - Type checking for all operations
  - Size validation for memory accesses
  - Overflow detection and prevention
  
- **Diagnostics**:
  - Comprehensive statistics
  - Region-level access analysis
  - Formatted memory dumps

### Initialization

```python
def __init__(self, num_lines, bytes_per_line, log=None, preset_values=None, debug=False):
    """
    Initialize the enhanced memory model.
    
    Args:
        num_lines: Number of memory lines
        bytes_per_line: Bytes per memory line
        log: Logger instance
        preset_values: Optional initial values for memory
        debug: Enable detailed debug logging
    """
```

### Key Methods

#### Memory Operations

- **write(address, data, strobe=None)**:
  Write data to memory with improved error handling and diagnostics.
  
- **read(address, length)**:
  Read data from memory with error checking.
  
- **reset(to_preset=False)**:
  Reset memory to initial state.
  
- **expand(additional_lines)**:
  Expand memory by adding additional lines.

#### Memory Organization

- **define_region(name, start_addr, end_addr, description=None)**:
  Define a named memory region for better organization and diagnostics.
  
- **get_region_access_stats(name)**:
  Get access statistics for a named region.
  
- **dump(include_access_info=False)**:
  Generate a detailed memory dump.

#### Data Conversion

- **integer_to_bytearray(value, byte_length=None)**:
  Convert an integer to a bytearray with enhanced error checking.
  
- **bytearray_to_integer(byte_array)**:
  Convert a bytearray to an integer.

#### Statistics

- **get_stats()**:
  Get memory operation statistics.

### Access Tracking Arrays

```python
# NumPy arrays for memory and access tracking
self.mem = np.zeros(self.size, dtype=np.uint8)
self.read_access_map = np.zeros(self.size, dtype=np.uint32)
self.write_access_map = np.zeros(self.size, dtype=np.uint32)
```

### Memory Regions

```python
# Memory regions for logical organization
self.regions = {}  # name -> (start_addr, end_addr, description)
```

### Statistics

```python
self.stats = {
    'reads': 0,
    'writes': 0,
    'read_errors': 0,
    'write_errors': 0,
    'uninitialized_reads': 0
}
```

## Usage Examples

### Using FIFOMemoryInteg with Components

```python
# Create a memory model
memory_model = EnhancedMemoryModel(num_lines=8, bytes_per_line=4)

# Create memory integration for a master component
master_mem_integ = FIFOMemoryInteg(
    memory_model,
    component_name="Master",
    memory_fields={
        'addr': 'addr',
        'data': 'data',
        'strb': 'strb'
    }
)

# Write to memory from a transaction
transaction = FIFOPacket(field_config)
transaction.addr = 0x00000004
transaction.data = 0xABCDEF01
transaction.strb = 0xF

success, error_msg = master_mem_integ.write(transaction)
if not success:
    print(f"Write error: {error_msg}")
else:
    print("Write successful")

# Create memory integration for a slave component
slave_mem_integ = FIFOMemoryInteg(
    memory_model,
    component_name="Slave"
)

# Read from memory for a transaction
read_txn = FIFOPacket(field_config)
read_txn.addr = 0x00000004

success, data, error_msg = slave_mem_integ.read(read_txn, update_transaction=True)
if not success:
    print(f"Read error: {error_msg}")
else:
    print(f"Read data: 0x{data:X}")
    print(f"Transaction data field: 0x{read_txn.data:X}")
```

### Using EnhancedMemoryModel with Regions

```python
# Create an enhanced memory model
mem_model = EnhancedMemoryModel(
    num_lines=16,
    bytes_per_line=4,
    debug=True
)

# Define memory regions
mem_model.define_region("control", 0, 15, "Control registers")
mem_model.define_region("data", 16, 47, "Data buffer")
mem_model.define_region("status", 48, 63, "Status registers")

# Write to different regions
mem_model.write(0, bytearray([0x01, 0x02, 0x03, 0x04]), 0xF)  # Control region
mem_model.write(16, bytearray([0xA0, 0xA1, 0xA2, 0xA3]), 0xF)  # Data region
mem_model.write(48, bytearray([0xFF, 0x00, 0x00, 0x00]), 0xF)  # Status region

# Read from regions
control_data = mem_model.read(0, 4)
data_buffer = mem_model.read(16, 4)
status_reg = mem_model.read(48, 4)

# Get region statistics
control_stats = mem_model.get_region_access_stats("control")
print(f"Control region: {control_stats['read_percentage'] * 100:.1f}% read coverage")

# Generate a memory dump
dump = mem_model.dump(include_access_info=True)
print(dump)
```

### Using Integer/Bytearray Conversion

```python
# Create a memory model
mem_model = EnhancedMemoryModel(num_lines=8, bytes_per_line=4)

# Convert integer to bytearray
value = 0x12345678
byte_array = mem_model.integer_to_bytearray(value, byte_length=4)
print(f"Integer 0x{value:X} as bytearray: {list(byte_array)}")

# Convert bytearray back to integer
restored_value = mem_model.bytearray_to_integer(byte_array)
print(f"Bytearray back to integer: 0x{restored_value:X}")

# Try with overflow (value too large for byte_length)
try:
    mem_model.integer_to_bytearray(0xFFFFFFFF, byte_length=2)
except OverflowError as e:
    print(f"Caught expected overflow: {e}")
```

### Memory Access Tracking and Analysis

```python
# Create memory model with tracking
mem_model = EnhancedMemoryModel(
    num_lines=8,
    bytes_per_line=4
)

# Write some data
for i in range(4):
    addr = i * 4
    data = bytearray([i*4, i*4+1, i*4+2, i*4+3])
    mem_model.write(addr, data, 0xF)

# Read some data (not all addresses)
mem_model.read(0, 4)
mem_model.read(8, 4)

# Get statistics
stats = mem_model.get_stats()
print(f"Read coverage: {stats['read_coverage']*100:.1f}%")
print(f"Write coverage: {stats['write_coverage']*100:.1f}%")
print(f"Any access coverage: {stats['any_access_coverage']*100:.1f}%")
print(f"Untouched bytes: {stats['untouched_bytes']}")
```

## Integration with FIFO Components

The memory integration classes are designed to work seamlessly with FIFO components:

### Master Component Integration

```python
# In FIFOMaster.__init__
if self.memory_model:
    self.memory_integration = FIFOMemoryInteg(
        self.memory_model,
        component_name=f"Master({self.title})",
        log=self.log,
        memory_fields=self.memory_fields
    )

# In FIFOMaster._driver_send
if hasattr(self, 'memory_integration') and self.memory_model and 'write' in kwargs and kwargs['write']:
    success, error_msg = self.memory_integration.write(transaction)
    if not success:
        self.log.error(f"Master({self.title}): {error_msg}")
```

### Slave Component Integration

```python
# In FIFOSlave.__init__
if self.memory_model:
    self.memory_integration = FIFOMemoryInteg(
        self.memory_model,
        component_name=f"Slave({self.title})",
        log=self.log,
        memory_fields=self.memory_fields
    )

# In FIFOSlave._finish_packet
if hasattr(self, 'memory_integration') and self.memory_model:
    success, data, error_msg = self.memory_integration.read(packet, update_transaction=True)
    if not success:
        self.log.warning(f"Slave({self.title}): {error_msg}")
```

## Error Handling

### FIFOMemoryInteg Error Handling

The `write` method returns a tuple of `(success, error_message)`:

```python
def write(self, transaction, check_required_fields=True) -> Tuple[bool, str]:
    """
    Write transaction data to memory with enhanced error handling.
    
    Args:
        transaction: The transaction to write to memory
        check_required_fields: If True, validate that required fields exist
        
    Returns:
        (success, error_message): Tuple with success flag and error message
    """
    if self.memory_model is None:
        return False, "No memory model available"
        
    try:
        # Get field mapping
        addr_field = self.memory_fields.get('addr', 'addr')
        data_field = self.memory_fields.get('data', 'data')
        strb_field = self.memory_fields.get('strb', 'strb')
        
        # Check if transaction has required fields
        if check_required_fields:
            if not hasattr(transaction, addr_field):
                return False, f"Transaction missing required address field '{addr_field}'"
            if not hasattr(transaction, data_field):
                return False, f"Transaction missing required data field '{data_field}'"
        
        # Get values from transaction
        addr = getattr(transaction, addr_field)
        data = getattr(transaction, data_field)
        
        # Get strobe if available, default to all bytes enabled
        if hasattr(transaction, strb_field):
            strb = getattr(transaction, strb_field)
        else:
            # Calculate appropriate strobe based on data width
            bytes_per_line = self.memory_model.bytes_per_line
            strb = (1 << bytes_per_line) - 1
        
        # Perform boundary checking
        if addr < 0:
            self.stats['boundary_violations'] += 1
            return False, f"Invalid negative address: {addr}"
            
        if addr + self.memory_model.bytes_per_line > self.memory_model.size:
            self.stats['boundary_violations'] += 1
            return False, f"Memory write at 0x{addr:X} would exceed memory bounds (size: {self.memory_model.size})"
        
        # Convert data to bytearray with proper size handling
        try:
            data_bytes = self._integer_to_bytearray(data, self.memory_model.bytes_per_line)
        except OverflowError:
            # If data doesn't fit, mask it
            max_value = (1 << (self.memory_model.bytes_per_line * 8)) - 1
            masked_data = data & max_value
            if self.log:
                self.log.warning(
                    f"{self.component_name}: Data value 0x{data:X} exceeds memory width, masked to 0x{masked_data:X}"
                )
            data_bytes = self._integer_to_bytearray(masked_data, self.memory_model.bytes_per_line)
            self.stats['overflow_masked'] += 1
        
        # Write to memory
        self.memory_model.write(addr, data_bytes, strb)
        if self.log:
            self.log.debug(f"{self.component_name}: Wrote to memory: addr=0x{addr:X}, data=0x{data:X}, strb=0x{strb:X}")
        self.stats['writes'] += 1
        
        return True, ""
        
    except Exception as e:
        error_msg = f"{self.component_name}: Error writing to memory: {str(e)}"
        if self.log:
            self.log.error(error_msg)
        self.stats['write_errors'] += 1
        return False, error_msg
```

The `read` method returns a tuple of `(success, data, error_message)`:

```python
def read(self, transaction, update_transaction=True, check_required_fields=True) -> Tuple[bool, Any, str]:
    """
    Read data from memory based on transaction address.
    
    Args:
        transaction: The transaction containing the address to read from
        update_transaction: If True, update the transaction's data field with read value
        check_required_fields: If True, validate that required fields exist
        
    Returns:
        (success, data, error_message): Tuple with success flag, data read (or None), 
                                       and error message
    """
    if self.memory_model is None:
        return False, None, "No memory model available"
        
    try:
        # Get field mapping
        addr_field = self.memory_fields.get('addr', 'addr')
        data_field = self.memory_fields.get('data', 'data')
        
        # Check if transaction has required fields
        if check_required_fields and not hasattr(transaction, addr_field):
            return False, None, f"Transaction missing required address field '{addr_field}'"
        
        # Get address from transaction
        addr = getattr(transaction, addr_field)
        
        # Perform boundary checking
        if addr < 0:
            self.stats['boundary_violations'] += 1
            return False, None, f"Invalid negative address: {addr}"
            
        if addr + self.memory_model.bytes_per_line > self.memory_model.size:
            self.stats['boundary_violations'] += 1
            return False, None, f"Memory read at 0x{addr:X} would exceed memory bounds (size: {self.memory_model.size})"
        
        # Read from memory
        data_bytes = self.memory_model.read(addr, self.memory_model.bytes_per_line)
        data = self._bytearray_to_integer(data_bytes)
        
        # Update transaction if requested
        if update_transaction and hasattr(transaction, data_field):
            setattr(transaction, data_field, data)
        
        if self.log:
            self.log.debug(f"{self.component_name}: Read from memory: addr=0x{addr:X}, data=0x{data:X}")
        self.stats['reads'] += 1
        
        return True, data, ""
        
    except Exception as e:
        error_msg = f"{self.component_name}: Error reading from memory: {str(e)}"
        if self.log:
            self.log.error(error_msg)
        self.stats['read_errors'] += 1
        return False, None, error_msg
```

### EnhancedMemoryModel Error Handling

The memory model implements comprehensive error handling:

```python
def write(self, address, data, strobe=None):
    """Write data to memory with improved error handling and diagnostics."""
    if not isinstance(data, bytearray):
        raise TypeError("Data must be a bytearray")
        
    start = address
    data_len = len(data)
    end = start + len(data)
    
    # Check for memory overflow
    if end > self.size:
        raise ValueError(f"Write at address 0x{address:X} with size {data_len} exceeds memory bounds (size: {self.size})")
        
    # Ensure the data and strobe lengths match
    if data_len * 8 < strobe.bit_length():
        raise ValueError(f"Data length {data_len} does not match strobe length {strobe.bit_length() // 8}")
```

## Performance Optimizations

### NumPy-based Memory Storage

```python
# Initialize memory using numpy for better performance
if preset_values:
    if len(preset_values) != self.size:
        if log:
            log.warning(f"Preset values length {len(preset_values)} doesn't match memory size {self.size}. Adjusting.")
        
        # Truncate or pad preset values to match memory size
        if len(preset_values) > self.size:
            preset_values = preset_values[:self.size]
        else:
            preset_values = preset_values + [0] * (self.size - len(preset_values))
            
    # Convert to numpy array
    self.mem = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
    self.preset_values = np.frombuffer(bytearray(preset_values), dtype=np.uint8).copy()
else:
    self.mem = np.zeros(self.size, dtype=np.uint8)
    self.preset_values = np.zeros(self.size, dtype=np.uint8)
```

### Vectorized Write Operations

```python
# Convert bytearray to numpy array
data_np = np.frombuffer(data, dtype=np.uint8)

# Create a mask array from the strobe
mask = np.zeros(data_len, dtype=bool)
for i in range(data_len):
    if strobe & (1 << i):
        mask[i] = True
        
        # Update write access map
        self.write_access_map[start + i] += 1

# Apply the masked write operation in one vectorized operation
if np.any(mask):
    indices = np.arange(start, start + data_len)[mask]
    self.mem[indices] = data_np[mask]
```

### Efficient Memory Access Tracking

```python
# Access tracking for diagnostics
self.read_access_map = np.zeros(self.size, dtype=np.uint32)  # Count reads per address
self.write_access_map = np.zeros(self.size, dtype=np.uint32)  # Count writes per address
```

## Best Practices

1. **Always Check Results**: Check return values from memory operations
2. **Handle Errors**: Implement proper error handling for memory operations
3. **Define Memory Regions**: Define logical regions for better organization
4. **Track Statistics**: Monitor memory access statistics for coverage
5. **Use Boundary Checking**: Rely on boundary checking to catch errors
6. **Debug Memory Operations**: Enable debug mode for detailed logging
7. **Use Appropriate Field Mapping**: Ensure field mapping matches your packet format

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
