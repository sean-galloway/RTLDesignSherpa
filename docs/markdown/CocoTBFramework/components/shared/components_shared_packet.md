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

# packet.py

Generic packet class for protocol testing with thread-safe performance optimizations. This module provides an optimized base Packet class that can be used across different protocols (GAXI, APB, etc.) to handle common packet operations like field management, formatting, and comparisons.

## Overview

The `packet.py` module provides a comprehensive packet handling system designed for verification environments. It features thread-safe caching, automatic field validation, and rich formatting capabilities while maintaining protocol independence.

### Key Features
- **Thread-safe performance optimizations** with field caching
- **Automatic field validation and masking** to prevent overflow
- **Protocol-agnostic design** for use across GAXI, FIFO, APB, AXI4, etc.
- **FIFO packing/unpacking support** for signal-level operations
- **Rich formatting and comparison** capabilities
- **Timing information tracking** for performance analysis

## Thread-Safe Caching System

### _FieldCache

Internal thread-safe cache for field operations to improve performance in parallel testing environments.

#### Features
- **Field masks cache**: Caches field bit masks for validation
- **Field bits cache**: Caches field bit widths
- **Field active bits cache**: Caches active bit ranges
- **Field formatters cache**: Caches formatting functions
- **Field encodings cache**: Caches encoding dictionaries
- **Thread safety**: Uses RLock for concurrent access
- **Performance tracking**: Monitors cache hits and misses

#### Global Functions

##### `get_field_cache_stats() -> Dict[str, Any]`
Get field cache statistics (thread-safe).

```python
stats = get_field_cache_stats()
print(f"Cache hit rate: {stats['hit_rate']:.1f}%")
print(f"Total operations: {stats['hits'] + stats['misses']}")
```

##### `clear_field_cache()`
Clear the field cache (thread-safe).

```python
# Clear cache between test runs
clear_field_cache()
```

## Core Class

### Packet

Generic packet class for handling protocol transactions with thread-safe optimized performance.

#### Constructor

```python
Packet(field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]], 
       skip_compare_fields: Optional[List[str]] = None, 
       **kwargs)
```

**Parameters:**
- `field_config`: Either a FieldConfig object or dictionary of field definitions
- `skip_compare_fields`: List of field names to skip during comparison operations
- `**kwargs`: Initial values for fields (e.g., addr=0x123, data=0xABC)

```python
# Create packet with FieldConfig
config = FieldConfig()
config.add_field(FieldDefinition("addr", 32, format="hex"))
config.add_field(FieldDefinition("data", 32, format="hex"))

packet = Packet(config, addr=0x1000, data=0xDEADBEEF)

# Create packet with dictionary config
field_dict = {
    'addr': {'bits': 32, 'format': 'hex'},
    'data': {'bits': 32, 'format': 'hex'}
}
packet = Packet(field_dict, addr=0x2000, data=0x12345678)
```

#### Core Properties

- `field_config`: FieldConfig object defining packet structure
- `fields`: Dictionary containing current field values
- `skip_compare_fields`: Fields to skip during equality comparison
- `start_time`: Transaction start timestamp
- `end_time`: Transaction end timestamp

## Field Access and Validation

### Direct Attribute Access

Fields can be accessed directly as attributes with automatic validation:

```python
packet.addr = 0x1000      # Sets addr field
packet.data = 0xDEADBEEF  # Sets data field

# Access field values
address = packet.addr     # Gets addr field value
data = packet.data        # Gets data field value
```

### `mask_field_value(value, field_name)`

Mask a value to ensure it doesn't exceed the bit width of the specified field.

**Parameters:**
- `value`: The value to mask
- `field_name`: Name of the field whose bit width determines the mask

**Returns:** Value masked to fit within the field's bit width

```python
# Field is 8 bits wide, value exceeds range
masked_value = packet.mask_field_value(0x1FF, "status")  # Returns 0xFF
```

## FIFO Operations

### `shift_for_fifo(value, field_name)`

Convert a full field value to its FIFO representation by right-shifting based on active_bits.

**Parameters:**
- `value`: The full field value
- `field_name`: Name of the field

**Returns:** Value adjusted according to active_bits configuration for FIFO

```python
# If addr[31:5] is 0x12345678, this returns 0x91A2B3 (shifted right by 5)
fifo_value = packet.shift_for_fifo(0x12345678, "addr")
```

### `expand_from_fifo(value, field_name)`

Expand a FIFO value to its full field representation by left-shifting.

**Parameters:**
- `value`: The FIFO field value
- `field_name`: Name of the field

**Returns:** Value expanded according to active_bits configuration

```python
# If addr[31:5] in FIFO is 0x91A2B3, this returns 0x12345660 (shifted left by 5)
full_value = packet.expand_from_fifo(0x91A2B3, "addr")
```

### `pack_for_fifo()`

Pack the packet into a dictionary suitable for FIFO transmission.

**Returns:** Dictionary with field names and FIFO-adjusted values

```python
fifo_data = packet.pack_for_fifo()
print(fifo_data)  # {'addr': 0x91A2B3, 'data': 0xDEADBEEF}
```

### `unpack_from_fifo(fifo_data)`

Unpack FIFO data into full field values, applying appropriate bit field expansions.

**Parameters:**
- `fifo_data`: Dictionary with field values from FIFO, or a single integer value

**Returns:** Self for chaining

```python
# Unpack dictionary of FIFO values
fifo_data = {'addr': 0x91A2B3, 'data': 0xDEADBEEF}
packet.unpack_from_fifo(fifo_data)

# Unpack single value to 'data' field
packet.unpack_from_fifo(0x12345678)
```

## Formatting and Display

### `formatted(compact=False, show_fifo=False)`

Return a formatted string representation.

**Parameters:**
- `compact`: If True, return a more compact representation
- `show_fifo`: If True, show FIFO values instead of full field values

**Returns:** Formatted string representation

```python
# Detailed formatting
print(packet.formatted())

# Compact formatting
print(packet.formatted(compact=True))

# Show FIFO values
print(packet.formatted(show_fifo=True))
```

### `__str__()`

Provide a detailed string representation with all fields displayed in definition order.

```python
print(packet)
# Output:
# Packet:
#   Address        : 0x00001000
#   Data value     : 0xDEADBEEF
#   Start Time: 1000 ns
#   End Time: 2000 ns
#   Duration: 1000 ns
```

## Comparison and Copying

### `__eq__(other)`

Compare packets for equality, skipping fields in `skip_compare_fields`.

**Parameters:**
- `other`: Another packet to compare with

**Returns:** True if all non-skipped fields match and have defined values

```python
packet1 = Packet(config, addr=0x1000, data=0xDEADBEEF)
packet2 = Packet(config, addr=0x1000, data=0xDEADBEEF)

assert packet1 == packet2  # True

# Undefined values (X/Z represented as -1) cause comparison to fail
packet3 = Packet(config, addr=0x1000, data=-1)
assert packet1 != packet3  # True - undefined data
```

### `copy()`

Create a copy of this packet.

**Returns:** New packet with the same field values

```python
original = Packet(config, addr=0x1000, data=0xDEADBEEF)
copy_packet = original.copy()

# Modify copy without affecting original
copy_packet.data = 0x12345678
assert original.data == 0xDEADBEEF  # Original unchanged
```

## Utility Methods

### `get_total_bits()`

Calculate the total number of bits in the packet.

**Returns:** Total number of bits across all fields

```python
total_bits = packet.get_total_bits()
print(f"Packet size: {total_bits} bits")
```

## Usage Patterns

### Basic Packet Creation and Usage

```python
# Define field configuration
config = FieldConfig()
config.add_field(FieldDefinition("cmd", 4, format="hex", encoding={
    0x0: "NOP", 0x1: "READ", 0x2: "WRITE", 0x3: "BURST"
}))
config.add_field(FieldDefinition("addr", 32, format="hex"))
config.add_field(FieldDefinition("data", 32, format="hex"))

# Create packet with initial values
packet = Packet(config, cmd=0x2, addr=0x1000, data=0xDEADBEEF)

# Access and modify fields
print(f"Command: {packet.cmd}")  # 2
packet.addr = 0x2000
packet.data = 0x12345678

# Display packet
print(packet)
```

### Protocol-Specific Packet Usage

```python
class GAXIWritePacket(Packet):
    """GAXI-specific write packet"""
    
    def __init__(self, **kwargs):
        # Define GAXI write fields
        config = FieldConfig()
        config.add_field(FieldDefinition("awid", 4, format="hex"))
        config.add_field(FieldDefinition("awaddr", 32, format="hex"))
        config.add_field(FieldDefinition("awlen", 8, format="dec"))
        config.add_field(FieldDefinition("awsize", 3, format="hex"))
        config.add_field(FieldDefinition("awburst", 2, format="hex", encoding={
            0: "FIXED", 1: "INCR", 2: "WRAP"
        }))
        
        super().__init__(config, **kwargs)
    
    def is_single_transfer(self):
        return self.awlen == 0
    
    def get_burst_length(self):
        return self.awlen + 1
    
    def calculate_address_range(self):
        bytes_per_beat = 1 << self.awsize
        total_bytes = self.get_burst_length() * bytes_per_beat
        return (self.awaddr, self.awaddr + total_bytes - 1)

# Usage
gaxi_packet = GAXIWritePacket(
    awid=0x5,
    awaddr=0x1000,
    awlen=3,        # 4 beats
    awsize=2,       # 4 bytes per beat
    awburst=1       # INCR
)

print(f"Burst type: {gaxi_packet.formatted()}")
print(f"Address range: 0x{gaxi_packet.calculate_address_range()[0]:X} - 0x{gaxi_packet.calculate_address_range()[1]:X}")
```

### FIFO Interface Usage

```python
class FIFOInterface:
    def __init__(self, packet_config):
        self.config = packet_config
        
    def write_to_fifo(self, packet):
        """Convert packet to FIFO format and write"""
        fifo_data = packet.pack_for_fifo()
        
        # Write each field to appropriate FIFO signal
        for field_name, value in fifo_data.items():
            signal = getattr(self, f"{field_name}_sig")
            signal.value = value
    
    def read_from_fifo(self):
        """Read from FIFO and create packet"""
        packet = Packet(self.config)
        
        # Read from FIFO signals
        fifo_data = {}
        for field_name in self.config.field_names():
            signal = getattr(self, f"{field_name}_sig")
            fifo_data[field_name] = int(signal.value)
        
        # Unpack FIFO data to packet
        packet.unpack_from_fifo(fifo_data)
        return packet
```

### Advanced Field Manipulation

```python
class AdvancedPacket(Packet):
    """Extended packet with additional functionality"""
    
    def set_timestamp(self, timestamp=None):
        """Set timing information"""
        if timestamp is None:
            timestamp = cocotb.utils.get_sim_time()
        self.start_time = timestamp
    
    def complete_transaction(self, end_timestamp=None):
        """Mark transaction as complete"""
        if end_timestamp is None:
            end_timestamp = cocotb.utils.get_sim_time()
        self.end_time = end_timestamp
    
    def get_duration(self):
        """Get transaction duration"""
        if self.start_time and self.end_time:
            return self.end_time - self.start_time
        return None
    
    def validate_fields(self):
        """Validate all field values"""
        errors = []
        
        for field_name in self.field_config.field_names():
            field_def = self.field_config.get_field(field_name)
            value = getattr(self, field_name)
            
            # Check for undefined values
            if value == -1:
                errors.append(f"Field '{field_name}' has undefined value")
            
            # Check field-specific constraints
            max_value = (1 << field_def.bits) - 1
            if value > max_value:
                errors.append(f"Field '{field_name}' value {value} exceeds maximum {max_value}")
        
        return errors
    
    def apply_random_values(self, randomizer):
        """Apply random values using a randomizer"""
        if hasattr(randomizer, 'next'):
            values = randomizer.next()
            for field_name, value in values.items():
                if hasattr(self, field_name):
                    setattr(self, field_name, value)
```

### Performance-Critical Usage

```python
class HighPerformancePacketProcessor:
    """Optimized packet processing for high-throughput scenarios"""
    
    def __init__(self, packet_config):
        self.config = packet_config
        self.packet_pool = []
        self.pool_size = 100
        
        # Pre-allocate packet pool
        for _ in range(self.pool_size):
            self.packet_pool.append(Packet(packet_config))
    
    def get_packet(self):
        """Get packet from pool (avoids allocation overhead)"""
        if self.packet_pool:
            packet = self.packet_pool.pop()
            self._reset_packet(packet)
            return packet
        else:
            # Pool exhausted, create new packet
            return Packet(self.config)
    
    def return_packet(self, packet):
        """Return packet to pool"""
        if len(self.packet_pool) < self.pool_size:
            self.packet_pool.append(packet)
    
    def _reset_packet(self, packet):
        """Reset packet to default values"""
        for field_name, field_def in self.config.items():
            setattr(packet, field_name, field_def.default)
        packet.start_time = 0
        packet.end_time = 0
    
    def process_transaction_batch(self, raw_data_list):
        """Process multiple transactions efficiently"""
        processed_packets = []
        
        for raw_data in raw_data_list:
            packet = self.get_packet()
            packet.unpack_from_fifo(raw_data)
            
            # Process packet
            self._validate_and_transform(packet)
            processed_packets.append(packet)
        
        return processed_packets
    
    def _validate_and_transform(self, packet):
        """Validate and transform packet data"""
        # Apply any necessary transformations
        # Validate protocol-specific constraints
        pass
```

### Test Framework Integration

```python
@cocotb.test()
def packet_comparison_test(dut):
    """Test using packet comparison for validation"""
    
    # Create expected packets
    expected_packets = []
    for i in range(10):
        packet = Packet(config, addr=0x1000 + i*4, data=i*0x100)
        expected_packets.append(packet)
    
    # Monitor actual packets
    actual_packets = []
    
    # Run transactions
    for expected in expected_packets:
        # Drive transaction
        yield drive_packet_to_dut(dut, expected)
        
        # Capture result
        actual = yield capture_packet_from_dut(dut)
        actual_packets.append(actual)
    
    # Compare expected vs actual
    for expected, actual in zip(expected_packets, actual_packets):
        assert expected == actual, f"Packet mismatch: expected {expected}, got {actual}"
    
    # Performance analysis
    cache_stats = get_field_cache_stats()
    cocotb.log.info(f"Cache performance: {cache_stats['hit_rate']:.1f}% hit rate")

@cocotb.coroutine
def drive_packet_to_dut(dut, packet):
    """Drive packet to DUT"""
    fifo_data = packet.pack_for_fifo()
    
    for field_name, value in fifo_data.items():
        signal = getattr(dut, f"{field_name}_i")
        signal.value = value
    
    yield RisingEdge(dut.clk)

@cocotb.coroutine
def capture_packet_from_dut(dut):
    """Capture packet from DUT"""
    # Wait for valid output
    yield RisingEdge(dut.valid_o)
    
    # Capture values
    fifo_data = {}
    for field_name in config.field_names():
        signal = getattr(dut, f"{field_name}_o")
        fifo_data[field_name] = int(signal.value)
    
    # Create packet
    packet = Packet(config)
    packet.unpack_from_fifo(fifo_data)
    return packet
```

## Thread Safety and Performance

### Cache Performance

The packet system includes thread-safe caching for optimal performance:

```python
# Monitor cache performance
def monitor_cache_performance():
    stats = get_field_cache_stats()
    print(f"Cache Statistics:")
    print(f"  Hits: {stats['hits']}")
    print(f"  Misses: {stats['misses']}")
    print(f"  Hit Rate: {stats['hit_rate']:.1f}%")
    print(f"  Cache Sizes: {stats['cache_size']}")

# Clear cache between test runs
def cleanup_between_tests():
    clear_field_cache()
```

### Thread-Safe Usage

The packet system is designed for thread-safe operation:

```python
import threading

def worker_thread(packet_config, thread_id, num_packets):
    """Worker thread that processes packets"""
    for i in range(num_packets):
        packet = Packet(packet_config, addr=thread_id*1000 + i, data=i)
        
        # Thread-safe field access and manipulation
        fifo_data = packet.pack_for_fifo()
        packet.unpack_from_fifo(fifo_data)
        
        # Process packet...

# Create multiple worker threads
threads = []
for thread_id in range(4):
    thread = threading.Thread(target=worker_thread, args=(config, thread_id, 1000))
    threads.append(thread)
    thread.start()

# Wait for completion
for thread in threads:
    thread.join()
```

## Best Practices

### 1. **Use Appropriate Field Configurations**
```python
# Define meaningful field configurations
config = FieldConfig()
config.add_field(FieldDefinition("addr", 32, format="hex", description="Memory address"))
config.add_field(FieldDefinition("data", 32, format="hex", description="Data payload"))
```

### 2. **Handle Undefined Values**
```python
# Check for undefined values before processing
if packet.data != -1:  # -1 indicates X/Z value
    process_valid_data(packet.data)
else:
    handle_undefined_data()
```

### 3. **Use FIFO Operations for Signal Interface**
```python
# Convert to FIFO format for signal driving
fifo_data = packet.pack_for_fifo()
drive_signals(fifo_data)

# Convert from FIFO format when receiving
packet.unpack_from_fifo(captured_fifo_data)
```

### 4. **Leverage Packet Comparison for Validation**
```python
# Use packet equality for test validation
assert expected_packet == actual_packet
```

### 5. **Monitor Cache Performance**
```python
# Check cache performance periodically
if test_count % 1000 == 0:
    stats = get_field_cache_stats()
    if stats['hit_rate'] < 90:
        log.warning(f"Low cache hit rate: {stats['hit_rate']:.1f}%")
```

The Packet class provides a robust, high-performance foundation for protocol verification with thread-safe operation, rich formatting, and comprehensive field management capabilities.
