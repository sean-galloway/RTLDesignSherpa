# Packet Class Documentation

## Overview
The `Packet` class provides a flexible and optimized framework for representing protocol transactions in digital verification environments. It is designed to work with the `FieldConfig` system to handle field definitions, formatting, and bit manipulations with high performance.

## Key Features
- Field-based structure with automatic bit masking
- Performance optimizations through caching
- Support for protocol-specific bit field operations
- Comprehensive formatting and display capabilities
- FIFO-compatible packing and unpacking
- Robust comparison operators

## Class Structure

The main components of the Packet module include:

1. `_FieldCache`: Internal cache for field operations
2. `Packet`: Main packet class for protocol transactions

## _FieldCache Class

### Purpose
The `_FieldCache` class provides caching for field operations to improve performance by avoiding redundant calculations.

### Class Definition
```python
class _FieldCache:
    """Cache for field operations to improve performance"""

    def __init__(self):
        """Initialize empty caches"""
        # Field masks cache: (field_config_id, field_name) -> mask
        self.field_masks = {}

        # Field bits cache: (field_config_id, field_name) -> bits
        self.field_bits = {}

        # Field active bits cache: (field_config_id, field_name) -> (msb, lsb)
        self.field_active_bits = {}

        # Field format cache: (field_config_id, field_name) -> format_function
        self.field_formatters = {}

        # Statistics
        self.hits = 0
        self.misses = 0
```

### Key Methods

#### Cache Retrieval
```python
def get_mask(self, field_config: FieldConfig, field_name: str) -> int:
    """Get mask for a field (cached)"""
```
Gets or calculates a field mask and caches the result.

```python
def get_bits(self, field_config: FieldConfig, field_name: str) -> int:
    """Get bits for a field (cached)"""
```
Gets or calculates a field's bit width and caches the result.

```python
def get_active_bits(self, field_config: FieldConfig, field_name: str) -> Tuple[int, int]:
    """Get active bits (msb, lsb) for a field (cached)"""
```
Gets or calculates a field's active bits and caches the result.

```python
def get_formatter(self, field_config: FieldConfig, field_name: str):
    """Get a formatting function for a field (cached)"""
```
Gets or creates a formatting function for a field and caches the result.

#### Cache Management
```python
def clear(self):
    """Clear all caches"""
```
Clears all caches.

```python
def get_stats(self) -> Dict[str, Any]:
    """Get cache statistics"""
```
Returns statistics about cache usage.

## Packet Class

### Purpose
The `Packet` class provides a flexible representation of protocol transactions, with automatic field management and bit operations.

### Class Definition
```python
class Packet:
    """
    Generic packet class for handling protocol transactions with optimized performance.

    This class provides a flexible way to define packets with custom fields without
    requiring subclassing for each protocol. Fields are defined through a FieldConfig
    object, and the class handles bit field transformations automatically during
    packing/unpacking.

    Performance optimizations include:
    - Caching of field masks, bits, and formatters
    - Fast field lookup and validation
    - Optimized bit shifting operations for pack/unpack
    """

    def __init__(self, field_config: Union[FieldConfig, Dict[str, Dict[str, Any]]],
                 skip_compare_fields: Optional[List[str]] = None, **kwargs):
        """
        Initialize a packet with the given field configuration.

        Args:
            field_config: Either a FieldConfig object or a dictionary of field definitions
            skip_compare_fields: List of field names to skip during comparison operations
            **kwargs: Initial values for fields (e.g., addr=0x123, data=0xABC)
        """
```

### Key Features

#### Field Management
The packet maintains fields in a dictionary and supports direct attribute access:
```python
# Initialize a packet with fields
packet = Packet(field_config, addr=0x1000, data=0xABCD)

# Access fields as attributes
addr = packet.addr  # Returns 0x1000

# Set fields as attributes (with automatic masking)
packet.data = 0x12345678  # Will be masked to field width
```

#### Value Masking
```python
def mask_field_value(self, value, field_name):
    """
    Mask a value to ensure it doesn't exceed the bit width of the specified field.
    """
```
Automatically masks values to ensure they fit within the field's bit width.

#### FIFO Operations
```python
def shift_for_fifo(self, value, field_name):
    """
    Convert a full field value to its FIFO representation by right-shifting.
    """
```
Converts a field value to its FIFO representation by right-shifting according to active bits.

```python
def expand_from_fifo(self, value, field_name):
    """
    Expand a FIFO value to its full field representation by left-shifting.
    """
```
Expands a FIFO value to its full field representation by left-shifting according to active bits.

```python
def pack_for_fifo(self):
    """
    Pack the packet into a dictionary suitable for FIFO transmission.
    """
```
Packs the packet into a dictionary suitable for FIFO transmission.

```python
def unpack_from_fifo(self, fifo_data):
    """
    Unpack FIFO data into full field values.
    """
```
Unpacks FIFO data into full field values.

#### Field Formatting
```python
def _format_field(self, field_name, value):
    """Format a field value according to its configuration."""
```
Formats a field value according to its configuration.

#### String Representation
```python
def __str__(self):
    """Provide a detailed string representation of the packet."""
```
Provides a detailed string representation of the packet.

```python
def formatted(self, compact=False, show_fifo=False):
    """Return a formatted string representation."""
```
Returns a formatted string representation with options for compact display and FIFO values.

#### Comparison
```python
def __eq__(self, other):
    """Compare packets for equality, skipping fields in skip_compare_fields."""
```
Compares packets for equality, skipping specified fields.

#### Cloning
```python
def copy(self):
    """Create a copy of this packet."""
```
Creates a copy of the packet.

### Global Functions

#### Cache Management
```python
def get_field_cache_stats() -> Dict[str, Any]:
    """Get field cache statistics"""
```
Returns statistics about the field cache.

```python
def clear_field_cache():
    """Clear the field cache"""
```
Clears the field cache.

## Usage Examples

### Basic Packet Usage
```python
# Create field configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create packet with initial values
packet = Packet(field_config, addr=0x1000, data=0xABCD)

# Access fields as attributes
addr = packet.addr  # Returns 0x1000
data = packet.data  # Returns 0xABCD

# Set fields as attributes (with automatic masking)
packet.data = 0x12345678  # Will be masked to field width (e.g., 0x345678)

# Print the packet
print(packet)  # Detailed representation
print(packet.formatted(compact=True))  # Compact representation
```

### FIFO Operations
```python
# Create field configuration with active bits
field_config = FieldConfig()
field_config.add_field(FieldDefinition(
    name="addr",
    bits=32,
    active_bits=(31, 2),  # Only bits 31:2 are active for FIFO
    format="hex"
))
field_config.add_field(FieldDefinition(
    name="data",
    bits=32,
    format="hex"
))

# Create packet
packet = Packet(field_config, addr=0x12345678, data=0xABCD)

# Pack for FIFO
fifo_data = packet.pack_for_fifo()
# fifo_data = {'addr': 0x48D159E, 'data': 0xABCD}
# addr is right-shifted by 2 bits

# Create new packet and unpack from FIFO
new_packet = Packet(field_config)
new_packet.unpack_from_fifo(fifo_data)

# Now new_packet.addr = 0x12345678 (left-shifted)
# and new_packet.data = 0xABCD
```

### Comparison
```python
# Create two packets
packet1 = Packet(field_config, addr=0x1000, data=0xABCD)
packet2 = Packet(field_config, addr=0x1000, data=0xABCD)
packet3 = Packet(field_config, addr=0x2000, data=0xABCD)

# Compare packets
print(packet1 == packet2)  # True
print(packet1 == packet3)  # False

# Create packet with timing information
packet4 = Packet(field_config, addr=0x1000, data=0xABCD)
packet4.start_time = 100
packet4.end_time = 200

# Compare with default skip_compare_fields
print(packet1 == packet4)  # True (timing fields are skipped by default)

# Create packet with custom skip_compare_fields
packet5 = Packet(
    field_config,
    skip_compare_fields=['data', 'start_time', 'end_time'],
    addr=0x1000,
    data=0x1234
)

# Compare with different data (data field is skipped in comparison)
print(packet1 == packet5)  # True
```

### Packet Copying
```python
# Create a packet
packet = Packet(field_config, addr=0x1000, data=0xABCD)
packet.start_time = 100
packet.end_time = 200

# Create a copy
copy = packet.copy()

# Modify the original
packet.addr = 0x2000

# The copy remains unchanged
print(copy.addr)  # 0x1000
print(copy.start_time)  # 100
```

### Cache Statistics
```python
# Get cache statistics
stats = get_field_cache_stats()
print(f"Cache hits: {stats['hits']}")
print(f"Cache misses: {stats['misses']}")
print(f"Hit rate: {stats['hit_rate']:.2f}%")
print(f"Cache size: {stats['cache_size']}")

# Clear the cache if needed
clear_field_cache()
```

## Best Practices

1. **Use with FieldConfig**: Always use the `Packet` class with a well-defined `FieldConfig` to ensure proper field validation and formatting.

2. **Leverage Direct Attribute Access**: Access fields directly as attributes for cleaner code:
   ```python
   # Good
   packet.addr = 0x1000
   
   # Avoid
   packet.fields['addr'] = 0x1000
   ```

3. **Use FIFO Operations for Bit Field Handling**: When working with active bit ranges, use the FIFO packing/unpacking methods to handle bit shifting automatically.

4. **Specify Skip Compare Fields**: When comparing packets, specify which fields should be ignored in the comparison:
   ```python
   packet = Packet(
       field_config,
       skip_compare_fields=['timestamp', 'metadata'],
       addr=0x1000,
       data=0xABCD
   )
   ```

5. **Format for Display**: Use the `formatted()` method with appropriate parameters for different display contexts:
   ```python
   # Detailed view
   print(packet)
   
   # Compact view
   print(packet.formatted(compact=True))
   
   # Show FIFO values
   print(packet.formatted(show_fifo=True))
   ```

6. **Copy for Independence**: Use the `copy()` method when you need an independent copy of a packet:
   ```python
   original = Packet(field_config, addr=0x1000)
   modified = original.copy()
   modified.addr = 0x2000  # Doesn't affect original
   ```

7. **Monitor Cache Performance**: For high-volume verification, monitor cache performance and clear the cache if hit rate decreases significantly:
   ```python
   stats = get_field_cache_stats()
   if stats['hit_rate'] < 50.0:
       clear_field_cache()
   ```
