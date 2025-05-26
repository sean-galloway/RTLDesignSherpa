# GAXIPacket Component

## Overview

The `GAXIPacket` class serves as the fundamental data structure for GAXI transactions, representing the information exchanged between master and slave components. It extends the base `Packet` class with GAXI-specific features like field value masking, randomization support, and dependency tracking.

## Key Features

- Automatic field value masking to ensure values stay within field boundaries
- Optimized mask caching for improved performance
- Support for master and slave randomizers for timing control
- Dynamic field access through both attribute and dictionary-style access
- Custom string formatting for debug output
- Pack/unpack methods for data conversion between different formats

## Class Definition

```python
class GAXIPacket(Packet):
    def __init__(self, field_config=None, fields=None,
                master_randomizer=None, slave_randomizer=None):
        # ...
```

## Parameters

- **field_config**: Field configuration defining the packet structure
- **fields**: Optional initial field values
- **master_randomizer**: Optional randomizer for master interface
- **slave_randomizer**: Optional randomizer for slave interface

## Field Configuration

The packet structure is defined by a `FieldConfig` object that specifies the fields, their bit widths, default values, formatting, and active bits. Each field becomes an accessible attribute of the packet.

Example field configuration:
```python
field_config = FieldConfig()
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})
```

## Properties and Methods

### Mask Handling

```python
def _mask_field_value(self, field, value):
    """Mask a field value according to its maximum allowed value"""
    
def clear_cache(self):
    """Clear the mask cache"""
    
def get_cache_stats(self):
    """Get cache statistics"""
```

### Field Access

```python
def __setitem__(self, field, value):
    """Set a field value with masking"""
    
def __getitem__(self, field):
    """Get a field value"""
    
def __getattr__(self, name):
    """Get a field value by attribute access"""
    
def __setattr__(self, name, value):
    """Set a field value by attribute access with masking"""
```

### Randomization Support

```python
def set_master_randomizer(self, randomizer):
    """Set the master randomizer"""
    
def set_slave_randomizer(self, randomizer):
    """Set the slave randomizer"""
    
def get_master_delay(self):
    """Get the delay for the master interface"""
    
def get_slave_delay(self):
    """Get the delay for the slave interface"""
```

### Data Conversion

```python
def pack_for_fifo(self):
    """Pack fields into a dictionary suitable for FIFO transmission"""
    
def unpack_from_fifo(self, data_dict):
    """Unpack fields from a dictionary received from FIFO"""
```

### String Formatting

```python
def formatted(self, compact=False):
    """Format the packet for display"""
    
def __str__(self):
    """String representation"""
    
def __repr__(self):
    """Detailed string representation"""
```

## Usage Example

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

# Create a packet
packet = GAXIPacket(field_config)

# Set field values using attribute access
packet.addr = 0x1000
packet.data = 0xABCDEF01
packet.strb = 0xF

# Access fields
print(f"Address: 0x{packet.addr:X}")
print(f"Data: 0x{packet.data:X}")
print(f"Strobe: 0b{packet.strb:04b}")

# Set field values using dictionary-style access
packet['addr'] = 0x2000
packet['data'] = 0x12345678

# Field value masking in action
packet.data = 0x1234567890ABCDEF  # Too large for 32-bit field
print(f"Masked data: 0x{packet.data:X}")  # Will be masked to 0x90ABCDEF

# Display the packet
print(packet.formatted())
print(packet.formatted(compact=True))
```

## Randomization Example

```python
# Create randomizers for master and slave
master_randomizer = FlexRandomizer({
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
})
slave_randomizer = FlexRandomizer({
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
})

# Create a packet with randomizers
packet = GAXIPacket(field_config, 
                    master_randomizer=master_randomizer,
                    slave_randomizer=slave_randomizer)

# Set field values
packet.addr = 0x1000
packet.data = 0xABCDEF01

# Get delays for transmission
master_delay = packet.get_master_delay()
slave_delay = packet.get_slave_delay()

print(f"Master delay: {master_delay} cycles")
print(f"Slave delay: {slave_delay} cycles")
```

## Pack/Unpack Methods Example

```python
# Create a packet with multiple fields
packet = GAXIPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01
packet.strb = 0xF

# Pack the fields for FIFO transmission
packed_data = packet.pack_for_fifo()
print(f"Packed data: {packed_data}")
# Output: {'addr': 0x1000, 'data': 0xABCDEF01, 'strb': 0xF}

# Create a new packet and unpack the data
new_packet = GAXIPacket(field_config)
new_packet.unpack_from_fifo(packed_data)

print(f"Unpacked address: 0x{new_packet.addr:X}")
print(f"Unpacked data: 0x{new_packet.data:X}")
print(f"Unpacked strobe: 0b{new_packet.strb:04b}")
```

## Field Comparison Example

```python
# Create two packets
packet1 = GAXIPacket(field_config)
packet1.addr = 0x1000
packet1.data = 0xABCDEF01

packet2 = GAXIPacket(field_config)
packet2.addr = 0x1000
packet2.data = 0xABCDEF01

# Compare packets
if packet1 == packet2:
    print("Packets match")
else:
    print("Packets are different")

# Modify one packet
packet2.data = 0x12345678

# Compare again
if packet1 == packet2:
    print("Packets match")
else:
    print("Packets are different")

# Check specific field differences
diff_fields = []
for field in field_config.field_names():
    if packet1[field] != packet2[field]:
        diff_fields.append(field)

print(f"Different fields: {diff_fields}")
```

## Mask Caching Example

```python
# Create a packet with multiple fields
packet = GAXIPacket(field_config)

# Set field values multiple times
for i in range(100):
    packet.addr = 0x1000 + i
    packet.data = 0xABCDEF00 + i

# Check cache statistics
cache_stats = packet.get_cache_stats()
print(f"Cache size: {cache_stats['cache_size']}")
print(f"Cached fields: {cache_stats['cached_fields']}")

# Clear the cache
packet.clear_cache()

# Check cache statistics again
cache_stats = packet.get_cache_stats()
print(f"Cache size after clearing: {cache_stats['cache_size']}")
```

## Tips and Best Practices

1. **Field Configuration**: Define field configurations carefully, especially bit widths
2. **Value Masking**: Let the packet handle masking automatically instead of manually masking values
3. **Attribute Access**: Use attribute access (packet.field) for clearer and more readable code
4. **Formatting**: Use the formatted() method for consistent and readable debug output
5. **Randomization**: Set randomizers at packet creation time for consistent timing behavior
6. **Performance**: Use the built-in mask caching for better performance with many packets
7. **Equality Comparison**: Use the built-in equality comparison for easy packet matching
8. **Packet Copying**: Use copy.deepcopy() to create independent copies of packets
9. **Field Naming**: Use consistent field naming conventions across all packet types

## Navigation

[↑ GAXI Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
