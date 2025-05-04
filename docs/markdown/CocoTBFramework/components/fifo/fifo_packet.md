# FIFO Packet Documentation

## Overview

`fifo_packet.py` implements the FIFOPacket class, which represents data packets transmitted through FIFO interfaces. It extends the generic Packet class and adds FIFO-specific functionality, optimized field value masking, and transaction tracking capabilities.

## Class: FIFOPacket

```python
class FIFOPacket(Packet):
    """
    Packet class for FIFO protocol with value masking to ensure values stay 
    within field boundaries and mask caching for improved performance
    """
```

### Key Features

- **Field Value Masking**:
  - Ensures field values stay within their bit width boundaries
  - Automatically masks values that exceed field width
  - Caches masks for improved performance
  
- **FIFO-Specific Field Handling**:
  - Methods for packing and unpacking fields for FIFO transmission
  - Support for active bit ranges within fields
  
- **Timing Support**:
  - Integration with randomizers for master and slave timing constraints
  - Storage of transaction start and end times
  
- **Transaction Dependency Tracking**:
  - Support for dependencies between transactions
  - Storage of dependency type and completion status
  
- **Optimization**:
  - Mask caching for improved performance
  - Lazy field value loading
  - Efficient field packing/unpacking

### Initialization

```python
def __init__(self, field_config: Optional[FieldConfig] = None, 
             fields: Optional[Dict[str, int]] = None,
             master_randomizer: Optional[FlexRandomizer] = None,
             slave_randomizer: Optional[FlexRandomizer] = None):
    """
    Initialize a FIFO packet with field masking.

    Args:
        field_config: Field configuration
        fields: Optional initial field values
        master_randomizer: Optional randomizer for master interface
        slave_randomizer: Optional randomizer for slave interface
    """
```

### Key Methods

#### Field Value Masking

- **_mask_field_value(field, value)**:
  Mask a field value according to its maximum allowed value.
  
- **__setitem__(field, value)**:
  Set a field value with automatic masking.
  
- **__getitem__(field)**:
  Get a field value with lazy loading from memory model if needed.

#### Timing and Randomization

- **set_master_randomizer(randomizer)**:
  Set the master randomizer.
  
- **set_slave_randomizer(randomizer)**:
  Set the slave randomizer.
  
- **get_master_delay()**:
  Get the delay for the master interface.
  
- **get_slave_delay()**:
  Get the delay for the slave interface.

#### FIFO Operations

- **pack_for_fifo()**:
  Pack fields for FIFO transmission with automatic masking.
  
- **unpack_from_fifo(data_dict)**:
  Unpack values from FIFO into packet fields with masking.

#### Transaction Tracking

- **set_fifo_metadata(depth, capacity)**:
  Set FIFO-specific metadata for transaction tracking.
  
- **set_dependency(depends_on_index, dependency_type)**:
  Set dependency information for the packet.
  
- **mark_completed()**:
  Mark the transaction as completed.

#### Cache Management

- **clear_cache()**:
  Clear the mask cache.
  
- **get_cache_stats()**:
  Get cache statistics.

#### Utility Methods

- **get_all_field_names()**:
  Get all field names from both the field_config and the packet's fields.

### Field Value Masking

The packet uses field value masking to ensure data integrity:

```python
def _mask_field_value(self, field, value):
    """
    Mask a field value according to its maximum allowed value.
    Uses caching for improved performance.
    """
    # Check cache first
    if field in self._field_masks:
        mask = self._field_masks[field]
        masked_value = value & mask
        if masked_value != value:
            self.log.warning(f"{field} value 0x{value:x} exceeds field width, masked to 0x{masked_value:x}")
        return masked_value
    
    # Calculate mask if not cached
    if self.field_config and field in self.field_config.field_names():
        field_def = self.field_config.get_field(field)
        field_width = field_def.bits
        mask = (1 << field_width) - 1
        
        # Cache the mask for future use
        self._field_masks[field] = mask
        
        # Apply mask
        masked_value = value & mask
        if masked_value != value:
            self.log.warning(f"{field} value 0x{value:x} exceeds field width ({field_width} bits), masked to 0x{masked_value:x}")
        return masked_value

    # If no field config or field not defined, return original value
    return value
```

### FIFO Packing and Unpacking

The packet provides methods for FIFO-specific field handling:

```python
def pack_for_fifo(self) -> Dict[str, Any]:
    """
    Pack fields for FIFO transmission with automatic masking.
    
    This method prepares the packet's fields for transmission through
    the FIFO interface, applying appropriate field masking to ensure values
    fit within their specified bit widths.
    
    Returns:
        Dictionary mapping field names to masked field values
    """
    result = {}
    
    # Process all fields in the order specified by field_config if available
    if self.field_config:
        for field_name in self.field_config.field_names():
            if hasattr(self, field_name) and getattr(self, field_name) is not None:
                value = getattr(self, field_name)
                # Ensure value is properly masked
                masked_value = self._mask_field_value(field_name, value)
                result[field_name] = masked_value
    else:
        # Handle cases where field_config is not available
        # Just include all fields in the packet
        for field_name, value in self._fields.items():
            if value is not None:
                result[field_name] = value
                
    return result
```

```python
def unpack_from_fifo(self, data_dict: Dict[str, Any]):
    """
    Unpack values from FIFO into packet fields with masking.
    
    Args:
        data_dict: Dictionary of field values from FIFO
    """
    for field_name, value in data_dict.items():
        if value is not None:
            # Apply masking as needed
            masked_value = self._mask_field_value(field_name, value)
            setattr(self, field_name, masked_value)
```

### Transaction Dependencies

The packet supports transaction dependencies:

```python
def set_dependency(self, depends_on_index, dependency_type="after"):
    """
    Set dependency information for the packet.
    
    Args:
        depends_on_index: Index of transaction this depends on
        dependency_type: Type of dependency ("after", "immediate", "conditional")
    """
    self.depends_on_index = depends_on_index
    self.dependency_type = dependency_type
```

## Usage Examples

### Basic Packet Creation and Manipulation

```python
# Create a field configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create a packet
packet = FIFOPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01

# Pack for FIFO transmission
fifo_data = packet.pack_for_fifo()
print(f"FIFO data: {fifo_data}")

# Create a new packet and unpack from FIFO data
new_packet = FIFOPacket(field_config)
new_packet.unpack_from_fifo(fifo_data)
print(f"Unpacked addr: 0x{new_packet.addr:X}, data: 0x{new_packet.data:X}")
```

### With Randomized Timing

```python
# Create timing constraints
master_constraints = {
    'write_delay': ([[0, 0], [1, 3], [4, 10]], [0.5, 0.3, 0.2])
}
slave_constraints = {
    'read_delay': ([[0, 1], [2, 5]], [0.7, 0.3])
}

# Create randomizers
master_randomizer = FlexRandomizer(master_constraints)
slave_randomizer = FlexRandomizer(slave_constraints)

# Create packet with randomizers
packet = FIFOPacket(field_config)
packet.set_master_randomizer(master_randomizer)
packet.set_slave_randomizer(slave_randomizer)

# Get randomized delays
master_delay = packet.get_master_delay()
slave_delay = packet.get_slave_delay()
print(f"Master delay: {master_delay} cycles, Slave delay: {slave_delay} cycles")
```

### Setting Transaction Dependencies

```python
# Create packets with dependencies
packet1 = FIFOPacket(field_config)
packet1.data = 0x1000

packet2 = FIFOPacket(field_config)
packet2.data = 0x2000
packet2.set_dependency(depends_on_index=0, dependency_type="after")

packet3 = FIFOPacket(field_config)
packet3.data = 0x3000
packet3.set_dependency(depends_on_index=1, dependency_type="after")

# Process packets in order with dependencies enforced
# ...
```

### With FIFO Metadata

```python
# Create packet with FIFO metadata
packet = FIFOPacket(field_config)
packet.data = 0x12345678
packet.set_fifo_metadata(depth=3, capacity=8)

# Check metadata
fullness = packet.fifo_metadata['fullness_percentage']
print(f"FIFO fullness: {fullness:.1f}%")
```

### Using Transaction IDs

```python
# Create packet with transaction ID
packet = FIFOPacket(field_config)
packet.data = 0x12345678
packet.transaction_id = 12345

# Later, match response to this transaction using the ID
# ...
```

## Field Masks Caching

The packet implements caching for field masks to improve performance:

```python
# Create packet with field mask cache
packet = FIFOPacket(field_config)

# Set values for multiple fields
packet.data = 0x12345678
packet.addr = 0x1000
packet.strb = 0xF

# Check cache statistics
cache_stats = packet.get_cache_stats()
print(f"Cache size: {cache_stats['cache_size']} entries")
print(f"Cached fields: {cache_stats['cached_fields']}")

# Clear cache if needed
packet.clear_cache()
```

## Integration with Other Components

The FIFOPacket class is designed to work with:

- **Packet Class**: Inherits from the generic Packet base class
- **FIFOMaster**: Used to transmit packets to the FIFO
- **FIFOSlave**: Used to receive packets from the FIFO
- **FIFOCommandHandler**: Coordinates packet routing and response matching
- **FIFOSequence**: Generates sequences of packets for testing
- **FlexRandomizer**: Provides randomized timing parameters

## Performance Considerations

1. **Mask Caching**: Cache field masks to avoid recalculating them
2. **Lazy Loading**: Only load field values when needed
3. **Minimal Validation**: Validate field values only when setting them
4. **Efficient Packing**: Pack only valid fields for FIFO transmission
5. **Memory Integration**: Direct integration with memory models

## Best Practices

1. **Always Use Field Configs**: Provide field configurations for proper masking
2. **Set Dependencies Clearly**: Use explicit dependency relationships
3. **Use Transaction IDs**: Assign unique transaction IDs for response matching
4. **Track Metadata**: Use FIFO metadata for transaction context
5. **Check Cache Stats**: Monitor cache performance for optimization

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
