# AXI4 Field Configuration System

This document provides an overview of the updated AXI4 components that use the new `FieldConfig` class for type-safe field definitions.

## Overview

The AXI4 verification components have been enhanced to use the `FieldConfig` class instead of dictionary-based field definitions. This provides several benefits:

- **Type Safety**: Field values are properly masked to their bit width
- **Improved Validation**: Better error messages and protocol verification
- **Enhanced Debugging**: More informative error messages and cleaner logs
- **Better Maintainability**: Clearer separation of concerns and configuration

## Key Components

### Field Configurations

Field configurations are defined using the `FieldConfig` class, which contains a collection of `FieldDefinition` objects:

```python
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Create a field configuration for an AXI4 channel
config = FieldConfig()

# Add field definitions
config.add_field(FieldDefinition(
    name="awid",
    bits=8,
    default=0,
    format="hex",
    display_width=2,
    active_bits=(7, 0),
    description="Write Address ID"
))

# Add more fields...
```

Pre-defined field configurations are provided for each AXI4 channel:

- `AXI4_AW_FIELD_CONFIG`: Write Address channel
- `AXI4_W_FIELD_CONFIG`: Write Data channel
- `AXI4_B_FIELD_CONFIG`: Write Response channel
- `AXI4_AR_FIELD_CONFIG`: Read Address channel
- `AXI4_R_FIELD_CONFIG`: Read Data channel

### AXI4 Packets

The `AXI4Packet` class has been updated to work with the new field configuration system:

```python
from CocoTBFramework.components.axi4.axi4_packets import AXI4Packet

# Create a write address packet
aw_packet = AXI4Packet.create_aw_packet(
    awid=1,
    awaddr=0x1000,
    awlen=7,    # 8 beat burst
    awsize=2,   # 4 bytes per beat
    awburst=1   # INCR
)

# Field values are automatically masked to their proper bit width
```

### AXI4 Master

The `AXI4Master` class has been updated to use field configurations:

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_master

# Create an AXI4 master with custom field widths
master = create_axi4_master(
    dut, "master", "axi", "_", "", clock, ["AW", "W", "B", "AR", "R"],
    id_width=16,
    addr_width=64,
    data_width=128,
    user_width=4
)

# Execute a write transaction
result = await master.write(
    addr=0x1000,
    data=[0xDEADBEEF, 0xCAFEBABE],
    size=2,   # 4 bytes per beat
    burst=1,  # INCR
    id=5
)
```

### AXI4 Slave

The `AXI4Slave` class has been updated to use field configurations:

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave
from CocoTBFramework.components.memory_model import MemoryModel

# Create a memory model
memory = MemoryModel(
    num_lines=1024,
    bytes_per_line=4,
    log=log
)

# Create an AXI4 slave with memory model
slave = create_axi4_slave(
    dut, "slave", "axi", "_", "", clock, ["AW", "W", "B", "AR", "R"],
    id_width=16,
    addr_width=64,
    data_width=128,
    user_width=4,
    memory_model=memory
)

# Start the transaction processor
await slave.start_processor()
```

### AXI4 Monitor

The `AXI4Monitor` class has been updated to use field configurations:

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_monitor

# Create an AXI4 monitor
monitor = create_axi4_monitor(
    dut, "monitor", "axi", "_", "", clock, ["AW", "W", "B", "AR", "R"],
    id_width=16,
    addr_width=64,
    data_width=128,
    user_width=4,
    is_slave_side=False,
    check_protocol=True
)

# Set callbacks for completed transactions
monitor.set_write_callback(handle_write_transaction)
monitor.set_read_callback(handle_read_transaction)
```

## Field Width Adjustment

Field widths can be adjusted for different bus configurations:

```python
from CocoTBFramework.components.axi4.axi4_fields_signals import (
    AXI4_AW_FIELD_CONFIG, AXI4_W_FIELD_CONFIG, AXI4_B_FIELD_CONFIG,
    AXI4_AR_FIELD_CONFIG, AXI4_R_FIELD_CONFIG, adjust_field_configs
)

# Create field configs dictionary
field_configs = {
    'AW': AXI4_AW_FIELD_CONFIG,
    'W': AXI4_W_FIELD_CONFIG,
    'B': AXI4_B_FIELD_CONFIG,
    'AR': AXI4_AR_FIELD_CONFIG,
    'R': AXI4_R_FIELD_CONFIG
}

# Adjust for custom widths
adjusted_configs = adjust_field_configs(
    field_configs, 
    id_width=16, 
    addr_width=64, 
    data_width=128, 
    user_width=4
)
```

## Protocol Validation

The `AXI4Packet` class provides protocol validation methods:

```python
# Create a packet
packet = AXI4Packet.create_aw_packet(
    awid=1,
    awaddr=0x1002,  # Not aligned for 4-byte transfers
    awsize=2,       # 4 bytes
    awburst=1       # INCR
)

# Validate against AXI4 protocol rules
is_valid, error_msg = packet.validate_axi4_protocol()
if not is_valid:
    print(f"Protocol error: {error_msg}")
```

## Burst Address Calculation

The `get_burst_addresses` method calculates all addresses in a burst:

```python
# Create a packet with INCR burst
packet = AXI4Packet.create_aw_packet(
    awaddr=0x1000,
    awlen=3,    # 4 beats
    awsize=2,   # 4 bytes
    awburst=1   # INCR
)

# Calculate all addresses in the burst
addresses = packet.get_burst_addresses()
# Result: [0x1000, 0x1004, 0x1008, 0x100C]
```

## Best Practices

### Field Configuration

- Use the factory functions to create standard field configurations
- Adjust field widths using `adjust_field_configs` rather than modifying directly
- Use `field_config.update_field_width()` to change a specific field's width

### Packet Creation

- Use the factory methods (`create_aw_packet`, etc.) instead of creating packets directly
- Let the packet class handle field masking rather than masking values yourself
- Validate packets against protocol rules before sending them

### Transaction Processing

- Use the `write()` and `read()` methods for simple transactions
- For more complex sequences, create and send individual packets
- Use the protocol validation to catch errors early

## Migration Guide

If you're migrating from the old dictionary-based system, follow these steps:

1. Replace dictionary field configurations with `FieldConfig` objects
2. Update packet creation to use the factory methods
3. Use proper field accessing through attributes instead of dictionary keys
4. Use `adjusted_configs` instead of manually adjusting field widths

## Advanced Features

### Custom Field Configurations

You can create custom field configurations for special requirements:

```python
from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# Create a custom field configuration
custom_config = FieldConfig()

# Add custom fields
custom_config.add_field(FieldDefinition(
    name="custom_field",
    bits=12,
    default=0,
    format="hex",
    display_width=3,
    active_bits=(11, 0),
    description="Custom Field"
))

# Use in your components
# ...
```

### Response Ordering Control

The AXI4Slave component supports different response ordering strategies:

```python
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave

# Create a slave with in-order responses
slave_inorder = create_axi4_slave(
    dut, "slave_inorder", "axi", "_", "", clock, ["AW", "W", "B", "AR", "R"],
    inorder=True
)

# Create a slave with weighted out-of-order responses
slave_ooo = create_axi4_slave(
    dut, "slave_ooo", "axi", "_", "", clock, ["AW", "W", "B", "AR", "R"],
    inorder=False,
    ooo_strategy='weighted'
)

# Set weights for different IDs
slave_ooo.set_ooo_weight(id_value=1, weight=5.0)  # Higher priority
slave_ooo.set_ooo_weight(id_value=2, weight=1.0)  # Lower priority
```
