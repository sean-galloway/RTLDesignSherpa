# GAXI Scoreboard Documentation

## Overview

The GAXI (Generic AXI) Scoreboard module provides specialized components for verifying GAXI protocol transactions. GAXI is a simplified version of the AXI protocol used for internal verification purposes. This module includes:

1. `GAXIScoreboard`: Core verification component for GAXI transactions
2. `TransformScoreboard`: Support for protocol transformation and verification
3. `GAXItoMemoryAdapter`: Interface to memory models for data verification

## GAXIScoreboard Class

### Purpose

The `GAXIScoreboard` provides core functionality for verifying GAXI protocol transactions. It supports both the legacy configuration approach and the new field configuration system.

### Class Definition

```python
class GAXIScoreboard(BaseScoreboard):
    """Scoreboard for GAXI transactions"""

    def __init__(self, name, field_config, log=None):
        """
        Initialize the scoreboard with the given field configuration.
        
        Args:
            name: Name of the scoreboard
            field_config: Field configuration (FieldConfig object or dictionary)
            log: Logger instance
        """
```

### Key Features

#### Flexible Configuration

The scoreboard supports both the newer `FieldConfig` class and legacy dictionary-based configuration:
```python
# Convert dict to FieldConfig if needed
if isinstance(field_config, dict):
    self.field_config = FieldConfig.validate_and_create(field_config)
else:
    self.field_config = field_config
```

#### Transaction Comparison

```python
def _compare_transactions(self, expected, actual):
    """
    Compare GAXI packets for equality.
    
    Args:
        expected: Expected transaction
        actual: Actual transaction
        
    Returns:
        True if transactions match, False otherwise
    """
```
Validates that both transactions are `GAXIPacket` objects and uses their built-in comparison.

#### Enhanced Mismatch Logging

```python
def _log_mismatch(self, expected, actual):
    """
    Enhanced mismatch logging for GAXI packets.
    
    Args:
        expected: Expected transaction
        actual: Actual transaction
    """
```
Provides detailed field-by-field comparison of mismatched transactions, with formatting for both the new and legacy packet classes.

## TransformScoreboard Class

### Purpose

The `TransformScoreboard` extends the functionality of the `BaseScoreboard` by adding support for protocol transformation, allowing verification across different protocols.

### Class Definition

```python
class TransformScoreboard(BaseScoreboard):
    """Scoreboard that handles protocol transformations"""

    def __init__(self, name, transformer, target_scoreboard, log=None):
        """
        Initialize a transform scoreboard.
        
        Args:
            name: Name of the scoreboard
            transformer: Transformer to convert transactions
            target_scoreboard: Target scoreboard for verification
            log: Logger instance
        """
```

### Key Features

#### Protocol Transformation

```python
def add_expected(self, transaction):
    """
    Transform source transaction and add resulting transactions to expected queue.
    
    Args:
        transaction: Transaction to transform and add
    """
```
Transforms the source transaction to the target protocol and adds the results to the target scoreboard.

```python
def add_actual(self, transaction):
    """
    Add actual transaction with channel information.
    
    Args:
        transaction: Actual transaction to add
    """
```
Adds the actual transaction directly to the target scoreboard.

#### Delegation to Target Scoreboard

```python
def report(self):
    """
    Generate report using target scoreboard.
    
    Returns:
        Error count from target scoreboard
    """
```
Delegates report generation to the target scoreboard.

```python
def clear(self):
    """Clear target scoreboard"""
```
Clears the target scoreboard.

## GAXItoMemoryAdapter Class

### Purpose

The `GAXItoMemoryAdapter` provides an interface between GAXI packets and memory models, facilitating verification against memory references.

### Class Definition

```python
class GAXItoMemoryAdapter:
    """
    Adapter for memory model integration with GAXI packets.
    Converts between GAXI packets and memory read/write operations.
    """

    def __init__(self, memory_model, field_map=None, log=None):
        """
        Initialize the adapter.

        Args:
            memory_model: Memory model for storage
            field_map: Mapping of memory operations to packet fields
            log: Logger
        """
```

### Key Features

#### Field Mapping

The adapter supports custom mapping between GAXI fields and memory operations:
```python
# Default field mapping if not provided
self.field_map = field_map or {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}
```

#### Memory Operations

```python
def write_to_memory(self, packet):
    """
    Write packet data to memory model.

    Args:
        packet: GAXI packet with write data

    Returns:
        True if successful, False otherwise
    """
```
Writes data from a GAXI packet to the memory model, handling both new and legacy packet formats.

```python
def read_from_memory(self, packet):
    """
    Read data from memory model based on packet address.

    Args:
        packet: GAXI packet with address to read from

    Returns:
        Data value read from memory, or None if error
    """
```
Reads data from the memory model based on the address in a GAXI packet, handling both new and legacy packet formats.

## Usage Examples

### Basic GAXI Scoreboard

```python
# Create a field configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create GAXI scoreboard
gaxi_sb = GAXIScoreboard("GAXI_SB", field_config, log=logger)

# Add expected transaction
expected_tx = GAXIPacket(field_config, addr=0x1000, data=0xABCD1234)
gaxi_sb.add_expected(expected_tx)

# Add actual transaction (triggers comparison)
actual_tx = GAXIPacket(field_config, addr=0x1000, data=0xABCD1234)
gaxi_sb.add_actual(actual_tx)

# Check results
result = gaxi_sb.result()  # 1.0 for perfect match
print(gaxi_sb.report())    # Detailed report
```

### Protocol Transformation

```python
# Create field configurations for source and target protocols
source_config = create_source_protocol_config()
target_config = create_target_protocol_config()

# Create transformer
transformer = SourceToTargetTransformer(source_config, target_config, log=logger)

# Create target scoreboard
target_sb = TargetScoreboard("Target_SB", target_config, log=logger)

# Create transform scoreboard
transform_sb = TransformScoreboard("Transform_SB", transformer, target_sb, log=logger)

# Add expected source transaction (will be transformed)
source_tx = SourcePacket(source_config, field1=value1, field2=value2)
transform_sb.add_expected(source_tx)

# Add actual target transaction
target_tx = TargetPacket(target_config, field1=value1, field2=value2)
transform_sb.add_actual(target_tx)

# Check results
result = transform_sb.result()
print(transform_sb.report())
```

### Memory Model Integration

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Create GAXI field configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create adapter
gaxi_mem_adapter = GAXItoMemoryAdapter(mem_model, log=logger)

# Create GAXI packet
write_packet = GAXIPacket(field_config, addr=0x1000, data=0xABCD1234, strb=0xF)

# Write to memory
success = gaxi_mem_adapter.write_to_memory(write_packet)

# Create read packet
read_packet = GAXIPacket(field_config, addr=0x1000)

# Read from memory
read_data = gaxi_mem_adapter.read_from_memory(read_packet)
print(f"Read data: 0x{read_data:X}")  # Should print 0xABCD1234
```

## Field Configuration

The GAXI scoreboard supports both the new `FieldConfig` class and legacy dictionary-based configuration:

### New FieldConfig Approach

```python
# Create standard address/data configuration
field_config = FieldConfig.create_standard(addr_width=32, data_width=32)

# Create data-only configuration
data_config = FieldConfig.create_data_only(data_width=64)

# Create multi-data configuration
multi_config = FieldConfig.create_multi_data(
    addr_width=4,
    ctrl_width=4,
    data_width=8,
    num_data=4
)
```

### Legacy Dictionary Approach

```python
field_config = {
    'addr': {
        'bits': 32,
        'default': 0,
        'format': 'hex'
    },
    'data': {
        'bits': 32,
        'default': 0,
        'format': 'hex'
    },
    'cmd': {
        'bits': 2,
        'default': 0,
        'format': 'dec'
    }
}
```

## Best Practices

1. Use the newer `FieldConfig` class for more robust field configuration
2. Ensure field configurations match between protocols when using transformers
3. For memory verification, use the `GAXItoMemoryAdapter` to connect to a memory model
4. Always check both the result (pass rate) and detailed report for verification
5. Clear scoreboards between test phases
6. Use appropriate field mapping when different field names are used between protocols

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
