# FIFO Scoreboard Documentation

## Overview

The FIFO Scoreboard module provides components for verifying FIFO (First-In, First-Out) transactions in digital designs. It includes:

1. `FIFOScoreboard`: Core verification component for FIFO transactions
2. `MemoryAdapter`: Interface between FIFO packets and memory models

These components allow verification engineers to track and compare FIFO transactions, ensuring that data flows correctly through FIFO interfaces.

## FIFOScoreboard Class

### Purpose

The `FIFOScoreboard` extends the basic `BaseScoreboard` to provide FIFO-specific transaction verification capabilities.

### Class Definition

```python
class FIFOScoreboard(BaseScoreboard):
    """Scoreboard for FIFO transactions"""

    def __init__(self, name, field_config, log=None):
        super().__init__(name, log)
        self.field_config = field_config
```

### Key Features

#### Transaction Comparison

```python
def _compare_transactions(self, expected, actual):
    """Compare FIFO packets"""
```
Verifies that both transactions are valid `FIFOPacket` objects and compares them using their built-in equality method.

#### Enhanced Mismatch Logging

```python
def _log_mismatch(self, expected, actual):
    """Enhanced mismatch logging for FIFO packets"""
```
Provides detailed field-by-field comparison when transactions don't match, making it easier to identify the source of verification failures.

## MemoryAdapter Class

### Purpose

The `MemoryAdapter` provides an interface between FIFO packets and memory models, allowing memory-based verification of FIFO transactions.

### Class Definition

```python
class MemoryAdapter:
    """
    Adapter for memory model integration with FIFO packets.
    Converts between FIFO packets and memory read/write operations.
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

Supports custom mapping between FIFO packet fields and memory operations:
```python
# Default field mapping if not provided
self.field_map = field_map or {
    'addr': 'addr',
    'data': 'data',
    'ctrl': 'ctrl'
}
```

#### Memory Write Operations

```python
def write_to_memory(self, packet):
    """
    Write packet data to memory model.

    Args:
        packet: FIFO packet with write data

    Returns:
        True if successful, False otherwise
    """
```
Extracts address, data, and control information from a FIFO packet and writes it to the memory model.

#### Memory Read Operations

```python
def read_from_memory(self, packet):
    """
    Read data from memory model based on packet address.

    Args:
        packet: FIFO packet with address to read from

    Returns:
        Data value read from memory, or None if error
    """
```
Reads data from the memory model based on the address in a FIFO packet and returns the data value.

## FIFO Packet Structure

FIFO packets typically include the following components:
- `addr`: Address for memory operations
- `data`: Data payload
- `ctrl`: Control information or mask for the operation

The exact structure is defined by the `field_config` provided during initialization.

## Usage Examples

### Basic FIFO Verification

```python
# Create field configuration
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
    'ctrl': {
        'bits': 4,
        'default': 0,
        'format': 'bin'
    }
}

# Create FIFO scoreboard
fifo_sb = FIFOScoreboard("FIFO_SB", field_config, log=logger)

# Add expected transaction
expected_tx = FIFOPacket(field_config, addr=0x1000, data=0xABCD, ctrl=0xF)
fifo_sb.add_expected(expected_tx)

# Add actual transaction (triggers comparison)
actual_tx = FIFOPacket(field_config, addr=0x1000, data=0xABCD, ctrl=0xF)
fifo_sb.add_actual(actual_tx)

# Get results
result = fifo_sb.result()  # 1.0 for perfect match
print(fifo_sb.report())    # Detailed report
```

### Memory-Based Verification

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Create memory adapter
adapter = MemoryAdapter(mem_model, log=logger)

# Create field configuration
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
    'ctrl': {
        'bits': 4,
        'default': 0,
        'format': 'bin'
    }
}

# Create FIFO scoreboard
fifo_sb = FIFOScoreboard("FIFO_SB", field_config, log=logger)

# Create write packet
write_packet = FIFOPacket(field_config, addr=0x1000, data=0xABCD, ctrl=0xF)

# Write to memory
adapter.write_to_memory(write_packet)

# Create read packet
read_packet = FIFOPacket(field_config, addr=0x1000)

# Read from memory
read_data = adapter.read_from_memory(read_packet)

# Check if read data matches expected
assert read_data == 0xABCD, f"Read data mismatch: expected 0xABCD, got 0x{read_data:X}"
```

### Verification with Multiple FIFO Interfaces

```python
# Create field configuration
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
    'ctrl': {
        'bits': 4,
        'default': 0,
        'format': 'bin'
    }
}

# Create scoreboards for input and output FIFOs
input_fifo_sb = FIFOScoreboard("Input_FIFO_SB", field_config, log=logger)
output_fifo_sb = FIFOScoreboard("Output_FIFO_SB", field_config, log=logger)

# Add expected transactions to both scoreboards
tx1 = FIFOPacket(field_config, addr=0x1000, data=0xABCD, ctrl=0xF)
tx2 = FIFOPacket(field_config, addr=0x1004, data=0x1234, ctrl=0xF)

input_fifo_sb.add_expected(tx1)
input_fifo_sb.add_expected(tx2)
output_fifo_sb.add_expected(tx1)
output_fifo_sb.add_expected(tx2)

# Add actual transactions as they occur
# ... (during simulation)

# Check results for both scoreboards
input_result = input_fifo_sb.result()
output_result = output_fifo_sb.result()

print(f"Input FIFO: {input_result}")
print(f"Output FIFO: {output_result}")
```

## Integration with Other Components

The FIFO Scoreboard can be integrated with other verification components:

### With Protocol Transformers

```python
# Create transformer between FIFO and target protocol
transformer = FIFOtoTargetTransformer(fifo_config, target_config)

# Create target scoreboard
target_sb = TargetScoreboard("Target_SB", target_config)

# Set transformer on FIFO scoreboard
fifo_sb = FIFOScoreboard("FIFO_SB", fifo_config)
fifo_sb.set_transformer(transformer)

# Add expected FIFO transaction (will be transformed)
fifo_tx = FIFOPacket(fifo_config, addr=0x1000, data=0xABCD, ctrl=0xF)
fifo_sb.add_expected(fifo_tx)

# Add actual target transaction
target_tx = TargetPacket(target_config, addr=0x1000, data=0xABCD)
fifo_sb.add_actual(target_tx)
```

### With Memory Models

```python
# Create memory model
mem_model = MemoryModel(num_lines=1024, bytes_per_line=4, log=logger)

# Create memory adapter
adapter = MemoryAdapter(mem_model, log=logger)

# Verify FIFO transactions against memory model
for packet in fifo_transactions:
    # For write transactions
    if is_write_transaction(packet):
        adapter.write_to_memory(packet)
    
    # For read transactions
    else:
        expected_data = adapter.read_from_memory(packet)
        actual_data = packet.data
        
        if expected_data != actual_data:
            print(f"ERROR: Read data mismatch at 0x{packet.addr:X}")
            print(f"  Expected: 0x{expected_data:X}")
            print(f"  Actual: 0x{actual_data:X}")
```

## Best Practices

1. Define a clear field configuration for your FIFO packets
2. Use the memory adapter when verifying against a reference memory model
3. Check the result and report for detailed statistics on verification
4. For complex designs, consider using separate scoreboards for different FIFO interfaces
5. Clear the scoreboard between test phases with `clear()`
6. For cross-protocol verification, use transformers to convert between protocols
7. Ensure field mappings match your specific FIFO implementation

## Navigation

[↑ Scoreboards Index](index.md) | [↑ CocoTBFramework Index](../index.md)
