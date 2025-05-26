# APB Packet

## Overview

The `APBPacket` class provides a structured representation of APB (Advanced Peripheral Bus) protocol transactions. It extends the base `Packet` class with APB-specific fields and functionality, offering specialized methods for handling APB operations and formatting.

## Features

- Field-based representation of APB transactions
- Support for read and write operations
- Automatic direction determination based on PWRITE value
- Rich formatting capabilities for debugging
- Equality comparison with protocol-specific logic
- Integration with constrained random verification

## Classes

### APBPacket

The main packet class for APB transactions, extending the base `Packet` class.

#### Constructor

```python
def __init__(self, field_config=None, skip_compare_fields=None,
             data_width=32, addr_width=32, strb_width=4, **kwargs)
```

- `field_config`: Field configuration (uses default APB fields if None)
- `skip_compare_fields`: Fields to exclude from comparison operations
- `data_width`: Width of data fields (PWDATA, PRDATA) in bits
- `addr_width`: Width of address field (PADDR) in bits
- `strb_width`: Width of write strobe field (PSTRB) in bits
- `**kwargs`: Initial values for fields (e.g., `paddr=0x123`, `pwrite=1`)

#### Key Methods

- `__str__()`: Detailed string representation with all fields
- `formatted(compact=False)`: Formatted string representation
- `__eq__(other)`: Protocol-specific comparison logic
- `_format_field(field_name, value)`: Format a field according to its configuration

#### Key Attributes

- `fields`: Dictionary of field values
- `direction`: String representation of direction ('READ' or 'WRITE')
- `start_time`: Transaction start time (ns)
- `end_time`: Transaction end time (ns)
- `count`: Transaction count for tracing

### APBTransaction

A class for generating randomized APB transactions with constraints.

#### Constructor

```python
def __init__(self, data_width=32, addr_width=32, strb_width=4, constraints=None, **kwargs)
```

- `data_width`: Width of data fields in bits
- `addr_width`: Width of address field in bits
- `strb_width`: Width of write strobe field in bits
- `constraints`: Optional constraints for randomization
- `**kwargs`: Initial values for fields

#### Key Methods

- `next()`: Generate next randomized transaction
- `set_constrained_random()`: Set fields using constrained randomization
- `__str__()`: String representation using packet's formatting
- `formatted(compact=False)`: Formatted representation

## Example Usage

### Basic Transaction Creation

```python
# Create a simple APB write transaction
packet = APBPacket(
    pwrite=1,  # Write operation
    paddr=0x1000,  # Address
    pwdata=0xABCD1234,  # Write data
    pstrb=0xF  # All byte enables active
)

# Access field values
print(f"Operation: {packet.direction}")
print(f"Address: 0x{packet.fields['paddr']:X}")
print(f"Write Data: 0x{packet.fields['pwdata']:X}")

# Create a read transaction
read_packet = APBPacket(
    pwrite=0,  # Read operation
    paddr=0x1000  # Address
)
```

### Using Randomization

```python
# Create a transaction generator with constraints
trans_gen = APBTransaction(
    constraints={
        'pwrite': ([(0, 0), (1, 1)], [1, 3]),  # 25% reads, 75% writes
        'paddr': ([(0, 0xFFF), (0x1000, 0x1FFF)], [1, 2])  # Address ranges
    }
)

# Generate 10 random transactions
for _ in range(10):
    packet = trans_gen.next()
    print(packet.formatted(compact=True))
```

### Comparing Transactions

```python
# Create two packets
packet1 = APBPacket(pwrite=1, paddr=0x1000, pwdata=0x12345678)
packet2 = APBPacket(pwrite=1, paddr=0x1000, pwdata=0x12345678)

# Compare them
if packet1 == packet2:
    print("Packets are equal")
else:
    print("Packets differ")
```

## Implementation Details

### Field Configuration

The `APBPacket` class creates a default field configuration with the following fields:

- `pwrite`: Direction (0=Read, 1=Write)
- `paddr`: Address
- `pwdata`: Write data
- `prdata`: Read data
- `pstrb`: Write strobes
- `pprot`: Protection control
- `pslverr`: Slave error

### Direction Mapping

The class maintains a mapping from the `pwrite` value to a human-readable direction:

```python
PWRITE_MAP = ['READ', 'WRITE']
```

### Randomization

The `APBTransaction` class uses two complementary randomization approaches:

1. Cocotb's `Randomized` class for constrained random verification
2. The framework's `FlexRandomizer` for more fine-grained control

## Notes

- The `APBPacket` class is designed to work with the `APBMaster`, `APBSlave`, and `APBMonitor` components
- For equality comparison, it only examines the relevant data field based on direction
- The class provides backward compatibility through the `cycle` attribute
- Field values are automatically masked to prevent overflow

## See Also

- [Packet](../packet.md) - Base packet class that APBPacket extends
- [APB Components](apb_components.md) - APB master, slave, and monitor implementation
- [APB Sequence](apb_sequence.md) - Generation of APB test sequences
- [Field Config](../field_config.md) - Configuration of packet fields

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
