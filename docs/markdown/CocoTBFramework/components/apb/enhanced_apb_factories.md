# Enhanced APB Factories

## Overview

The Enhanced APB Factories module extends the basic APB factory functions with advanced features for register testing and functional verification. It provides sophisticated test generation capabilities, register map integration, and test execution functions that streamline the verification process.

## Features

- All base APB factory functions from the standard module
- Advanced register test sequence generation
- Integration with register map definitions
- Field-level test generation and verification
- Support for read-modify-write operations
- Various test types: walking patterns, access checks, reset testing
- Specialized functional testing with register field tuples
- Register map manipulation and verification

## Factory Functions

### Standard APB Factory Functions

This module includes all the functions from the standard `apb_factories` module:

- `create_apb_master`
- `create_apb_slave`
- `create_apb_monitor`
- `create_apb_scoreboard`
- `create_apb_command_handler`
- `create_apb_components`
- `create_apb_transformer`
- `create_apb_packet`
- `create_apb_sequence`

See [APB Factories](apb_factories.md) for details on these functions.

### Enhanced Register Testing Functions

#### create_register_test_sequence

Creates a test sequence for register testing based on register map information.

```python
def create_register_test_sequence(reg_map, test_type="walk", options=None)
```

- `reg_map`: RegisterMap instance containing register definitions
- `test_type`: Type of test to generate:
  - "walk": Walking ones/zeros test
  - "field": Field-specific tests
  - "access": Access rights verification
  - "reset": Register reset value verification
  - "stress": Stress testing with rapid accesses
  - "random": Randomized register operations
- `options`: Dictionary of test-specific options

Returns:
- `APBSequence` configured for the requested test

#### create_sequence_from_tuples

Creates an APB sequence from a list of (register, field, value) tuples.

```python
def create_sequence_from_tuples(reg_map, reg_field_values, name="functional_test", options=None)
```

- `reg_map`: RegisterMap instance containing register definitions
- `reg_field_values`: List of (register, field, value) tuples
- `name`: Name for the sequence
- `options`: Dictionary of options (delay, verify, etc.)

Returns:
- `APBSequence` configured with the register/field operations

#### run_test_sequence

Runs a register test sequence through an APB master.

```python
async def run_test_sequence(apb_master, sequence, verify_func=None)
```

- `apb_master`: APB master driver
- `sequence`: Test sequence to run
- `verify_func`: Optional function to verify each transaction

Returns:
- List of transaction results

## Test Types

### Walk Test

The `_create_walk_test` function generates walking ones/zeros or alternating patterns:

- Tests each writable register with specific bit patterns
- Writes pattern to each register and reads back to verify
- Options:
  - `pattern`: "walking_ones", "walking_zeros", or "alternating"
  - `delay`: Clock cycles between transactions

### Field Test

The `_create_field_test` function tests specific fields within registers:

- Tests individual fields with various values
- Preserves other fields during write operations using read-modify-write
- Options:
  - `fields`: List of field names to test (default: all fields)
  - `values`: List of test values
  - `delay`: Clock cycles between transactions

### Access Test

The `_create_access_test` function verifies register access rights:

- Tests read and write access according to specifications
- Verifies special access types like W1C (write-1-to-clear)
- Options:
  - `delay`: Clock cycles between transactions

### Reset Test

The `_create_reset_test` function verifies registers return to default values after reset:

- Writes non-default values to registers
- Triggers a reset (via an external function)
- Verifies registers return to default values
- Options:
  - `delay`: Clock cycles between transactions
  - `reset_type`: Type of reset to perform ("hard", "soft")

### Stress Test

The `_create_stress_test` function generates rapid back-to-back accesses:

- Creates sequences with minimal delays
- Generates a mix of reads and writes
- Options:
  - `iterations`: Number of test iterations
  - `delay`: Clock cycles between transactions

### Random Test

The `_create_random_test` function generates randomized operations:

- Creates a mix of register reads, writes, and field operations
- Randomizes values, fields, and registers
- Options:
  - `iterations`: Number of test iterations
  - `seed`: Random seed for reproducibility
  - `delay_min`: Minimum delay between transactions
  - `delay_max`: Maximum delay between transactions

## Functional Testing

The `create_sequence_from_tuples` function supports flexible functional testing:

```python
# Define functional test operations
operations = [
    ("STATUS", "READY", 1),     # Set STATUS.READY bit
    ("CONTROL", "ENABLE", 1),   # Enable the module
    ("CONFIG", "MODE", 0x2),    # Set mode to 0x2
]

# Create the test sequence
sequence = create_sequence_from_tuples(
    reg_map,
    operations,
    name="device_init_sequence",
    options={
        "delay": 5,
        "verify": True  # Read back to verify
    }
)
```

## Example Usage

### Creating and Running a Register Walking Test

```python
# Create a walking ones test
walk_test = create_register_test_sequence(
    reg_map,
    test_type="walk",
    options={
        "pattern": "walking_ones",
        "delay": 2
    }
)

# Run the test
results = await run_test_sequence(apb_master, walk_test)

# Analyze results
for packet in results:
    print(f"Transaction {packet.count}: {packet.formatted(compact=True)}")
```

### Field-Level Testing

```python
# Create a field test for specific fields
field_test = create_register_test_sequence(
    reg_map,
    test_type="field",
    options={
        "fields": ["MODE", "ENABLE", "THRESHOLD"],
        "values": [0x0, 0x1, 0xF, 0xFF],
        "delay": 3
    }
)

# Run the test
await run_test_sequence(apb_master, field_test)
```

### Reset Testing

```python
# Create a reset test
reset_test = create_register_test_sequence(
    reg_map,
    test_type="reset",
    options={
        "reset_type": "hard",
        "delay": 5
    }
)

# Custom verification function with reset handling
async def verify_with_reset(packet, index):
    if index in reset_test.reset_points:
        # Perform reset when reaching a reset point
        await dut.reset.driver.value(1)
        await RisingEdge(dut.clk)
        await RisingEdge(dut.clk)
        await dut.reset.driver.value(0)

# Run the test with reset
await run_test_sequence(apb_master, reset_test, verify_with_reset)
```

### Functional Testing with Tuples

```python
# Define a register configuration sequence
config_sequence = [
    ("CONTROL", "RESET", 1),       # Reset the device
    ("CONTROL", "RESET", 0),       # Clear reset bit
    ("CONFIG", "CLOCK_DIV", 0x8),  # Set clock divider
    ("CONFIG", "PRESCALE", 0x2),   # Set prescaler
    ("INTERRUPT", "ENABLE", 0x1),  # Enable interrupts
    ("CONTROL", "ENABLE", 0x1)     # Enable the module
]

# Create and run the sequence
seq = create_sequence_from_tuples(reg_map, config_sequence)
await run_test_sequence(apb_master, seq)
```

## Implementation Details

### Register Map Integration

The enhanced factory functions integrate with a register map structure that provides:

- Register definitions with addresses and sizes
- Field definitions with bit positions and access rights
- Default values for reset testing
- Register arrays for multi-instance registers

Example register map structure:

```python
{
    "STATUS": {
        "address": "0x00",
        "size": 4,
        "sw": "r",  # Software access rights
        "default": "0x00000000",
        "READY": {
            "type": "field",
            "offset": "0",
            "sw": "r"
        },
        "BUSY": {
            "type": "field",
            "offset": "1",
            "sw": "r"
        }
    },
    "CONTROL": {
        "address": "0x04",
        "size": 4,
        "sw": "rw",
        "default": "0x00000000",
        # Fields...
    }
}
```

### Read-Modify-Write Operations

For field-level operations, the `create_sequence_from_tuples` function supports read-modify-write:

1. Read the current register value
2. Modify only the specified field bits
3. Write back the modified value

This is represented in the sequence with a tuple:

```python
# For read-modify-write:
sequence.data_seq.append((~field_mask & 0xFFFFFFFF, field_value))
```

The `run_test_sequence` function handles these tuples during execution.

## Notes

- The enhanced factories are designed to work with a RegisterMap class for structured register definitions
- Field operations use read-modify-write when possible to preserve other field values
- The `run_test_sequence` function handles special data formats like read-modify-write tuples
- Register sequences can have embedded control points like reset triggers

## See Also

- [APB Factories](apb_factories.md) - Base APB factory functions
- [APB Components](apb_components.md) - Core APB component implementations
- [APB Packet](apb_packet.md) - APB packet structure
- [APB Sequence](apb_sequence.md) - APB test sequence generation

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
