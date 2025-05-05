# GAXI Buffer Sequence

## Overview

The `GAXIBufferSequence` class provides a comprehensive test sequence generator for GAXI buffer testing. It extends the base `GAXISequence` class with specialized patterns and sequences for testing complex buffer components with multiple fields (addr, ctrl, data0, data1). The class supports various test patterns including incrementing values, walking ones, alternating bits, boundary values, and random data, making it a powerful tool for thorough verification.

## Class Definition

```python
class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests with multi-field support.

    This class expands on the base GAXISequence to add specific patterns and
    sequences suitable for testing GAXI buffer components with multiple fields
    (addr, ctrl, data0, data1).
    """

    def __init__(self, name, field_config, packet_class=GAXIPacket):
        """
        Initialize the GAXI buffer sequence.

        Args:
            name: Sequence name
            field_config: Field configuration for multi-field packets
            packet_class: Class to use for packet creation
        """
        super().__init__(name, field_config, packet_class)

        # Extract field widths from the field_config
        if isinstance(field_config, FieldConfig):
            # Get field widths from FieldConfig object
            self.addr_width = field_config.get_field('addr').bits
            self.ctrl_width = field_config.get_field('ctrl').bits
            self.data0_width = field_config.get_field('data0').bits
            self.data1_width = field_config.get_field('data1').bits
        else:
            # Get field widths from dictionary
            self.addr_width = field_config['addr']['bits']
            self.ctrl_width = field_config['ctrl']['bits']
            self.data0_width = field_config['data0']['bits']
            self.data1_width = field_config['data1']['bits']
```

## Key Features

- Support for multi-field GAXI packet structures
- Comprehensive test pattern generation
- Parameterized field widths
- Method chaining for sequence construction
- Timing control via delay parameters
- Field-specific pattern generation
- Support for various test strategies (walking ones, boundary values, etc.)
- Randomizer integration for timing control

## Primary Methods

### add_multi_field_transaction

Adds a transaction with values for all fields.

```python
def add_multi_field_transaction(self, addr=0, ctrl=0, data0=0, data1=0, delay=0):
    """
    Add a transaction with values for all fields.

    Args:
        addr: Address value
        ctrl: Control value
        data0: Data0 value
        data1: Data1 value
        delay: Delay after transaction

    Returns:
        Self for method chaining
    """
    field_values = {
        'addr': addr,
        'ctrl': ctrl,
        'data0': data0,
        'data1': data1
    }
    return self.add_transaction(field_values, delay)
```

### add_incrementing_pattern

Adds transactions with incrementing values for all fields.

```python
def add_incrementing_pattern(self, count, start_value=0, addr_step=1, ctrl_step=1,
                            data0_step=1, data1_step=1, delay=0):
    """
    Add transactions with incrementing values for all fields.

    Args:
        count: Number of transactions to generate
        start_value: Base starting value for all fields
        addr_step: Increment step for address field
        ctrl_step: Increment step for control field
        data0_step: Increment step for data0 field
        data1_step: Increment step for data1 field
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    for i in range(count):
        addr = start_value + (i * addr_step)
        ctrl = start_value + (i * ctrl_step)
        data0 = start_value + (i * data0_step)
        data1 = start_value + (i * data1_step)

        self.add_multi_field_transaction(
            addr=addr,
            ctrl=ctrl,
            data0=data0,
            data1=data1,
            delay=delay
        )

    return self
```

### add_walking_ones_pattern

Adds transactions with walking ones pattern across all fields.

```python
def add_walking_ones_pattern(self, delay=0):
    """
    Add transactions with walking ones pattern across all fields.
    The pattern moves from LSB to MSB through each field in sequence.

    Args:
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Calculate total bits across all fields
    total_bits = self.addr_width + self.ctrl_width + self.data0_width + self.data1_width

    for bit_position in range(total_bits):
        # Determine which field this bit belongs to
        if bit_position < self.addr_width:
            # This bit is in the addr field
            addr = 1 << bit_position
            ctrl = 0
            data0 = 0
            data1 = 0
        elif bit_position < (self.addr_width + self.ctrl_width):
            # This bit is in the ctrl field
            addr = 0
            ctrl = 1 << (bit_position - self.addr_width)
            data0 = 0
            data1 = 0
        elif bit_position < (self.addr_width + self.ctrl_width + self.data0_width):
            # This bit is in the data0 field
            addr = 0
            ctrl = 0
            data0 = 1 << (bit_position - self.addr_width - self.ctrl_width)
            data1 = 0
        else:
            # This bit is in the data1 field
            addr = 0
            ctrl = 0
            data0 = 0
            data1 = 1 << (bit_position - self.addr_width - self.ctrl_width - self.data0_width)

        self.add_multi_field_transaction(
            addr=addr,
            ctrl=ctrl,
            data0=data0,
            data1=data1,
            delay=delay
        )

    return self
```

### add_field_test_pattern

Adds test patterns that exercise all fields individually and together.

```python
def add_field_test_pattern(self, delay=0):
    """
    Add test patterns that exercise all fields individually and together.

    Args:
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Create masks for each field
    addr_mask = (1 << self.addr_width) - 1
    ctrl_mask = (1 << self.ctrl_width) - 1
    data0_mask = (1 << self.data0_width) - 1
    data1_mask = (1 << self.data1_width) - 1

    # Test each field individually
    # Addr only
    self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=0, data1=0, delay=delay)

    # Ctrl only
    self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=0, data1=0, delay=delay)

    # Data0 only
    self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_mask, data1=0, delay=delay)

    # Data1 only
    self.add_multi_field_transaction(addr=0, ctrl=0, data0=0, data1=data1_mask, delay=delay)

    # Test pairs of fields
    # Addr + Ctrl
    self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=0, data1=0, delay=delay)

    # Addr + Data0
    self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=data0_mask, data1=0, delay=delay)

    # Addr + Data1
    self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=0, data1=data1_mask, delay=delay)

    # Ctrl + Data0
    self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=data0_mask, data1=0, delay=delay)

    # Ctrl + Data1
    self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=0, data1=data1_mask, delay=delay)

    # Data0 + Data1
    self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_mask, data1=data1_mask, delay=delay)

    # Test groups of three fields
    # Addr + Ctrl + Data0
    self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=data0_mask, data1=0, delay=delay)

    # Addr + Ctrl + Data1
    self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=0, data1=data1_mask, delay=delay)

    # Addr + Data0 + Data1
    self.add_multi_field_transaction(addr=addr_mask, ctrl=0, data0=data0_mask, data1=data1_mask, delay=delay)

    # Ctrl + Data0 + Data1
    self.add_multi_field_transaction(addr=0, ctrl=ctrl_mask, data0=data0_mask, data1=data1_mask, delay=delay)

    # Test all fields
    # Addr + Ctrl + Data0 + Data1
    self.add_multi_field_transaction(addr=addr_mask, ctrl=ctrl_mask, data0=data0_mask, data1=data1_mask, delay=delay)

    return self
```

### add_alternating_patterns

Adds transactions with alternating bit patterns across fields.

```python
def add_alternating_patterns(self, count, delay=0):
    """
    Add transactions with alternating bit patterns across fields.

    Args:
        count: Number of transactions to generate
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Create masks for each field
    addr_mask = (1 << self.addr_width) - 1
    ctrl_mask = (1 << self.ctrl_width) - 1
    data0_mask = (1 << self.data0_width) - 1
    data1_mask = (1 << self.data1_width) - 1

    # Patterns
    patterns = [
        # 0x55 = 01010101, 0xAA = 10101010
        {'addr': 0x55555555 & addr_mask, 'ctrl': 0x55 & ctrl_mask,
            'data0': 0x55555555 & data0_mask, 'data1': 0x55555555 & data1_mask},

        {'addr': 0xAAAAAAAA & addr_mask, 'ctrl': 0xAA & ctrl_mask,
            'data0': 0xAAAAAAAA & data0_mask, 'data1': 0xAAAAAAAA & data1_mask},

        # 0x33 = 00110011, 0xCC = 11001100
        {'addr': 0x33333333 & addr_mask, 'ctrl': 0x33 & ctrl_mask,
            'data0': 0x33333333 & data0_mask, 'data1': 0x33333333 & data1_mask},

        {'addr': 0xCCCCCCCC & addr_mask, 'ctrl': 0xCC & ctrl_mask,
            'data0': 0xCCCCCCCC & data0_mask, 'data1': 0xCCCCCCCC & data1_mask},

        # 0x0F = 00001111, 0xF0 = 11110000
        {'addr': 0x0F0F0F0F & addr_mask, 'ctrl': 0x0F & ctrl_mask,
            'data0': 0x0F0F0F0F & data0_mask, 'data1': 0x0F0F0F0F & data1_mask},

        {'addr': 0xF0F0F0F0 & addr_mask, 'ctrl': 0xF0 & ctrl_mask,
            'data0': 0xF0F0F0F0 & data0_mask, 'data1': 0xF0F0F0F0 & data1_mask},
    ]

    # Add transactions with these patterns
    for _, pattern in itertools.product(range(count), patterns):
        self.add_multi_field_transaction(
            addr=pattern['addr'],
            ctrl=pattern['ctrl'],
            data0=pattern['data0'],
            data1=pattern['data1'],
            delay=delay
        )

    return self
```

### add_random_data_pattern

Adds transactions with random data in all fields.

```python
def add_random_data_pattern(self, count, delay=0):
    """
    Add transactions with random data in all fields.

    Args:
        count: Number of transactions to generate
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Create masks for each field
    addr_mask = (1 << self.addr_width) - 1
    ctrl_mask = (1 << self.ctrl_width) - 1
    data0_mask = (1 << self.data0_width) - 1
    data1_mask = (1 << self.data1_width) - 1

    # Add random transactions
    for _ in range(count):
        addr = random.randint(0, 0xFFFFFFFF) & addr_mask
        ctrl = random.randint(0, 0xFF) & ctrl_mask
        data0 = random.randint(0, 0xFFFFFFFF) & data0_mask
        data1 = random.randint(0, 0xFFFFFFFF) & data1_mask

        self.add_multi_field_transaction(
            addr=addr,
            ctrl=ctrl,
            data0=data0,
            data1=data1,
            delay=delay
        )

    return self
```

### add_boundary_values

Adds transactions with boundary values for all fields.

```python
def add_boundary_values(self, delay=0):
    """
    Add transactions with boundary values for all fields.

    Args:
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Create masks for each field
    addr_mask = (1 << self.addr_width) - 1
    ctrl_mask = (1 << self.ctrl_width) - 1
    data0_mask = (1 << self.data0_width) - 1
    data1_mask = (1 << self.data1_width) - 1

    # Boundary test cases
    test_cases = [
        # All zeros
        {'addr': 0, 'ctrl': 0, 'data0': 0, 'data1': 0},

        # All ones
        {'addr': addr_mask, 'ctrl': ctrl_mask, 'data0': data0_mask, 'data1': data1_mask},

        # LSB only
        {'addr': 1, 'ctrl': 1, 'data0': 1, 'data1': 1},

        # MSB only
        {'addr': 1 << (self.addr_width - 1), 'ctrl': 1 << (self.ctrl_width - 1),
            'data0': 1 << (self.data0_width - 1), 'data1': 1 << (self.data1_width - 1)},

        # All except LSB
        {'addr': addr_mask & ~1, 'ctrl': ctrl_mask & ~1,
            'data0': data0_mask & ~1, 'data1': data1_mask & ~1},

        # All except MSB
        {'addr': addr_mask & ~(1 << (self.addr_width - 1)),
            'ctrl': ctrl_mask & ~(1 << (self.ctrl_width - 1)),
            'data0': data0_mask & ~(1 << (self.data0_width - 1)),
            'data1': data1_mask & ~(1 << (self.data1_width - 1))},
    ]

    # Add transactions with boundary values
    for test_case in test_cases:
        self.add_multi_field_transaction(
            addr=test_case['addr'],
            ctrl=test_case['ctrl'],
            data0=test_case['data0'],
            data1=test_case['data1'],
            delay=delay
        )

    return self
```

### add_overflow_test

Adds transactions with values that exceed field widths to test masking.

```python
def add_overflow_test(self, delay=0):
    """
    Add transactions with values that exceed field widths to test masking.

    Args:
        delay: Delay between transactions

    Returns:
        Self for method chaining
    """
    # Create masks and overflow values for each field
    addr_mask = (1 << self.addr_width) - 1
    addr_overflow = addr_mask + random.randint(1, 100)

    ctrl_mask = (1 << self.ctrl_width) - 1
    ctrl_overflow = ctrl_mask + random.randint(1, 20)

    data0_mask = (1 << self.data0_width) - 1
    data0_overflow = data0_mask + random.randint(1, 100)

    data1_mask = (1 << self.data1_width) - 1
    data1_overflow = data1_mask + random.randint(1, 100)

    # Add transactions with overflow values
    # Test each field individually
    self.add_multi_field_transaction(addr=addr_overflow, ctrl=0, data0=0, data1=0, delay=delay)
    self.add_multi_field_transaction(addr=0, ctrl=ctrl_overflow, data0=0, data1=0, delay=delay)
    self.add_multi_field_transaction(addr=0, ctrl=0, data0=data0_overflow, data1=0, delay=delay)
    self.add_multi_field_transaction(addr=0, ctrl=0, data0=0, data1=data1_overflow, delay=delay)

    # Test all fields with overflow
    self.add_multi_field_transaction(
        addr=addr_overflow,
        ctrl=ctrl_overflow,
        data0=data0_overflow,
        data1=data1_overflow,
        delay=delay
    )

    return self
```

## Randomizer Support

The sequence class includes support for setting custom randomizers:

```python
# Set master randomizer
def set_master_randomizer(self, randomizer):
    """Set custom randomizer for master"""
    self.master_randomizer = randomizer
    return self

# Set slave randomizer
def set_slave_randomizer(self, randomizer):
    """Set custom randomizer for slave"""
    self.slave_randomizer = randomizer
    return self
```

## Pattern Generation Details

### Walking Ones Pattern

The walking ones pattern exercises each bit position in each field, setting one bit at a time to 1. This helps identify issues with individual bit positions.

- Sequences through each bit of each field
- Addresses a single bit at a time
- Covers all bits across all fields sequentially

### Alternating Patterns

The alternating patterns use common bit patterns to test bit adjacency issues.

- 0x55 / 0xAA - Alternating 01/10 patterns (test adjacent bits)
- 0x33 / 0xCC - Alternating 0011/1100 patterns (test 2-bit groups)
- 0x0F / 0xF0 - Alternating 0000 1111/1111 0000 patterns (test 4-bit groups)

### Field Test Pattern

The field test pattern systematically tests field interactions.

1. Individual fields (addr, ctrl, data0, data1)
2. Pairs of fields (addr+ctrl, addr+data0, etc.)
3. Triplets of fields (addr+ctrl+data0, etc.)
4. All fields together

### Boundary Values

The boundary values test special cases:

- All zeros
- All ones
- LSB only
- MSB only
- All except LSB
- All except MSB

### Overflow Test

The overflow test verifies proper field width masking by:

- Setting individual fields beyond their max values
- Setting all fields beyond their max values simultaneously

## Example Usage

Basic usage of the GAXI buffer sequence in a testbench:

```python
# Create a sequence
sequence = GAXIBufferSequence("comprehensive_test", field_config)

# Add various test patterns
sequence.add_incrementing_pattern(count=10, delay=1)
sequence.add_walking_ones_pattern(delay=1)
sequence.add_field_test_pattern(delay=1)
sequence.add_alternating_patterns(count=1, delay=1)
sequence.add_boundary_values(delay=2)
sequence.add_random_data_pattern(count=10, delay=1)

# Set custom randomizers (optional)
sequence.set_master_randomizer(FlexRandomizer({
    'valid_delay': ([[0, 0]], [1])  # No delay
}))

# Generate packets from the sequence
packets = sequence.generate_packets()
```

Creating a burst test sequence:

```python
# Create burst test sequence
burst_sequence = GAXIBufferSequence("burst_test", field_config)
burst_sequence.add_incrementing_pattern(30, delay=0)

# Set fast randomizers for back-to-back transfers
burst_sequence.set_master_randomizer(FlexRandomizer({
    'valid_delay': ([[0, 0]], [1])  # No delay
}))
burst_sequence.set_slave_randomizer(FlexRandomizer({
    'ready_delay': ([[0, 0]], [1])  # No delay
}))

# Generate packets
packets = burst_sequence.generate_packets()
```

Creating a custom sequence with specialized patterns:

```python
# Create custom sequence
custom_sequence = GAXIBufferSequence("custom_test", field_config)

# Add specific test patterns
for i in range(1, 6):
    addr = i * 100
    ctrl = i * 10
    data0 = i * 1000
    data1 = i * 10000
    custom_sequence.add_multi_field_transaction(addr, ctrl, data0, data1, delay=i)

# Add walking ones pattern
custom_sequence.add_walking_ones_pattern(delay=0)

# Add some special test cases
custom_sequence.add_boundary_values(delay=2)
custom_sequence.add_overflow_test(delay=3)

# Generate packets
packets = custom_sequence.generate_packets()
```

## Implementation Notes

- The sequence class builds on the base GAXISequence class
- Method chaining allows for fluent sequence construction
- Each pattern generator targets specific verification aspects
- Field widths are automatically extracted from the field configuration
- Mask values are calculated based on field widths
- Delay parameters allow for timing control
- Custom randomizers can be attached to sequences

## Key Verification Strategies

The sequence generator implements several verification strategies:

1. **Individual Bit Testing**: Walking ones pattern exercises each bit in isolation.

2. **Field Interaction Testing**: Field test patterns exercise field dependencies.

3. **Bit Pattern Testing**: Alternating patterns test bit pattern sensitivities.

4. **Boundary Condition Testing**: Boundary values test special corner cases.

5. **Overflow Testing**: Overflow tests verify proper field width handling.

6. **Randomized Testing**: Random patterns provide coverage for unexpected cases.

7. **Timing Variations**: Delay parameters allow for timing stress testing.

8. **Burst Testing**: Back-to-back transactions test buffer capacity and flow control.

## Best Practices

When using the GAXIBufferSequence class:

1. **Combine Pattern Types**: Use multiple pattern types for comprehensive testing.

2. **Vary Delays**: Use different delay values to test timing sensitivities.

3. **Add Custom Patterns**: Extend with custom patterns for specific tests.

4. **Use Method Chaining**: Chain method calls for concise sequence creation.

5. **Set Custom Randomizers**: Use custom randomizers for specific timing behavior.

6. **Test Boundary Cases**: Include boundary values and overflow tests.

7. **Document Sequences**: Name sequences descriptively for clear test reporting.

8. **Scale Test Depth**: Adjust pattern counts based on verification requirements.

## See Also

- [GAXI Buffer Field](gaxi_buffer_field.md) - Field-based GAXI testbench
- [GAXI Buffer Multi](gaxi_buffer_multi.md) - Multi-signal GAXI testbench
- [GAXI Packet](../../components/gaxi/gaxi_packet.md) - GAXI packet structure
- [GAXI Sequence](../../components/gaxi/gaxi_sequence.md) - Base sequence class

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)