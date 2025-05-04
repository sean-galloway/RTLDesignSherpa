# APB Sequence

## Overview

The `APBSequence` class provides a flexible mechanism for generating structured test patterns for APB (Advanced Peripheral Bus) protocol verification. It supports various testing patterns with configurable parameters, making it easy to create targeted test sequences for APB interfaces.

## Features

- Dataclass-based configuration for test sequence generation
- Support for multiple test patterns: alternating, burst, strobes, etc.
- Configurable iteration with predictable or random selection
- Direct generation of ready-to-use APB packets
- Built-in inter-cycle delays for timing control
- Integration with `FlexRandomizer` for advanced randomization

## Classes

### APBSequence

A dataclass that generates test patterns with direct packet creation.

#### Constructor

```python
@dataclass
class APBSequence:
    # Test name
    name: str = "basic"

    # Transaction sequence - list of writes (True) and reads (False)
    pwrite_seq: List[bool] = field(default_factory=list)

    # Address sequence
    addr_seq: List[int] = field(default_factory=list)

    # Data sequence for writes
    data_seq: List[int] = field(default_factory=list)

    # Strobe sequence for writes
    strb_seq: List[int] = field(default_factory=list)

    # Protection attributes sequence
    pprot_seq: List[int] = field(default_factory=list)

    # Timing
    inter_cycle_delays: List[int] = field(default_factory=list)

    # Randomizers
    master_randomizer: Optional[Dict] = None
    slave_randomizer: Optional[Tuple] = None
    other_randomizer: Optional[Tuple] = None

    # Selection mode
    use_random_selection: bool = False

    # Verification
    verify_data: bool = True

    # Data width
    data_width: int = 32

    # Transaction count
    transaction_count: int = 0
```

#### Key Methods

- `reset_iterators()`: Reset all iterators to the beginning
- `next_pwrite()`: Get next write/read operation
- `next_addr()`: Get next address value
- `next_data()`: Get next data value
- `next_strb()`: Get next strobe mask
- `next_pprot()`: Get next protection attribute
- `next_delay()`: Get next inter-cycle delay
- `next()`: Generate the next complete APB packet
- `has_more_transactions()`: Check if more transactions are available

## Test Patterns

The APB sequence can be configured to generate different test patterns:

### Alternating Pattern

Alternating writes and reads to the same address:

```
Write → Read → Write → Read → ...
```

This pattern is useful for basic register access testing.

### Burst Pattern

A sequence of all writes followed by all reads:

```
Write → Write → Write → ... → Read → Read → Read → ...
```

This pattern is good for testing back-to-back operations.

### Strobe Pattern

Tests different write strobe combinations:

```
Write (all strobes) → Read → Write (byte 0) → Read → Write (byte 1) → Read → ...
```

This pattern verifies partial write operations.

### Stress Pattern

Random mix of reads and writes with various patterns:

```
Write → Write → Read → Write → Read → Read → ...
```

This pattern tests robustness of the APB interface.

## Example Usage

### Creating a Basic Sequence

```python
# Create an alternating read/write sequence
sequence = APBSequence(
    name="basic_test",
    pwrite_seq=[True, False, True, False],  # W-R-W-R
    addr_seq=[0x1000, 0x1004, 0x1008],
    data_seq=[0xABCD1234, 0x5678ABCD],
    strb_seq=[0xF],  # All strobes enabled
    inter_cycle_delays=[2, 3, 1, 2]  # Delays between transactions
)

# Get the next packet
packet = sequence.next()
```

### Using with APB Master

```python
# Create sequence
sequence = APBSequence(
    name="register_test",
    pwrite_seq=[True, False] * 10,  # 10 W-R pairs
    addr_seq=[0x1000 + i*4 for i in range(10)],
    data_seq=[0xA0000000 + i for i in range(10)],
    strb_seq=[0xF],
    inter_cycle_delays=[5] * 20
)

# Send all transactions
while sequence.has_more_transactions():
    packet = sequence.next()
    await apb_master.send(packet)
    await cocotb.triggers.Timer(sequence.next_delay(), units="ns")
```

### Creating a Random Sequence

```python
# Create a sequence with random selection
sequence = APBSequence(
    name="random_test",
    pwrite_seq=[True, False],  # Will be randomly selected
    addr_seq=[0x1000, 0x1004, 0x1008, 0x100C],
    data_seq=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    strb_seq=[0xF, 0x3, 0x5, 0xA],
    use_random_selection=True  # Enable random selection
)

# Generate 20 random transactions
for _ in range(20):
    packet = sequence.next()
    print(packet.formatted(compact=True))
```

## Implementation Details

### Sequence Iteration

The class implements iterators for each sequence type (pwrite, addr, data, etc.) with two modes:

1. **Sequential**: Cycles through the sequence list in order, wrapping around when reaching the end
2. **Random**: Randomly selects items from the sequence list using Python's `random.choice()`

### Post Initialization

The `__post_init__()` method initializes iterators for all sequences and sets default values:

```python
def __post_init__(self):
    self.pwrite_iter = iter(self.pwrite_seq)
    self.addr_iter = iter(self.addr_seq)
    self.data_iter = iter(self.data_seq)
    self.strb_iter = iter(self.strb_seq)
    self.delay_iter = iter(self.inter_cycle_delays)

    # Default protection values if none provided
    if not self.pprot_seq:
        self.pprot_seq = [0]
    self.pprot_iter = iter(self.pprot_seq)
```

## Notes

- When `use_random_selection=True`, the `next()` method will randomly choose values from each sequence
- If a sequence is shorter than the number of transactions, it will wrap around automatically
- The `transaction_count` is incremented each time `next()` is called
- The `has_more_transactions()` method returns True indefinitely when `use_random_selection` is enabled

## See Also

- [APB Packet](apb_packet.md) - The packet class generated by this sequence
- [APB Components](apb_components.md) - APB master, slave, and monitor implementation
- [APB Factories](apb_factories.md) - Factory functions that create sequences
- [Flex Randomizer](../flex_randomizer.md) - Used for timing randomization

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
