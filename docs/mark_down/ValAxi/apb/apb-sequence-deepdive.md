# APB Sequence Deep Dive

This document examines the `APBSequence` class from `apb_sequence.py`, which provides functionality for creating and managing sequences of APB transactions for testing.

## Overview

The APB Sequence implementation enables the creation of complex test scenarios by managing series of APB transactions. It's designed with several key features:

1. **Sequence Management**: Controls series of read/write operations
2. **Address Patterns**: Manages address sequences (sequential, random, custom)
3. **Data Generation**: Provides data patterns for write operations
4. **Timing Control**: Manages delays between transactions
5. **Randomization Support**: Enables both deterministic and random testing

## Design Architecture

The `APBSequence` class is implemented as a dataclass, which provides automatic initialization of attributes, string representation, and comparison methods:

```python
@dataclass
class APBSequence:
    """Configuration for test patterns with direct packet generation"""
    # Test name
    name: str = "basic"

    # Transaction sequence - list of writes (True) and reads (False)
    # Examples: [True, False] for alternating write-read
    #           [True, True, ..., False, False] for all writes then all reads
    pwrite_seq: List[bool] = field(default_factory=list)

    # Address sequence - list of addresses to use
    # If shorter than pwrite_seq, will cycle through the addresses
    addr_seq: List[int] = field(default_factory=list)

    # Data sequence - list of data values to use for writes
    # If shorter than number of writes, will cycle through the data values
    data_seq: List[int] = field(default_factory=list)

    # Strobe sequence - list of strobe masks to use for writes
    # If shorter than number of writes, will cycle through the strobe masks
    strb_seq: List[int] = field(default_factory=list)

    # Protection attributes sequence
    pprot_seq: List[int] = field(default_factory=list)

    # Timing
    inter_cycle_delays: List[int] = field(default_factory=list)  # Delays between cycles

    # Master timing randomizer
    master_randomizer: Optional[Dict] = None
    slave_randomizer: Optional[Tuple] = None
    other_randomizer: Optional[Tuple] = None

    # Selection mode
    use_random_selection: bool = False  # If True, randomly select from sequences

    # Verification
    verify_data: bool = True

    # Data width for sizing operations
    data_width: int = 32

    # Current transaction count
    transaction_count: int = 0
```

The dataclass provides a clean, structured way to define the test configuration.

## Initialization and Reset

After initialization, the class sets up iterators for all the sequence attributes:

```python
def __post_init__(self):
    """Initialize iterators for sequences and defaults"""
    self.pwrite_iter = iter(self.pwrite_seq)
    self.addr_iter = iter(self.addr_seq)
    self.data_iter = iter(self.data_seq)
    self.strb_iter = iter(self.strb_seq)
    self.delay_iter = iter(self.inter_cycle_delays)

    # Default protection values if none provided
    if not self.pprot_seq:
        self.pprot_seq = [0]  # Default protection value
    self.pprot_iter = iter(self.pprot_seq)
    
def reset_iterators(self):
    """Reset all iterators to the beginning"""
    self.pwrite_iter = iter(self.pwrite_seq)
    self.addr_iter = iter(self.addr_seq)
    self.data_iter = iter(self.data_seq)
    self.strb_iter = iter(self.strb_seq)
    self.delay_iter = iter(self.inter_cycle_delays)
    self.pprot_iter = iter(self.pprot_seq)
    self.transaction_count = 0
```

This allows test sequences to be reused by resetting the iterators to the beginning.

The use of Python's iterator protocol provides several advantages:
1. Encapsulates the iteration state
2. Handles sequence wrapping (restarting when exhausted)
3. Allows independent iteration of each sequence type
4. Supports reset operations for test reuse

## Sequence Generation

The class provides methods to get the next value from each sequence:

```python
def next_pwrite(self) -> bool:
    """Get next write/read operation"""
    if self.use_random_selection:
        return random.choice(self.pwrite_seq)
    try:
        return next(self.pwrite_iter)
    except StopIteration:
        self.pwrite_iter = iter(self.pwrite_seq)
        return next(self.pwrite_iter)

def next_addr(self) -> int:
    """Get next address"""
    if self.use_random_selection:
        return random.choice(self.addr_seq)
    try:
        return next(self.addr_iter)
    except StopIteration:
        self.addr_iter = iter(self.addr_seq)
        return next(self.addr_iter)

# Similar methods for data, strobe, protection, and delay
```

These methods:
1. Check if random selection is enabled
2. If random, return a random choice from the sequence
3. Otherwise, get the next value from the iterator
4. If the iterator is exhausted, reset it and get the first value again

This design supports both sequential and random testing patterns.

Each access method follows the same pattern, providing a consistent interface for all sequence types. The cycling behavior of sequences enables compact test definitions - for example, alternating between read and write operations with just `[True, False]` in the `pwrite_seq`.

## Complete Packet Generation

The `next()` method generates a complete APB packet:

```python
def next(self) -> APBPacket:
    """
    Generate the next complete APB packet

    Returns:
        APBPacket: Complete APB packet object ready for transmission
    """
    # Get next values from sequence
    pwrite = self.next_pwrite()
    paddr = self.next_addr()
    pprot = self.next_pprot()

    # Get strobes and data for writes
    if pwrite:
        pwdata = self.next_data()
        pstrb = self.next_strb()
    else:
        pwdata = 0  # Not used for reads
        pstrb = 0   # Not used for reads

    # Create APB packet
    packet = APBPacket(
        count=self.transaction_count,
        pwrite=1 if pwrite else 0,
        paddr=paddr,
        pwdata=pwdata,
        prdata=0,  # Will be filled by slave for reads
        pstrb=pstrb,
        pprot=pprot,
        pslverr=0   # Will be set by slave if error
    )

    # Increment transaction count
    self.transaction_count += 1

    return copy.copy(packet)

def has_more_transactions(self) -> bool:
    """
    Check if there are more transactions in the sequence

    Returns:
        bool: True if more transactions are available
    """
    # For unlimited sequences or random selections, always return True
    if self.use_random_selection:
        return True

    # For finite sequences, check if we've reached the end
    return self.transaction_count < len(self.pwrite_seq)

## Usage Patterns

The APBSequence class supports several common usage patterns:

### 1. Basic Alternating Read/Write

```python
# Create alternating read/write sequence
sequence = APBSequence(
    name="basic",
    pwrite_seq=[True, False, True, False],  # Write, Read, Write, Read
    addr_seq=[0x0, 0x0, 0x4, 0x4],          # Addresses
    data_seq=[0x12345678, 0x87654321],      # Write data
    strb_seq=[0xF, 0xF],                    # Byte enables (all bytes)
    inter_cycle_delays=[5, 5, 5]            # Delays between transactions
)
```

### 2. Burst Mode (All Writes Followed by All Reads)

```python
# Create burst sequence
sequence = APBSequence(
    name="burst",
    pwrite_seq=[True, True, True, False, False, False],  # All writes then all reads
    addr_seq=[0x0, 0x4, 0x8],                           # Three addresses
    data_seq=[0x11111111, 0x22222222, 0x33333333],      # Three data values
    strb_seq=[0xF],                                     # One strobe value (reused)
    inter_cycle_delays=[0]                              # No delays (fast burst)
)
```

### 3. Randomized Testing

```python
# Create randomized sequence
sequence = APBSequence(
    name="random",
    pwrite_seq=[True, False],           # Operation types to select from
    addr_seq=[0x0, 0x4, 0x8, 0xC],      # Addresses to select from
    data_seq=[0x11111111, 0x22222222],  # Data values to select from
    strb_seq=[0x1, 0x3, 0x7, 0xF],      # Strobe patterns to select from
    use_random_selection=True           # Enable random selection
)
```

### 4. Fixed Sequence with Random Delays

```python
# Create sequence with random delays
import random
sequence = APBSequence(
    name="random_delay",
    pwrite_seq=[True, False] * 10,              # 10 pairs of write/read
    addr_seq=[0x0, 0x4, 0x8, 0xC],              # Four addresses
    data_seq=[random.randint(0, 0xFFFFFFFF) for _ in range(10)],  # Random data
    inter_cycle_delays=[random.randint(0, 10) for _ in range(19)]  # Random delays
)
```

## Implementation Insights

The APBSequence implementation provides several key insights into effective sequence generation:

1. **Separation of Concerns**: Each attribute (pwrite, addr, data, etc.) is managed independently
2. **Cyclic Sequences**: Shorter sequences automatically cycle, enabling compact test definitions
3. **Dual Mode Operation**: Supports both deterministic and random testing from the same interface
4. **Complete Packet Generation**: The `next()` method generates complete ready-to-send packets
5. **Resource Management**: The transaction counter and iterators track state for test management
6. **Test Reuse**: The `reset_iterators()` method enables test reuse and multiple test runs

