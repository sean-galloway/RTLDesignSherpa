<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# apb_sequence.py

APB Sequence class for test pattern generation and management. This module provides a flexible framework for creating and managing sequences of APB transactions with configurable patterns, timing, and randomization.

## Overview

The `apb_sequence.py` module provides the `APBSequence` class, which enables:
- **Flexible sequence definition** with configurable patterns
- **Multiple selection modes** (sequential or random)
- **Iterator-based value generation** with automatic cycling
- **Direct packet generation** for easy integration
- **Comprehensive timing control** and randomization support

### Key Features
- **Dataclass-based configuration** for clean, readable sequence definitions
- **Automatic iterator management** with cycling through sequences
- **Built-in randomization support** for flexible test patterns
- **Direct APBPacket generation** for seamless integration
- **Multiple sequence types** (addresses, data, strobes, delays)

## Core Class

### APBSequence

Configuration class for test patterns with direct packet generation capabilities.

#### Constructor

```python
@dataclass
class APBSequence:
    name: str = "basic"
    pwrite_seq: List[bool] = field(default_factory=list)
    addr_seq: List[int] = field(default_factory=list)
    data_seq: List[int] = field(default_factory=list)
    strb_seq: List[int] = field(default_factory=list)
    pprot_seq: List[int] = field(default_factory=list)
    inter_cycle_delays: List[int] = field(default_factory=list)
    master_randomizer: Optional[Dict] = None
    slave_randomizer: Optional[Tuple] = None
    other_randomizer: Optional[Tuple] = None
    use_random_selection: bool = False
    verify_data: bool = True
    data_width: int = 32
    transaction_count: int = 0
```

**Parameters:**
- `name`: Sequence identifier for logging and debugging
- `pwrite_seq`: List of write/read operations (True=Write, False=Read)
- `addr_seq`: List of addresses to cycle through
- `data_seq`: List of data values for write operations
- `strb_seq`: List of strobe patterns for write operations
- `pprot_seq`: List of protection attribute values
- `inter_cycle_delays`: List of delay values between transactions
- `master_randomizer`: Randomizer configuration for master timing
- `slave_randomizer`: Randomizer configuration for slave behavior
- `other_randomizer`: Additional randomizer configuration
- `use_random_selection`: If True, randomly select from sequences instead of cycling
- `verify_data`: Enable data verification for read operations
- `data_width`: Data width for packet generation
- `transaction_count`: Current transaction counter

```python
# Create basic alternating read/write sequence
sequence = APBSequence(
    name="alternating_test",
    pwrite_seq=[True, False, True, False],  # Write, Read, Write, Read
    addr_seq=[0x100, 0x104, 0x108, 0x10C],  # Sequential addresses
    data_seq=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    strb_seq=[0xF, 0xF, 0xF, 0xF],          # Full strobes
    inter_cycle_delays=[2, 1, 2, 1]         # Variable delays
)

# Create random selection sequence
random_sequence = APBSequence(
    name="random_test",
    pwrite_seq=[True, False],               # Mix of reads and writes
    addr_seq=list(range(0x1000, 0x2000, 4)), # Large address range
    data_seq=[0xAAAAAAAA, 0x55555555, 0xFFFFFFFF, 0x00000000],
    strb_seq=[0xF, 0x3, 0xC, 0x5],          # Various strobe patterns
    use_random_selection=True               # Random selection mode
)
```

#### Methods

##### `reset_iterators()`

Reset all iterators to the beginning of their sequences.

```python
sequence.reset_iterators()  # Start over from beginning
```

##### `next_pwrite() -> bool`

Get the next write/read operation from the sequence.

**Returns:** True for write, False for read

```python
is_write = sequence.next_pwrite()
if is_write:
    print("Next operation: WRITE")
else:
    print("Next operation: READ")
```

##### `next_addr() -> int`

Get the next address from the address sequence.

**Returns:** Address value

```python
address = sequence.next_addr()
print(f"Next address: 0x{address:X}")
```

##### `next_data() -> int`

Get the next data value from the data sequence.

**Returns:** Data value for write operations

```python
if is_write:
    data = sequence.next_data()
    print(f"Write data: 0x{data:X}")
```

##### `next_strb() -> int`

Get the next strobe pattern from the strobe sequence.

**Returns:** Strobe mask value

```python
if is_write:
    strobes = sequence.next_strb()
    print(f"Strobes: 0b{strobes:04b}")
```

##### `next_pprot() -> int`

Get the next protection attribute value.

**Returns:** Protection attribute value

```python
protection = sequence.next_pprot()
print(f"Protection: 0x{protection:X}")
```

##### `next_delay() -> int`

Get the next inter-cycle delay value.

**Returns:** Delay in clock cycles

```python
delay = sequence.next_delay()
print(f"Delay: {delay} cycles")
```

##### `next() -> APBPacket`

Generate the next complete APB packet from the sequence.

**Returns:** APBPacket ready for transmission

```python
packet = sequence.next()
print(f"Generated: {packet.formatted(compact=True)}")
```

##### `has_more_transactions() -> bool`

Check if there are more transactions available in the sequence.

**Returns:** True if more transactions can be generated

```python
while sequence.has_more_transactions():
    packet = sequence.next()
    # Process packet
```

## Usage Patterns

### Basic Sequential Sequence

```python
from CocoTBFramework.components.apb.apb_sequence import APBSequence

# Create a simple register test sequence
register_sequence = APBSequence(
    name="register_test",
    pwrite_seq=[True, False] * 10,          # 10 write-read pairs
    addr_seq=[0x1000 + i*4 for i in range(10)],  # Sequential addresses
    data_seq=[0xA0000000 + i for i in range(10)], # Pattern data
    strb_seq=[0xF] * 10,                    # Always full strobes
    inter_cycle_delays=[1] * 19             # Single cycle delays
)

# Generate all packets
packets = []
while register_sequence.has_more_transactions():
    packet = register_sequence.next()
    packets.append(packet)

print(f"Generated {len(packets)} packets")
```

### Burst Write/Read Sequence

```python
# Create burst write followed by burst read
burst_sequence = APBSequence(
    name="burst_test",
    # First 16 writes, then 16 reads
    pwrite_seq=[True] * 16 + [False] * 16,
    addr_seq=[0x2000 + i*4 for i in range(16)],  # Will cycle for reads
    data_seq=[0xB0000000 + i for i in range(16)], # Burst data pattern
    strb_seq=[0xF],                         # Single strobe pattern
    inter_cycle_delays=[0],                 # Back-to-back transfers
    verify_data=True
)

# Generate burst sequence
burst_packets = []
for i in range(32):  # 16 writes + 16 reads
    packet = burst_sequence.next()
    burst_packets.append(packet)
    print(f"Burst {i}: {packet.formatted(compact=True)}")
```

### Random Access Pattern

```python
# Create random access sequence
random_sequence = APBSequence(
    name="random_access",
    pwrite_seq=[True, False],               # Equal read/write probability
    addr_seq=[0x1000, 0x1004, 0x1008, 0x100C, 0x2000, 0x2004, 0x3000],
    data_seq=[0x11111111, 0x22222222, 0x33333333, 0x44444444, 0xAAAAAAAA, 0x55555555],
    strb_seq=[0xF, 0x3, 0xC, 0x5, 0xA],     # Various strobe patterns
    inter_cycle_delays=[0, 1, 2, 5, 10],    # Variable delays
    use_random_selection=True               # Enable random selection
)

# Generate random packets
random_packets = []
for i in range(50):
    packet = random_sequence.next()
    random_packets.append(packet)
```

### Strobe Pattern Testing

```python
# Create sequence testing different strobe patterns
strobe_sequence = APBSequence(
    name="strobe_test",
    pwrite_seq=[True] * 8,                  # All writes
    addr_seq=[0x4000],                      # Same address
    data_seq=[0x12345678],                  # Same data
    strb_seq=[0x1, 0x2, 0x4, 0x8, 0x3, 0xC, 0x5, 0xF],  # All strobe combinations
    inter_cycle_delays=[2] * 7
)

# Generate strobe test packets
strobe_packets = []
while strobe_sequence.has_more_transactions():
    packet = strobe_sequence.next()
    strobe_packets.append(packet)
    print(f"Strobe test: data=0x{packet.pwdata:X}, strb=0b{packet.pstrb:04b}")
```

### Performance Testing Sequence

```python
# Create high-performance back-to-back sequence
perf_sequence = APBSequence(
    name="performance_test",
    pwrite_seq=[True] * 1000,               # 1000 consecutive writes
    addr_seq=[0x8000 + i*4 for i in range(100)],  # 100 unique addresses (cycles)
    data_seq=[i for i in range(1000)],     # Sequential data
    strb_seq=[0xF],                        # Always full strobes
    inter_cycle_delays=[0],                # No delays - maximum performance
)

# Generate performance test
start_time = time.time()
perf_packets = []
while perf_sequence.has_more_transactions():
    packet = perf_sequence.next()
    perf_packets.append(packet)

print(f"Generated {len(perf_packets)} packets in {time.time() - start_time:.3f}s")
```

### Multi-Phase Test Sequence

```python
def create_multi_phase_sequence():
    """Create a sequence with multiple test phases"""
    
    # Phase 1: Initialization writes
    init_writes = [True] * 8
    init_addrs = [0x1000 + i*4 for i in range(8)]
    init_data = [0] * 8  # Initialize to zero
    
    # Phase 2: Pattern writes
    pattern_writes = [True] * 16
    pattern_addrs = [0x1000 + i*4 for i in range(8)]  # Will cycle
    pattern_data = [0xA5A5A5A5, 0x5A5A5A5A] * 8  # Alternating pattern
    
    # Phase 3: Verification reads
    verify_reads = [False] * 8
    verify_addrs = [0x1000 + i*4 for i in range(8)]
    
    # Combine phases
    combined_sequence = APBSequence(
        name="multi_phase_test",
        pwrite_seq=init_writes + pattern_writes + verify_reads,
        addr_seq=init_addrs + pattern_addrs + verify_addrs,
        data_seq=init_data + pattern_data + [0] * 8,  # Reads don't need data
        strb_seq=[0xF] * 32,
        inter_cycle_delays=[1] * 31,
        verify_data=True
    )
    
    return combined_sequence

multi_phase = create_multi_phase_sequence()
```

### Error Injection Sequence

```python
# Create sequence with error conditions
error_sequence = APBSequence(
    name="error_injection",
    pwrite_seq=[True, True, False, True, False],
    addr_seq=[0x100, 0xDEAD, 0x100, 0xBEEF, 0xBEEF],  # Some invalid addresses
    data_seq=[0x12345678, 0xBAADF00D, 0, 0xDEADBEEF, 0],
    strb_seq=[0xF, 0x0, 0xF, 0xF, 0xF],    # Invalid strobe pattern
    pprot_seq=[0, 7, 0, 3, 0],              # Various protection levels
    inter_cycle_delays=[1, 5, 1, 2, 1]
)

# Generate error test packets
error_packets = []
while error_sequence.has_more_transactions():
    packet = error_sequence.next()
    error_packets.append(packet)
    
    # Check for potential error conditions
    if packet.paddr > 0x8000:
        print(f"Warning: High address 0x{packet.paddr:X} may cause error")
    if packet.direction == 'WRITE' and packet.pstrb == 0:
        print(f"Warning: Write with no strobes may cause error")
```

### Timing-Critical Sequence

```python
# Create sequence with specific timing requirements
timing_sequence = APBSequence(
    name="timing_critical",
    pwrite_seq=[True, False, True, False, True, False],
    addr_seq=[0x5000, 0x5000, 0x5004, 0x5004, 0x5008, 0x5008],
    data_seq=[0x1, 0x0, 0x2, 0x0, 0x3, 0x0],
    strb_seq=[0xF, 0xF, 0xF, 0xF, 0xF, 0xF],
    inter_cycle_delays=[0, 10, 0, 15, 0, 20]  # Specific timing requirements
)

# Process with timing awareness
timing_packets = []
while timing_sequence.has_more_transactions():
    packet = timing_sequence.next()
    delay = timing_sequence.next_delay()
    
    timing_packets.append((packet, delay))
    print(f"Packet: {packet.formatted(compact=True)}, Delay: {delay}")
```

## Integration with Test Framework

### Testbench Integration

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.components.apb import APBMaster, APBSequence

@cocotb.test()
async def sequence_driven_test(dut):
    # Create master
    master = APBMaster(dut, "SeqMaster", "apb_", dut.clk)
    
    # Create test sequence
    test_sequence = APBSequence(
        name="testbench_sequence",
        pwrite_seq=[True, False] * 5,
        addr_seq=[0x1000 + i*4 for i in range(5)],
        data_seq=[0x10000000 + i for i in range(5)],
        strb_seq=[0xF] * 5,
        inter_cycle_delays=[1, 2, 1, 2, 1, 2, 1, 2, 1]
    )
    
    # Execute sequence
    while test_sequence.has_more_transactions():
        packet = test_sequence.next()
        delay = test_sequence.next_delay()
        
        # Send packet
        await master.send(packet)
        print(f"Sent: {packet.formatted(compact=True)}")
        
        # Apply inter-cycle delay
        if delay > 0:
            for _ in range(delay):
                await RisingEdge(dut.clk)
    
    # Wait for completion
    while master.transfer_busy:
        await RisingEdge(dut.clk)
```

### Loop-Based Sequence Execution

```python
async def execute_sequence_loop(master, sequence, cycles=None):
    """Execute a sequence with optional cycling"""
    cycle_count = 0
    max_cycles = cycles or float('inf')
    
    while cycle_count < max_cycles:
        if not sequence.has_more_transactions():
            if cycles is None:
                break  # Finite sequence completed
            else:
                sequence.reset_iterators()  # Restart for cycling
        
        packet = sequence.next()
        delay = sequence.next_delay()
        
        await master.send(packet)
        
        if delay > 0:
            await Timer(delay, units='ns')
        
        cycle_count += 1
        
        if cycle_count % 100 == 0:
            print(f"Executed {cycle_count} transactions")

# Execute sequence 5 times
await execute_sequence_loop(master, test_sequence, cycles=5)
```

### Sequence Composition

```python
def compose_sequences(*sequences):
    """Compose multiple sequences into one"""
    combined = APBSequence(name="composed_sequence")
    
    for seq in sequences:
        # Reset to ensure we get all transactions
        seq.reset_iterators()
        
        while seq.has_more_transactions():
            packet = seq.next()
            
            # Extract packet fields and add to combined sequences
            combined.pwrite_seq.append(packet.pwrite == 1)
            combined.addr_seq.append(packet.paddr)
            combined.data_seq.append(packet.pwdata if packet.pwrite else 0)
            combined.strb_seq.append(packet.pstrb)
            combined.pprot_seq.append(packet.pprot)
            combined.inter_cycle_delays.append(1)  # Default delay
    
    # Reinitialize iterators
    combined.reset_iterators()
    return combined

# Compose multiple test phases
init_seq = create_initialization_sequence()
test_seq = create_functional_test_sequence()
cleanup_seq = create_cleanup_sequence()

full_test = compose_sequences(init_seq, test_seq, cleanup_seq)
```

### Statistical Analysis

```python
def analyze_sequence(sequence):
    """Analyze sequence characteristics"""
    sequence.reset_iterators()
    
    stats = {
        'total_transactions': 0,
        'write_count': 0,
        'read_count': 0,
        'unique_addresses': set(),
        'strobe_patterns': set(),
        'total_delay': 0
    }
    
    while sequence.has_more_transactions():
        packet = sequence.next()
        delay = sequence.next_delay()
        
        stats['total_transactions'] += 1
        if packet.direction == 'WRITE':
            stats['write_count'] += 1
        else:
            stats['read_count'] += 1
        
        stats['unique_addresses'].add(packet.paddr)
        stats['strobe_patterns'].add(packet.pstrb)
        stats['total_delay'] += delay
    
    # Convert sets to counts
    stats['unique_addresses'] = len(stats['unique_addresses'])
    stats['strobe_patterns'] = len(stats['strobe_patterns'])
    
    # Calculate ratios
    if stats['total_transactions'] > 0:
        stats['write_ratio'] = stats['write_count'] / stats['total_transactions']
        stats['average_delay'] = stats['total_delay'] / stats['total_transactions']
    
    return stats

# Analyze test sequence
analysis = analyze_sequence(test_sequence)
print(f"Sequence analysis: {analysis}")
```

## Best Practices

### 1. **Use Descriptive Names**
```python
sequence = APBSequence(
    name="register_bank_initialization",  # Clear, descriptive name
    # ... rest of configuration
)
```

### 2. **Validate Sequence Configuration**
```python
def validate_sequence(sequence):
    """Validate sequence configuration"""
    if not sequence.pwrite_seq:
        raise ValueError("Empty pwrite_seq")
    
    if not sequence.addr_seq:
        raise ValueError("Empty addr_seq")
    
    # Check for write operations without data
    if any(sequence.pwrite_seq) and not sequence.data_seq:
        raise ValueError("Write operations require data_seq")
    
    return True

validate_sequence(my_sequence)
```

### 3. **Handle Sequence Completion**
```python
# Always check for more transactions
while sequence.has_more_transactions():
    packet = sequence.next()
    # Process packet

# Or use explicit transaction counting
for i in range(len(sequence.pwrite_seq)):
    packet = sequence.next()
    # Process packet
```

### 4. **Use Reset for Repeatable Tests**
```python
# Reset before each test run
sequence.reset_iterators()

# Run test
run_sequence_test(sequence)

# Reset for next test
sequence.reset_iterators()
run_different_test(sequence)
```

### 5. **Combine Sequential and Random Modes**
```python
# Create base sequence
base_sequence = APBSequence(
    pwrite_seq=[True, False] * 10,
    addr_seq=list(range(0x1000, 0x1100, 4)),
    data_seq=list(range(100)),
    use_random_selection=False  # Sequential first
)

# Run sequential test
run_sequence_test(base_sequence)

# Switch to random mode for stress testing
base_sequence.use_random_selection = True
run_stress_test(base_sequence)
```

The APBSequence class provides a powerful and flexible foundation for creating comprehensive APB test patterns, from simple register access sequences to complex multi-phase verification scenarios.