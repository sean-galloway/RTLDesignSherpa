# AXI4 Sequence Generation Documentation

## Introduction

AXI4 Sequences are a powerful way to create structured and reusable transactions for AXI4 verification. This document details the sequence generation capabilities of the AXI4 verification environment, covering transaction sequences, address sequences, data sequences, and protocol sequences.

## Sequence Hierarchy

The AXI4 sequence architecture follows a hierarchical structure:

1. **AXI4BaseSequence**: Base class with common utilities for all sequence types
2. **AXI4AddressSequence**: Generates AW/AR channel transactions
3. **AXI4DataSequence**: Generates W/R channel transactions
4. **AXI4ResponseSequence**: Generates B/R channel responses
5. **AXI4TransactionSequence**: Coordinates address and data sequences into complete transactions
6. **AXI4ProtocolSequence**: Creates specialized protocol test scenarios

This hierarchical approach allows for flexible sequence composition and reuse.

## AXI4TransactionSequence

The `AXI4TransactionSequence` is the main sequence class for generating complete AXI4 transactions.

### Creating a Transaction Sequence

```python
from axi4_seq_transaction import AXI4TransactionSequence

# Create a sequence
sequence = AXI4TransactionSequence(
    name="my_sequence",          # Sequence name
    id_width=8,                  # ID width in bits
    addr_width=32,               # Address width in bits
    data_width=32,               # Data width in bits
    user_width=1,                # User signal width in bits
    randomization_config=None    # Optional randomization configuration
)
```

### Adding Write Transactions

```python
# Add a single-beat write transaction
write_id = sequence.add_write_transaction(
    addr=0x1000,                 # Target address
    data_values=[0xDEADBEEF],    # Data to write (list of values)
    id_value=None,               # Transaction ID (auto-generated if None)
    burst_size=2,                # Size (log2 of bytes): 0=byte, 1=halfword, 2=word
    burst_type=1,                # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    strb_values=None,            # Optional strobe values
    lock=0,                      # Lock: 0=normal, 1=exclusive
    cache=0,                     # Cache type
    prot=0,                      # Protection type
    qos=0,                       # Quality of Service
    region=0,                    # Region identifier
    user=0,                      # User signal
    dependencies=None            # List of transaction IDs this depends on
)

# Add a multi-beat burst write transaction
burst_write_id = sequence.add_write_transaction(
    addr=0x2000,
    data_values=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    burst_type=1                 # INCR burst
)
```

### Adding Read Transactions

```python
# Add a single-beat read transaction
read_id = sequence.add_read_transaction(
    addr=0x1000,                 # Target address
    burst_len=0,                 # Burst length (0 = 1 beat)
    id_value=None,               # Transaction ID (auto-generated if None)
    burst_size=2,                # Size (log2 of bytes)
    burst_type=1,                # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    lock=0,                      # Lock: 0=normal, 1=exclusive
    cache=0,                     # Cache type
    prot=0,                      # Protection type
    qos=0,                       # Quality of Service
    region=0,                    # Region identifier
    user=0,                      # User signal
    dependencies=[write_id]      # Make read depend on previous write
)

# Add a multi-beat burst read transaction
burst_read_id = sequence.add_read_transaction(
    addr=0x2000,
    burst_len=3,                 # 4 beats (length = N means N+1 beats)
    burst_type=1,                # INCR burst
    dependencies=[burst_write_id]
)
```

### Adding Expected Responses

For AXI4-specific randomization, a specialized randomization configuration class is provided:

```python
from axi4_randomization_config import AXI4RandomizationConfig

# Create AXI4-specific randomization configuration
config = AXI4RandomizationConfig()

# Configure for specific data width
config.configure_for_data_width(data_width=32)

# Configure exclusive access frequency
config.set_exclusive_access_mode(probability=0.1)  # 10% exclusive transactions

# Configure error injection rate
config.set_error_injection_rate(error_rate=0.05)  # 5% error responses

# Use with sequence
sequence = AXI4TransactionSequence(
    name="axi4_random_sequence",
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    randomization_config=config
)
```

## Command Handler Usage

The AXI4CommandHandler coordinates transactions across channels. It's useful for handling transaction sequences:

```python
from axi4_command_handler import AXI4CommandHandler

# Create command handler
cmd_handler = AXI4CommandHandler(
    aw_master=master.aw_master,
    w_master=master.w_master,
    b_slave=master.b_slave,
    ar_master=master.ar_master,
    r_slave=master.r_slave,
    memory_model=memory_model,
    log=logger
)

# Start the handler
await cmd_handler.start()

# Process a transaction sequence
sequence = AXI4TransactionSequence.create_protocol_stress_test(data_width=32)
complete_event = await cmd_handler.process_transaction_sequence(sequence)

# Wait for completion
await complete_event.wait()

# Get stats
stats = cmd_handler.get_stats()
print(f"Write transactions: {stats['write_transactions']}")
print(f"Read transactions: {stats['read_transactions']}")

# Stop the handler
await cmd_handler.stop()
```

## Common Transaction Patterns

Here are some common AXI4 transaction patterns and how to implement them:

### Memory Initialization

```python
# Initialize a region of memory with a pattern
def create_memory_init_sequence(base_addr, size, pattern, burst_size=2):
    sequence = AXI4TransactionSequence(name="memory_init")
    
    # Calculate number of words based on data width
    bytes_per_word = 1 << burst_size
    word_count = (size + bytes_per_word - 1) // bytes_per_word
    
    # Generate data values based on pattern
    if pattern == "incrementing":
        data_values = [i for i in range(word_count)]
    elif pattern == "address":
        data_values = [base_addr + (i * bytes_per_word) for i in range(word_count)]
    elif pattern == "random":
        import random
        data_values = [random.randint(0, 0xFFFFFFFF) for _ in range(word_count)]
    else:  # Fixed pattern
        data_values = [pattern] * word_count
    
    # Add write transaction - split into multiple transactions if needed
    max_burst_len = 255  # Maximum AXI4 burst length
    
    for i in range(0, word_count, max_burst_len + 1):
        # Calculate burst length for this transaction
        burst_len = min(max_burst_len, word_count - i - 1)
        if burst_len < 0:
            burst_len = 0
        
        # Add transaction
        sequence.add_write_transaction(
            addr=base_addr + (i * bytes_per_word),
            data_values=data_values[i:i+burst_len+1],
            burst_size=burst_size,
            burst_type=1  # INCR
        )
    
    return sequence
```

### Memory Copy

```python
# Create a sequence to copy data from one memory region to another
def create_memory_copy_sequence(src_addr, dst_addr, size, burst_size=2):
    sequence = AXI4TransactionSequence(name="memory_copy")
    
    # Calculate number of words based on data width
    bytes_per_word = 1 << burst_size
    word_count = (size + bytes_per_word - 1) // bytes_per_word
    
    # Maximum burst length
    max_burst_len = 255
    
    # Process in chunks
    for i in range(0, word_count, max_burst_len + 1):
        # Calculate burst length for this chunk
        burst_len = min(max_burst_len, word_count - i - 1)
        if burst_len < 0:
            burst_len = 0
        
        # Current addresses
        current_src = src_addr + (i * bytes_per_word)
        current_dst = dst_addr + (i * bytes_per_word)
        
        # Read from source
        read_id = sequence.add_read_transaction(
            addr=current_src,
            burst_len=burst_len,
            burst_size=burst_size,
            burst_type=1  # INCR
        )
        
        # Write to destination, dependent on read completion
        sequence.add_write_transaction(
            addr=current_dst,
            data_values=[0] * (burst_len + 1),  # Placeholder, actual data will come from response
            burst_size=burst_size,
            burst_type=1,  # INCR
            dependencies=[read_id]
        )
    
    return sequence
```

### Exclusive Access Pattern

```python
# Create a sequence for an atomic read-modify-write operation using exclusive access
def create_atomic_rmw_sequence(addr, modify_function, burst_size=2):
    sequence = AXI4TransactionSequence(name="atomic_rmw")
    
    # Exclusive read
    read_id = sequence.add_read_transaction(
        addr=addr,
        burst_len=0,  # Single beat
        burst_size=burst_size,
        lock=1  # Exclusive access
    )
    
    # Function to process the read result and generate new value
    # This will be executed at runtime based on the actual read data
    def generate_modified_value(read_data):
        return modify_function(read_data)
    
    # Exclusive write - the actual data will be generated at runtime
    # based on the read response
    write_id = sequence.add_write_transaction(
        addr=addr,
        data_values=[0],  # Placeholder
        burst_size=burst_size,
        lock=1,  # Exclusive access
        dependencies=[read_id]
    )
    
    # Add expected response for the write
    sequence.add_write_response(write_id, resp=1)  # EXOKAY
    
    return sequence, read_id, write_id
```

### QoS Priority Test

```python
# Create a sequence to test QoS prioritization
def create_qos_priority_test(base_addr, qos_values=[0, 4, 8, 15]):
    sequence = AXI4TransactionSequence(name="qos_priority_test")
    
    # Add low-priority transactions first
    for i in range(10):
        sequence.add_write_transaction(
            addr=base_addr + (i * 4),
            data_values=[0xA0000000 + i],
            qos=0  # Lowest priority
        )
    
    # Add high-priority transactions that should be processed first
    for qos in qos_values:
        for i in range(5):
            sequence.add_write_transaction(
                addr=base_addr + 0x1000 + (qos * 0x100) + (i * 4),
                data_values=[0xB0000000 + (qos << 16) + i],
                qos=qos
            )
    
    return sequence
```

## Common Testing Patterns

### Protocol Compliance Test

```python
async def run_protocol_compliance_test(dut):
    # Create test environment with master, slave, monitor, and scoreboard
    master, slave, monitor, scoreboard = create_protocol_compliance_environment(
        dut=dut,
        prefix="axi",
        clock=dut.clk
    )
    
    # Create protocol test sequence
    sequence = AXI4ProtocolSequence.create_protocol_test_suite(
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1
    )
    
    # Start components
    await slave.start_processor()
    
    # Get the transaction sequence from the protocol sequence
    tx_sequence = sequence.get_transaction_sequence()
    
    # Execute sequence
    await master.execute_transaction_sequence(tx_sequence)
    
    # Wait for completion
    for _ in range(1000):
        await RisingEdge(dut.clk)
    
    # Stop components
    await slave.stop_processor()
    
    # Check for protocol violations
    if sequence.stats['protocol_violations'] > 0:
        print(f"Detected {sequence.stats['protocol_violations']} protocol violations")
        for id_value in range(32):  # Check IDs 0-31
            for is_read in [False, True]:
                if sequence.has_protocol_violations(id_value, is_read):
                    violations = sequence.get_protocol_violations(id_value, is_read)
                    for violation in violations:
                        print(f"Violation in {'Read' if is_read else 'Write'} ID={id_value}: {violation}")
    
    # Check scoreboard results
    errors = scoreboard.get_error_count()
    if errors > 0:
        print(f"Detected {errors} scoreboard errors")
        for error in scoreboard.get_errors():
            print(f"Scoreboard error: {error}")
    
    return sequence.stats, scoreboard.get_stats()
```

### Performance Benchmark Test

```python
async def run_performance_benchmark(dut, transaction_count=1000, burst_length=16):
    # Create performance test environment
    master, slave, monitor = create_performance_test_environment(
        dut=dut,
        prefix="axi",
        clock=dut.clk
    )
    
    # Start slave
    await slave.start_processor()
    
    # Create statistics tracking
    stats = {
        'start_time': 0,
        'end_time': 0,
        'write_transactions': 0,
        'read_transactions': 0,
        'write_beats': 0,
        'read_beats': 0
    }
    
    # Record start time
    stats['start_time'] = get_sim_time('ns')
    
    # Execute write transactions
    for i in range(transaction_count):
        addr = 0x10000 + (i * 64)
        data = [(0xA0000000 + i) for _ in range(burst_length)]
        
        await master.write(
            addr=addr,
            data=data,
            burst_type=1,  # INCR
            id=i % 16  # Use multiple IDs for parallelism
        )
        
        stats['write_transactions'] += 1
        stats['write_beats'] += burst_length
    
    # Execute read transactions
    for i in range(transaction_count):
        addr = 0x10000 + (i * 64)
        
        await master.read(
            addr=addr,
            burst_type=1,  # INCR
            length=burst_length - 1,
            id=i % 16  # Use multiple IDs for parallelism
        )
        
        stats['read_transactions'] += 1
        stats['read_beats'] += burst_length
    
    # Record end time
    stats['end_time'] = get_sim_time('ns')
    
    # Calculate metrics
    duration_ns = stats['end_time'] - stats['start_time']
    write_bandwidth = (stats['write_beats'] * 4) / (duration_ns / 1000000000)  # Bytes per second
    read_bandwidth = (stats['read_beats'] * 4) / (duration_ns / 1000000000)   # Bytes per second
    
    print(f"Test duration: {duration_ns/1000000} ms")
    print(f"Write bandwidth: {write_bandwidth/1000000:.2f} MB/s")
    print(f"Read bandwidth: {read_bandwidth/1000000:.2f} MB/s")
    
    # Stop slave
    await slave.stop_processor()
    
    return stats
```

## Creating Custom Sequences

To create custom sequences with specialized behavior:

```python
class MyCustomSequence(AXI4TransactionSequence):
    def __init__(self, name="custom_sequence", **kwargs):
        super().__init__(name=name, **kwargs)
    
    def generate_custom_pattern(self, base_addr, count):
        """Generate a custom transaction pattern"""
        # Add your custom pattern generation here
        for i in range(count):
            addr = base_addr + (i * 4)
            data = [0xC0FFEE00 + i]
            
            # Add write transaction
            write_id = self.add_write_transaction(
                addr=addr,
                data_values=data
            )
            
            # Add read transaction dependent on write
            read_id = self.add_read_transaction(
                addr=addr,
                dependencies=[write_id]
            )
            
            # Add expected response
            self.add_read_response_data(read_id, data)
        
        return self
```

## Conclusion

This document provides a comprehensive guide to using the AXI4 sequence generation capabilities of the verification environment. By combining these sequence generators, you can create complex test scenarios that thoroughly verify AXI4 interfaces while maintaining reusability and structure.

The sequence hierarchy allows for flexible composition of tests, from low-level channel transactions to high-level protocol test suites. The randomization capabilities enable thorough coverage through constrained random testing. The factory methods provide ready-to-use sequence templates for common verification scenarios.

For more advanced needs, custom sequences can be created by extending the base sequence classes and implementing specialized behavior. verification, you can add expected responses:

```python
# Add expected read response data
sequence.add_read_response_data(
    id_value=read_id,            # Transaction ID
    data_values=[0xDEADBEEF],    # Expected data values
    resp_values=[0],             # Response codes (0=OKAY)
    user=0                       # User signal
)

# Add expected burst read response data
sequence.add_read_response_data(
    id_value=burst_read_id,
    data_values=[0x11111111, 0x22222222, 0x33333333, 0x44444444]
)

# Add expected write response
sequence.add_write_response(
    id_value=write_id,
    resp=0,                      # Response code (0=OKAY, 1=EXOKAY)
    user=0                       # User signal
)
```

### Accessing Transaction Components

To get the components of a transaction:

```python
# Get write address packet
aw_packet = sequence.get_write_addr_packet(write_id)

# Get write data packets
w_packets = sequence.get_write_data_packets(write_id)

# Get read address packet
ar_packet = sequence.get_read_addr_packet(read_id)

# Get expected read response packets
r_packets = sequence.get_read_response_packets(read_id)

# Get expected write response packet
b_packet = sequence.get_write_response_packet(write_id)
```

### Managing Dependencies

Transaction dependencies allow ordering control:

```python
# Check if a transaction has dependencies
has_dependency = sequence.has_dependency(
    id_value=read_id,
    dependency_id=write_id,
    is_read=True
)

# Get all dependencies of a transaction
dependencies = sequence.get_dependencies(
    id_value=read_id,
    is_read=True
)

# Get transactions ready for execution (no pending dependencies)
ready_reads = sequence.get_ready_transactions(is_read=True)
ready_writes = sequence.get_ready_transactions(is_read=False)

# Mark a transaction as complete
sequence.complete_transaction(
    id_value=write_id,
    is_read=False
)
```

## AXI4AddressSequence

For more detailed control of address channel transactions, use `AXI4AddressSequence`.

### Creating an Address Sequence

```python
from axi4_seq_address import AXI4AddressSequence

# Create a write address sequence
aw_sequence = AXI4AddressSequence(
    name="aw_sequence",          # Sequence name
    channel="AW",                # Channel: "AW" or "AR"
    id_width=8,                  # ID width in bits
    addr_width=32,               # Address width in bits
    user_width=1,                # User signal width in bits
    randomization_config=None    # Optional randomization configuration
)

# Create a read address sequence
ar_sequence = AXI4AddressSequence(
    name="ar_sequence",
    channel="AR",
    id_width=8,
    addr_width=32,
    user_width=1
)
```

### Adding Address Transactions

```python
# Add a write address transaction
aw_sequence.add_transaction(
    addr=0x1000,                 # Target address
    id_value=0,                  # Transaction ID
    burst_len=0,                 # Burst length (0 = 1 beat)
    burst_size=2,                # Size (log2 of bytes)
    burst_type=1,                # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    lock=0,                      # Lock: 0=normal, 1=exclusive
    cache=0,                     # Cache type
    prot=0,                      # Protection type
    qos=0,                       # Quality of Service
    region=0,                    # Region identifier
    user=0                       # User signal
)
```

### Generating and Accessing Packets

```python
# Generate all packets
packets = aw_sequence.generate_packets()

# Generate a specific number of packets
packets = aw_sequence.generate_packets(count=5)

# Get a specific packet
packet = aw_sequence.get_packet(index=0)
```

### Factory Methods

The AXI4AddressSequence class provides factory methods for common patterns:

```python
# Create sequential address sequence
seq_addr = AXI4AddressSequence.create_sequential_addresses(
    start_addr=0x1000,
    count=10,
    increment=4,                 # Increment between addresses
    id_value=0,
    burst_size=2,
    channel="AW"
)

# Create 4KB boundary test sequence
boundary_test = AXI4AddressSequence.create_4k_boundary_test(
    channel="AW",
    id_value=0
)

# Create protection variations test
prot_test = AXI4AddressSequence.create_protection_variations(
    start_addr=0x1000,
    id_value=0,
    channel="AW"
)

# Create cache variations test
cache_test = AXI4AddressSequence.create_cache_variations(
    start_addr=0x1000,
    id_value=0,
    channel="AW"
)

# Create QoS variations test
qos_test = AXI4AddressSequence.create_qos_variations(
    start_addr=0x1000,
    id_value=0,
    channel="AW"
)

# Create random transactions
random_test = AXI4AddressSequence.create_random_transactions(
    count=10,
    addr_range=(0x1000, 0x2000),
    id_range=(0, 15),
    channel="AW"
)
```

## AXI4DataSequence

For more detailed control of data channel transactions, use `AXI4DataSequence`.

### Creating a Data Sequence

```python
from axi4_seq_data import AXI4DataSequence

# Create a write data sequence
w_sequence = AXI4DataSequence(
    name="w_sequence",           # Sequence name
    channel="W",                 # Channel: "W" or "R"
    data_width=32,               # Data width in bits
    user_width=1,                # User signal width in bits
    randomization_config=None    # Optional randomization configuration
)

# Create a read data sequence
r_sequence = AXI4DataSequence(
    name="r_sequence",
    channel="R",
    data_width=32,
    user_width=1
)
```

### Adding Data Transactions

```python
# Add a write data transaction
w_sequence.add_transaction(
    data=0xDEADBEEF,             # Data value
    strb=0xF,                    # Write strobe (for W channel)
    last=1,                      # Last indicator (1 = last transfer in burst)
    user=0                       # User signal
)

# Add a read data transaction
r_sequence.add_transaction(
    data=0xDEADBEEF,             # Data value
    last=1,                      # Last indicator
    user=0,                      # User signal
    id_value=0,                  # Transaction ID (for R channel)
    resp=0                       # Response code (for R channel)
)
```

### Adding Complete Bursts

```python
# Add a complete write data burst
w_sequence.add_burst(
    data_values=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    strb_values=[0xF, 0xF, 0xF, 0xF],
    user_values=[0, 0, 0, 0]
)

# Add a complete read data burst
r_sequence.add_burst(
    id_value=0,
    data_values=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    resp_value=0,                # Response code for all beats
    user_values=[0, 0, 0, 0]
)
```

### Generating and Accessing Packets

```python
# Generate all packets
packets = w_sequence.generate_packets()

# Generate a specific number of packets
packets = w_sequence.generate_packets(count=5)

# Get a specific packet
packet = w_sequence.get_packet(index=0)
```

### Factory Methods

The AXI4DataSequence class provides factory methods for common patterns:

```python
# Create incrementing data sequence
incr_data = AXI4DataSequence.create_incremental_data(
    start_value=0,
    count=10,
    increment=1,
    channel="W"
)

# Create pattern test sequence
pattern_test = AXI4DataSequence.create_pattern_test(
    channel="W",
    id_value=None,
    data_width=32
)

# Create strobe test sequence (W channel only)
strobe_test = AXI4DataSequence.create_strobe_test(
    data_width=32
)

# Create error response test sequence (R channel only)
error_test = AXI4DataSequence.create_error_response_test(
    id_value=0,
    data_width=32
)

# Create burst test sequence
burst_test = AXI4DataSequence.create_burst_test(
    burst_lengths=[0, 3, 7, 15],  # 1, 4, 8, 16 beats
    channel="W"
)
```

### Data Pattern Methods

The AXI4DataSequence also provides methods for generating common data patterns:

```python
# Add incrementing data
w_sequence.add_incrementing_data(
    count=10,
    start_value=0,
    increment=1,
    id_value=None,
    all_last=False               # If True, all beats have last=1
)

# Add specific pattern
w_sequence.add_pattern_data(
    patterns=[0xA5A5A5A5, 0x5A5A5A5A],
    repeat=2,                    # Repeat count
    id_value=None,
    all_last=False
)

# Add walking ones pattern
w_sequence.add_walking_ones(
    count=32,                    # Bit positions to walk through
    id_value=None
)

# Add walking zeros pattern
w_sequence.add_walking_zeros(
    count=32,
    id_value=None
)

# Add alternating patterns
w_sequence.add_alternating_patterns(
    id_value=None
)

# Add random data
w_sequence.add_random_data(
    count=10,
    id_value=None,
    all_last=False
)
```

## AXI4ResponseSequence

For more detailed control of response generation, use `AXI4ResponseSequence`.

### Creating a Response Sequence

```python
from axi4_seq_response import AXI4ResponseSequence

# Create a write response sequence
b_sequence = AXI4ResponseSequence(
    name="b_sequence",           # Sequence name
    channel="B",                 # Channel: "B" or "R"
    id_width=8,                  # ID width in bits
    user_width=1,                # User signal width in bits
    randomization_config=None    # Optional randomization configuration
)

# Create a read response sequence
r_sequence = AXI4ResponseSequence(
    name="r_sequence",
    channel="R",
    id_width=8,
    user_width=1
)
```

### Adding Response Transactions

```python
# Add a write response transaction
b_sequence.add_transaction(
    id_value=0,                  # Transaction ID
    resp=0,                      # Response code: 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR
    user=0                       # User signal
)

# Add a read response transaction
r_sequence.add_transaction(
    id_value=0,                  # Transaction ID
    resp=0,                      # Response code
    user=0,                      # User signal
    data=0xDEADBEEF,             # Data value (R channel only)
    last=1                       # Last indicator (R channel only)
)
```

### Adding Burst Responses

```python
# Add a complete read burst response
r_sequence.add_burst_response(
    id_value=0,
    burst_len=3,                 # 4 beats
    data_values=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    resp=0,                      # Response code for all beats
    user=0                       # User signal for all beats
)
```

### Response Ordering Control

```python
# Set in-order responses (default)
r_sequence.set_order_mode(inorder=True)

# Set out-of-order responses with strategy
r_sequence.set_order_mode(
    inorder=False,
    ooo_strategy='random'        # 'random', 'round_robin', or 'weighted'
)

# For weighted strategy, set weights
r_sequence.set_ooo_weight(
    id_value=0,
    weight=1.0                   # Default weight
)
r_sequence.set_ooo_weight(
    id_value=1,
    weight=2.0                   # Higher priority
)
```

### Factory Methods

The AXI4ResponseSequence class provides factory methods for common patterns:

```python
# Create write responses for a list of transaction IDs
write_responses = AXI4ResponseSequence.create_write_responses(
    id_values=[0, 1, 2, 3],
    resp_values=[0, 0, 0, 0],    # All OKAY
    id_width=8
)

# Create read responses with data
read_responses = AXI4ResponseSequence.create_read_responses(
    id_values=[0, 1],
    data_values=[                # List of data bursts
        [0x11111111, 0x12121212],
        [0x22222222, 0x23232323, 0x24242424]
    ],
    resp_values=[0, 0],          # All OKAY
    id_width=8
)

# Create error responses
error_responses = AXI4ResponseSequence.create_error_responses(
    id_values=[0, 1, 2],
    error_type='slverr',         # 'slverr' or 'decerr'
    channel="B",
    id_width=8
)

# Create exclusive access responses
exclusive_responses = AXI4ResponseSequence.create_exclusive_responses(
    id_values=[0, 1],
    id_width=8
)

# Create mixed response types
mixed_responses = AXI4ResponseSequence.create_mixed_responses(
    id_width=8
)

# Create pair of in-order and out-of-order sequences
inorder_seq, outoforder_seq = AXI4ResponseSequence.create_ordered_vs_unordered(
    id_width=8
)
```

## AXI4ProtocolSequence

The `AXI4ProtocolSequence` is a high-level sequence generator for testing protocol-specific features.

### Creating a Protocol Sequence

```python
from axi4_seq_protocol import AXI4ProtocolSequence

# Create a protocol sequence
sequence = AXI4ProtocolSequence(
    name="protocol_test",        # Sequence name
    id_width=8,                  # ID width in bits
    addr_width=32,               # Address width in bits
    data_width=32,               # Data width in bits
    user_width=1,                # User signal width in bits
    randomization_config=None    # Optional randomization configuration
)
```

### Adding Specialized Test Sequences

```python
# Add error response test sequence
sequence.create_slverr_response_sequence()
sequence.create_decerr_response_sequence()
sequence.create_exokay_response_sequence()

# Add boundary condition test sequence
sequence.create_4k_boundary_sequence()
sequence.create_unaligned_address_sequence()
sequence.create_max_burst_sequence()

# Add protocol compliance test sequence
sequence.create_burst_type_sequence()
sequence.create_protection_sequence()
sequence.create_exclusive_sequence()

# Add performance test sequence
sequence.create_throughput_sequence()
sequence.create_interleaved_sequence()
sequence.create_quality_of_service_sequence()
```

### Creating a Full Test Suite

```python
# Create a comprehensive protocol test suite
test_suite = AXI4ProtocolSequence.create_protocol_test_suite(
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1
)

# Create a simplified protocol test
basic_test = AXI4ProtocolSequence.create_basic_protocol_test(
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1
)
```

### Tracking Protocol Violations

```python
# Register a protocol violation
sequence.register_protocol_violation(
    id_value=0,                  # Transaction ID
    is_read=False,               # Write transaction
    message="Address not aligned for burst size"
)

# Check for violations
has_violations = sequence.has_protocol_violations(
    id_value=0,
    is_read=False
)

# Get violation messages
violations = sequence.get_protocol_violations(
    id_value=0,
    is_read=False
)
```

## Transaction Sequence Factory Methods

The AXI4TransactionSequence class provides factory methods for common patterns:

```python
# Create simple write transactions
write_sequence = AXI4TransactionSequence.create_simple_writes(
    addrs=[0x1000, 0x2000, 0x3000],
    data_values=[
        [0x11111111],
        [0x22222222, 0x22222223],
        [0x33333333, 0x33333334, 0x33333335]
    ],
    id_values=[0, 1, 2],
    data_width=32
)

# Create simple read transactions
read_sequence = AXI4TransactionSequence.create_simple_reads(
    addrs=[0x1000, 0x2000, 0x3000],
    burst_lens=[0, 1, 2],        # 1, 2, 3 beats
    id_values=[0, 1, 2],
    data_width=32
)

# Create incrementing write transactions
incr_write = AXI4TransactionSequence.create_incrementing_writes(
    start_addr=0x1000,
    count=10,
    data_width=32
)

# Create read-after-write pattern
raw_sequence = AXI4TransactionSequence.create_read_after_write(
    addrs=[0x1000, 0x2000, 0x3000],
    data_values=[
        [0x11111111],
        [0x22222222, 0x22222223],
        [0x33333333, 0x33333334, 0x33333335]
    ],
    data_width=32
)

# Create burst variations test
burst_test = AXI4TransactionSequence.create_burst_variations(
    start_addr=0x1000,
    data_width=32
)

# Create exclusive access test
exclusive_test = AXI4TransactionSequence.create_exclusive_access_test(
    addrs=[0x1000, 0x2000, 0x3000],
    data_values=[0xA1A1A1A1, 0xB2B2B2B2, 0xC3C3C3C3],
    data_width=32
)

# Create comprehensive protocol stress test
stress_test = AXI4TransactionSequence.create_protocol_stress_test(
    data_width=32
)
```

## Using Random Generation

All sequence types support randomization using the `RandomizationConfig` class:

```python
from CocoTBFramework.components.randomization_config import RandomizationConfig, RandomizationMode

# Create a randomization configuration
config = RandomizationConfig(protocol_name="AXI4")

# Configure address randomization
config.configure_field(
    field_name="aw_addr",
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0x1000, 0x1FFF), (0x2000, 0x2FFF)],
        "weights": [0.7, 0.3]
    }
)

# Configure ID randomization
config.configure_field(
    field_name="aw_id",
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0, 3), (4, 7)],
        "weights": [0.8, 0.2]
    }
)

# Use the configuration with a sequence
sequence = AXI4TransactionSequence(
    name="random_sequence",
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    randomization_config=config
)
```

### Specialized AXI4 Randomization

For