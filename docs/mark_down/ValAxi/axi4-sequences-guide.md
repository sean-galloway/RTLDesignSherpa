# Comprehensive Guide to AXI4 Sequences

## Table of Contents

1. [Introduction to AXI4 Sequences](#introduction-to-axi4-sequences)
2. [Sequence Hierarchy](#sequence-hierarchy)
3. [Basic Sequence Usage](#basic-sequence-usage)
4. [Command Handler Integration](#command-handler-integration)
5. [Concrete Integration Examples](#concrete-integration-examples)
6. [Error Handling and Debugging](#error-handling-and-debugging)
7. [Custom Sequence Extensions](#custom-sequence-extensions)
8. [Data Width Considerations](#data-width-considerations)
9. [Sequence Composition](#sequence-composition)
10. [Performance Optimization](#performance-optimization)
11. [Randomization Strategies](#randomization-strategies)
12. [Sequence Visualization](#sequence-visualization)
13. [Advanced Test Patterns](#advanced-test-patterns)
14. [Best Practices](#best-practices)

## Introduction to AXI4 Sequences

AXI4 Sequences provide a powerful framework for generating structured and reusable transactions for AXI4 verification. They allow you to create complex test scenarios while maintaining a high level of abstraction and reusability.

Sequences in the AXI4 verification environment serve several key purposes:

- **Protocol Compliance Testing**: Generate transactions that test various aspects of the AXI4 protocol
- **Test Pattern Generation**: Create common test patterns like read-after-write, burst variations, etc.
- **Randomization**: Support constrained random testing for better coverage
- **Reusability**: Build complex tests from reusable sequence components
- **Architecture Exploration**: Test different configurations of AXI4 interfaces

## Sequence Hierarchy

The AXI4 sequence architecture follows a hierarchical structure:

```
AXI4BaseSequence
├── AXI4AddressSequence (AW/AR channel)
├── AXI4DataSequence (W/R channel)
├── AXI4ResponseSequence (B/R channel)
└── AXI4TransactionSequence (Coordinates Address and Data)
    └── AXI4ProtocolSequence (Specialized Protocol Tests)
```

- **AXI4BaseSequence**: Base class with common utilities for randomization, memory management, and protocol-specific operations
- **AXI4AddressSequence**: Generates AW/AR channel transactions with proper burst configuration and address alignment
- **AXI4DataSequence**: Generates W/R channel transactions with data patterns and strobe handling
- **AXI4ResponseSequence**: Generates B/R channel responses with response ordering and error injection
- **AXI4TransactionSequence**: Coordinates address and data sequences into complete transactions with dependency management
- **AXI4ProtocolSequence**: Creates specialized protocol test scenarios focusing on compliance and edge cases

## Basic Sequence Usage

### Creating a Transaction Sequence

```python
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence

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
    burst_size=2,                # Size: 0=byte, 1=halfword, 2=word, 3=doubleword
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

For verification, you can add expected responses:

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

### Using Factory Methods

The sequence classes provide factory methods for common transaction patterns:

```python
# Create a read-after-write sequence
raw_sequence = AXI4TransactionSequence.create_read_after_write(
    addrs=[0x1000, 0x2000, 0x3000],
    data_values=[
        [0x11111111],
        [0x22222222, 0x22222223],
        [0x33333333, 0x33333334, 0x33333335]
    ],
    data_width=32
)

# Create a burst variations test
burst_test = AXI4TransactionSequence.create_burst_variations(
    start_addr=0x1000,
    data_width=32
)

# Create a protocol stress test
stress_test = AXI4TransactionSequence.create_protocol_stress_test(
    data_width=32
)
```

## Command Handler Integration

The AXI4CommandHandler is the key component that executes transaction sequences on the AXI4 interface. It coordinates the activity across all channels and manages the transaction flow.

### Creating a Command Handler

```python
from CocoTBFramework.components.axi4.axi4_command_handler import AXI4CommandHandler

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
```

### Processing Transactions

```python
# Process a transaction sequence
sequence = AXI4TransactionSequence.create_protocol_stress_test(data_width=32)
complete_event = await cmd_handler.process_transaction_sequence(sequence)

# Wait for completion
await complete_event.wait()

# Get statistics
stats = cmd_handler.get_stats()
print(f"Write transactions: {stats['write_transactions']}")
print(f"Read transactions: {stats['read_transactions']}")

# Stop the handler
await cmd_handler.stop()
```

## Concrete Integration Examples

This section provides complete examples of integrating sequences with the AXI4 command handler in a testbench.

### Basic Testbench Setup

```python
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Timer

from CocoTBFramework.components.axi4.axi4_factory import create_axi4_master, create_axi4_slave
from CocoTBFramework.components.axi4.axi4_factory import create_axi4_monitor, create_axi4_memory_scoreboard
from CocoTBFramework.components.axi4.axi4_command_handler import AXI4CommandHandler
from CocoTBFramework.components.axi4.axi4_seq_transaction import AXI4TransactionSequence
from CocoTBFramework.components.memory_models import SimpleMemoryModel

@cocotb.test()
async def test_axi4_read_after_write(dut):
    """Test AXI4 read-after-write sequence with command handler."""
    
    # Create clock
    clock = Clock(dut.clk, 10, units="ns")
    cocotb.start_soon(clock.start())
    
    # Reset DUT
    dut.rst_n.value = 0
    await Timer(100, units="ns")
    dut.rst_n.value = 1
    await Timer(100, units="ns")
    
    # Create memory model
    memory = SimpleMemoryModel(size=0x10000, byte_width=4)
    
    # Create AXI4 components
    master = create_axi4_master(
        dut=dut,
        title="master",
        prefix="m_axi",
        divider="_",
        suffix="",
        clock=dut.clk,
        channels=["AW", "W", "B", "AR", "R"],
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1
    )
    
    slave = create_axi4_slave(
        dut=dut,
        title="slave",
        prefix="s_axi",
        divider="_",
        suffix="",
        clock=dut.clk,
        channels=["AW", "W", "B", "AR", "R"],
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1,
        memory_model=memory
    )
    
    monitor = create_axi4_monitor(
        dut=dut,
        title="monitor",
        prefix="m_axi",
        divider="_",
        suffix="",
        clock=dut.clk,
        channels=["AW", "W", "B", "AR", "R"],
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1
    )
    
    scoreboard = create_axi4_memory_scoreboard(
        name="scoreboard",
        memory_model=memory,
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1
    )
    
    # Connect monitor to scoreboard
    monitor.set_write_callback(scoreboard.check_write)
    monitor.set_read_callback(scoreboard.check_read)
    
    # Create command handler
    cmd_handler = AXI4CommandHandler(
        aw_master=master.aw_master,
        w_master=master.w_master,
        b_slave=master.b_slave,
        ar_master=master.ar_master,
        r_slave=master.r_slave,
        memory_model=memory
    )
    
    # Start slave and command handler
    await slave.start_processor()
    await cmd_handler.start()
    
    # Create a read-after-write sequence
    sequence = AXI4TransactionSequence.create_read_after_write(
        addrs=[0x1000, 0x2000, 0x3000],
        data_values=[
            [0x11111111],
            [0x22222222, 0x22222223],
            [0x33333333, 0x33333334, 0x33333335]
        ],
        data_width=32
    )
    
    # Process the sequence
    complete_event = await cmd_handler.process_transaction_sequence(sequence)
    
    # Wait for completion
    await complete_event.wait()
    
    # Wait for any pending transactions to complete
    for _ in range(100):
        await RisingEdge(dut.clk)
    
    # Check results
    stats = cmd_handler.get_stats()
    print(f"Completed transactions: {stats['completed_transactions']}")
    
    errors = scoreboard.get_error_count()
    if errors > 0:
        print(f"Errors detected: {errors}")
        for error in scoreboard.get_errors():
            print(f"  {error}")
    else:
        print("No errors detected")
    
    # Stop components
    await cmd_handler.stop()
    await slave.stop_processor()
```

### Protocol Stress Test Example

```python
@cocotb.test()
async def test_axi4_protocol_stress(dut):
    """Test AXI4 protocol stress with various transaction types."""
    
    # [Setup code for clock, reset, and components as in previous example]
    
    # Create a protocol stress test sequence
    stress_sequence = AXI4TransactionSequence.create_protocol_stress_test(data_width=32)
    
    # Process the sequence
    complete_event = await cmd_handler.process_transaction_sequence(stress_sequence)
    
    # Wait for completion with timeout handling
    try:
        await cocotb.triggers.with_timeout(complete_event.wait(), 10000, units="ns")
        print("Sequence completed successfully")
    except cocotb.triggers.TimeoutError:
        print("Sequence timed out!")
        # List pending transactions
        pending_writes = stress_sequence.get_pending_transactions(is_read=False)
        pending_reads = stress_sequence.get_pending_transactions(is_read=True)
        print(f"Pending writes: {pending_writes}")
        print(f"Pending reads: {pending_reads}")
    
    # Check results
    errors = scoreboard.get_error_count()
    if errors > 0:
        print(f"Errors detected: {errors}")
        for error in scoreboard.get_errors():
            print(f"  {error}")
    else:
        print("No errors detected")
```

### Multiple Sequence Execution

```python
@cocotb.test()
async def test_axi4_multiple_sequences(dut):
    """Test executing multiple AXI4 sequences in sequence."""
    
    # [Setup code for clock, reset, and components as in previous example]
    
    # Create sequences
    sequences = [
        AXI4TransactionSequence.create_simple_writes(
            addrs=[0x1000, 0x2000, 0x3000],
            data_values=[[0xA1A1A1A1], [0xB2B2B2B2], [0xC3C3C3C3]],
            data_width=32
        ),
        AXI4TransactionSequence.create_simple_reads(
            addrs=[0x1000, 0x2000, 0x3000],
            burst_lens=[0, 0, 0],
            data_width=32
        ),
        AXI4TransactionSequence.create_burst_variations(
            start_addr=0x4000,
            data_width=32
        )
    ]
    
    # Process each sequence
    for i, sequence in enumerate(sequences):
        print(f"Executing sequence {i+1}/{len(sequences)}: {sequence.name}")
        complete_event = await cmd_handler.process_transaction_sequence(sequence)
        
        # Wait for completion
        await complete_event.wait()
        
        # Wait for any pending transactions to complete
        for _ in range(20):
            await RisingEdge(dut.clk)
```

## Error Handling and Debugging

When working with AXI4 sequences, several types of errors might occur. This section covers common issues and how to debug them.

### Common Error Types

1. **Protocol Violations**: Errors related to AXI4 protocol rules
2. **Sequence Generation Errors**: Issues with creating valid sequences
3. **Transaction Execution Errors**: Problems during transaction execution
4. **Response Timeout Errors**: Transactions that don't receive responses
5. **Data Mismatch Errors**: Actual data doesn't match expected data

### Enabling Verbose Logging

The first step in debugging is to enable detailed logging:

```python
import logging

# Create a logger
logger = logging.getLogger("axi4_test")
logger.setLevel(logging.DEBUG)

# Add console handler
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.DEBUG)
console_handler.setFormatter(logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s'))
logger.addHandler(console_handler)

# Use logger when creating components
master = create_axi4_master(..., log=logger)
slave = create_axi4_slave(..., log=logger)
cmd_handler = AXI4CommandHandler(..., log=logger)
```

### Protocol Validation

AXI4 sequences provide built-in protocol validation that can identify issues before execution:

```python
# Validate a transaction sequence
def validate_sequence(sequence):
    """Validate all transactions in a sequence for protocol compliance."""
    errors = []
    
    # Check write transactions
    for write_id in sequence.get_write_ids():
        # Get the AW packet
        aw_packet = sequence.get_write_addr_packet(write_id)
        if aw_packet:
            # Validate protocol rules
            valid, message = aw_packet.validate_axi4_protocol()
            if not valid:
                errors.append(f"Write ID {write_id}: {message}")
    
    # Check read transactions
    for read_id in sequence.get_read_ids():
        # Get the AR packet
        ar_packet = sequence.get_read_addr_packet(read_id)
        if ar_packet:
            # Validate protocol rules
            valid, message = ar_packet.validate_axi4_protocol()
            if not valid:
                errors.append(f"Read ID {read_id}: {message}")
    
    return errors

# Usage
sequence = AXI4TransactionSequence.create_protocol_stress_test(data_width=32)
errors = validate_sequence(sequence)
if errors:
    print("Sequence validation errors:")
    for error in errors:
        print(f"  {error}")
else:
    print("Sequence validation passed")
```

### Tracking Transaction Dependencies

Dependency issues are a common source of errors. You can trace dependencies to identify blocked transactions:

```python
def trace_dependencies(sequence, id_value, is_read=False, indent=0):
    """Recursively trace dependencies for a transaction."""
    prefix = "  " * indent
    dependencies = sequence.get_dependencies(id_value, is_read)
    
    print(f"{prefix}{'Read' if is_read else 'Write'} ID {id_value} depends on:")
    
    if not dependencies:
        print(f"{prefix}  No dependencies")
        return
    
    for dep_id in dependencies:
        # Check if dependency is a read or write
        is_dep_read = dep_id in sequence.get_read_ids()
        print(f"{prefix}  {'Read' if is_dep_read else 'Write'} ID {dep_id}")
        
        # Recursively trace dependencies of this dependency
        trace_dependencies(sequence, dep_id, is_dep_read, indent + 2)

# Usage
# Find transactions that haven't completed
pending_writes = sequence.get_pending_transactions(is_read=False)
pending_reads = sequence.get_pending_transactions(is_read=True)

for write_id in pending_writes:
    print(f"Tracing dependencies for pending Write ID {write_id}:")
    trace_dependencies(sequence, write_id, is_read=False)

for read_id in pending_reads:
    print(f"Tracing dependencies for pending Read ID {read_id}:")
    trace_dependencies(sequence, read_id, is_read=True)
```

### Timeout Handling

Implement timeout handling to detect stalled transactions:

```python
async def execute_with_timeout(cmd_handler, sequence, timeout_ns=10000):
    """Execute a sequence with timeout handling."""
    # Start processing the sequence
    complete_event = await cmd_handler.process_transaction_sequence(sequence)
    
    # Wait for completion with timeout
    try:
        await cocotb.triggers.with_timeout(complete_event.wait(), timeout_ns, units="ns")
        print("Sequence completed successfully")
        return True
    except cocotb.triggers.TimeoutError:
        print(f"Sequence timed out after {timeout_ns} ns!")
        
        # List pending transactions
        pending_writes = sequence.get_pending_transactions(is_read=False)
        pending_reads = sequence.get_pending_transactions(is_read=True)
        
        if pending_writes:
            print(f"Pending writes: {pending_writes}")
            for write_id in pending_writes:
                print(f"  Write ID {write_id} dependencies:")
                for dep_id in sequence.get_dependencies(write_id, is_read=False):
                    print(f"    Depends on ID {dep_id}")
        
        if pending_reads:
            print(f"Pending reads: {pending_reads}")
            for read_id in pending_reads:
                print(f"  Read ID {read_id} dependencies:")
                for dep_id in sequence.get_dependencies(read_id, is_read=True):
                    print(f"    Depends on ID {dep_id}")
        
        return False
```

### Signal Dumping for Debugging

When debugging complex issues, dumping signals to a waveform file can be helpful:

```python
# At the beginning of your test
dut._log.setLevel(logging.DEBUG)
dut._log.info("Dumping VCD waveform to axi4_test.vcd")
dut.log_waveform = True  # Enable waveform dumping
```

## Custom Sequence Extensions

Sometimes standard sequences aren't enough for specific test needs. This section covers how to extend the base sequence classes for specialized testing.

### Creating a Custom Transaction Sequence

```python
class CustomTransactionSequence(AXI4TransactionSequence):
    """Custom transaction sequence with specialized patterns."""
    
    def __init__(self, name="custom_sequence", **kwargs):
        super().__init__(name=name, **kwargs)
    
    def add_stride_pattern(self, base_addr, stride, count, data_pattern=None):
        """Add transactions with strided addressing pattern."""
        write_ids = []
        
        for i in range(count):
            addr = base_addr + (i * stride)
            
            # Generate data if not provided
            if data_pattern is None:
                data = [0xA0000000 + i]
            else:
                data = [data_pattern | i]
            
            # Add write transaction
            write_id = self.add_write_transaction(
                addr=addr,
                data_values=data
            )
            write_ids.append(write_id)
            
            # Add corresponding read transaction
            read_id = self.add_read_transaction(
                addr=addr,
                dependencies=[write_id]
            )
            
            # Add expected response
            self.add_read_response_data(read_id, data)
        
        return write_ids
    
    def add_toggle_pattern(self, addr, count, start_value=0):
        """Add transactions with toggling bit patterns."""
        write_ids = []
        last_write_id = None
        
        for i in range(count):
            # Generate toggling bit pattern
            toggle_bit = 1 << (i % 32)
            data_value = start_value ^ toggle_bit
            
            # Add write transaction
            if last_write_id:
                write_id = self.add_write_transaction(
                    addr=addr,
                    data_values=[data_value],
                    dependencies=[last_write_id]
                )
            else:
                write_id = self.add_write_transaction(
                    addr=addr,
                    data_values=[data_value]
                )
            
            write_ids.append(write_id)
            last_write_id = write_id
            
            # Add read transaction
            read_id = self.add_read_transaction(
                addr=addr,
                dependencies=[write_id]
            )
            
            # Add expected response
            self.add_read_response_data(read_id, [data_value])
        
        return write_ids
    
    @classmethod
    def create_cache_coherency_test(cls, addresses, data_width=32):
        """Create a sequence that tests cache coherency patterns."""
        sequence = cls(name="cache_coherency_test", data_width=data_width)
        
        # Add initial writes to all addresses
        write_ids = []
        for i, addr in enumerate(addresses):
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=[0xA0000000 + i]
            )
            write_ids.append(write_id)
        
        # Add reads to all addresses
        read_ids = []
        for i, addr in enumerate(addresses):
            read_id = sequence.add_read_transaction(
                addr=addr,
                dependencies=[write_ids[i]]
            )
            sequence.add_read_response_data(read_id, [0xA0000000 + i])
            read_ids.append(read_id)
        
        # Add second set of writes to the same addresses
        write_ids2 = []
        for i, addr in enumerate(addresses):
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=[0xB0000000 + i],
                dependencies=[read_ids[i]]
            )
            write_ids2.append(write_id)
        
        # Add second set of reads to verify updated values
        for i, addr in enumerate(addresses):
            read_id = sequence.add_read_transaction(
                addr=addr,
                dependencies=[write_ids2[i]]
            )
            sequence.add_read_response_data(read_id, [0xB0000000 + i])
        
        return sequence
```

### Custom Address Patterns

```python
class CustomAddressSequence(AXI4AddressSequence):
    """Custom address sequence with specialized patterns."""
    
    def __init__(self, name="custom_addr_seq", **kwargs):
        super().__init__(name=name, **kwargs)
    
    def add_interleaved_pattern(self, base_addr, regions, region_size, burst_size=2):
        """Add interleaved addresses across multiple memory regions."""
        for i in range(regions):
            for offset in range(0, region_size, 1 << burst_size):
                addr = base_addr + (i * region_size) + offset
                self.add_transaction(
                    addr=addr,
                    id_value=i,
                    burst_size=burst_size,
                    burst_type=self.BURST_INCR
                )
        
        return self
    
    def add_scatter_gather_pattern(self, addresses, id_value=0, burst_size=2):
        """Add non-contiguous addresses in a scatter-gather pattern."""
        for i, addr in enumerate(addresses):
            self.add_transaction(
                addr=addr,
                id_value=id_value,
                burst_size=burst_size,
                burst_type=self.BURST_INCR
            )
        
        return self
    
    @classmethod
    def create_page_boundary_test(cls, page_size=4096, pages=4, data_width=32):
        """Create a test that specifically targets page boundary crossings."""
        sequence = cls(name="page_boundary_test", data_width=data_width)
        
        # Calculate bytes per beat
        bytes_per_beat = data_width // 8
        
        # Add transactions at page boundaries
        for page in range(pages):
            page_addr = page * page_size
            
            # Just before boundary
            sequence.add_transaction(
                addr=page_addr - bytes_per_beat,
                burst_len=1,  # 2 beats to cross boundary
                burst_size=(bytes_per_beat).bit_length() - 1,
                burst_type=cls.BURST_INCR
            )
            
            # At boundary
            sequence.add_transaction(
                addr=page_addr,
                burst_len=1,  # 2 beats
                burst_size=(bytes_per_beat).bit_length() - 1,
                burst_type=cls.BURST_INCR
            )
            
            # Straddling boundary with different burst sizes
            for size in range((bytes_per_beat).bit_length()):
                bytes_this_size = 1 << size
                if bytes_this_size < bytes_per_beat:
                    sequence.add_transaction(
                        addr=page_addr - bytes_this_size,
                        burst_len=1,  # 2 beats
                        burst_size=size,
                        burst_type=cls.BURST_INCR
                    )
        
        return sequence
```

### Custom Data Patterns

```python
class CustomDataSequence(AXI4DataSequence):
    """Custom data sequence with specialized patterns."""
    
    def __init__(self, name="custom_data_seq", **kwargs):
        super().__init__(name=name, **kwargs)
    
    def add_march_pattern(self, count=32):
        """Add March pattern (used in memory testing).
        
        March patterns are systematic sequences for testing memories.
        This implements a simple March C pattern.
        """
        # March C has several elements: 
        # ⬆(w0); ⬆(r0,w1); ⬆(r1,w0); ⬇(r0,w1); ⬇(r1,w0); ⬆(r0)
        
        # First element - write 0s
        for i in range(count):
            self.add_transaction(
                data=0,
                last=(i == count-1)
            )
        
        # More elements would follow in a real March test
        
        return self
    
    def add_galloping_pattern(self, base_value=0xAAAAAAAA, count=16):
        """Add Galloping pattern (tests address decoder and adjacent bit coupling)."""
        for i in range(count):
            # Galloping pattern: toggles one bit at a time
            data = base_value ^ (1 << i)
            self.add_transaction(
                data=data,
                last=(i == count-1)
            )
        
        return self
    
    @classmethod
    def create_memory_stress_pattern(cls, channel="W", data_width=32):
        """Create a data pattern designed to stress memory cells."""
        sequence = cls(name="memory_stress", channel=channel, data_width=data_width)
        
        # Add various stress patterns
        
        # Alternating 1s and 0s
        sequence.add_pattern_data([0x55555555, 0xAAAAAAAA], repeat=4)
        
        # Checkerboard
        sequence.add_pattern_data([0x33333333, 0xCCCCCCCC], repeat=4)
        
        # Solid fills
        sequence.add_pattern_data([0x00000000, 0xFFFFFFFF], repeat=4)
        
        # Walking 1s and 0s
        sequence.add_walking_ones()
        sequence.add_walking_zeros()
        
        return sequence
```

## Data Width Considerations

The data width of the AXI4 interface affects many aspects of sequence generation. This section explains how to properly scale your tests for different data widths.

### Impact of Data Width on Sequence Generation

1. **Memory Alignment**: Proper address alignment depends on data width
2. **Burst Size Calculation**: Maximum burst size is limited by data width
3. **Byte Enable (Strobe) Width**: Strobe width is data_width/8
4. **Address Increment**: The step size for INCR bursts depends on data width
5. **Boundary Calculations**: 4KB boundary checks must account for data width

### Alignment Requirements

```python
def calculate_alignment_requirement(data_width, burst_size):
    """Calculate alignment requirement based on data width and burst size."""
    bytes_per_beat = data_width // 8
    alignment = 1 << burst_size  # 2^burst_size
    
    # Ensure alignment doesn't exceed data width
    if alignment > bytes_per_beat:
        print(f"Warning: Burst size {burst_size} requires {alignment} byte alignment, "
              f"but data width {data_width} only supports up to {bytes_per_beat} byte alignment")
    
    return alignment

# Usage example
data_width = 64  # 64-bit data bus
for burst_size in range(5):  # 0 to 4 (1, 2, 4, 8, 16 bytes)
    alignment = calculate_alignment_requirement(data_width, burst_size)
    print(f"Burst size {burst_size} (2^{burst_size} bytes) requires {alignment} byte alignment")
```

### Burst Size Selection

```python
def get_max_burst_size(data_width):
    """Get maximum burst size for the given data width."""
    bytes_per_beat = data_width // 8
    return (bytes_per_beat).bit_length() - 1

# Usage example
for data_width in [32, 64, 128, 256, 512, 1024]:
    max_burst_size = get_max_burst_size(data_width)
    bytes_per_beat = data_width // 8
    print(f"Data width {data_width} (bytes: {bytes_per_beat}) supports burst sizes up to {max_burst_size} "
          f"(2^{max_burst_size} = {1<<max_burst_size} bytes)")
```

### Data Width Aware Sequence Factory

Creating a factory function that automatically adjusts for data width:

```python
def create_data_width_aware_sequence(data_width, sequence_type="boundary_test"):
    """Create a sequence that's properly configured for the given data width."""
    # Calculate derived parameters
    bytes_per_beat = data_width // 8
    max_burst_size = (bytes_per_beat).bit_length() - 1
    
    if sequence_type == "boundary_test":
        # Create a 4KB boundary test with proper burst sizes
        sequence = AXI4AddressSequence.create_4k_boundary_test(
            channel="AW",
            id_value=0,
            data_width=data_width  # Pass data width to factory method
        )
    
    elif sequence_type == "burst_test":
        # Create a burst test with appropriate sizes
        sequence = AXI4TransactionSequence.create_burst_variations(
            start_addr=0x1000,
            data_width=data_width  # Pass data width to factory method
        )
    
    elif sequence_type == "stress_test":
        # Create a protocol stress test
        sequence = AXI4TransactionSequence.create_protocol_stress_test(
            data_width=data_width  # Pass data width to factory method
        )
    
    else:
        raise ValueError(f"Unknown sequence type: {sequence_type}")
    
    return sequence

# Usage example
for data_width in [32, 64, 128]:
    sequence = create_data_width_aware_sequence(data_width, "boundary_test")
    print(f"Created sequence for data width {data_width}")
    # Use the sequence...
```

### Address Calculation for Different Data Widths

```python
def calculate_burst_addresses(start_addr, burst_len, burst_size, burst_type, data_width):
    """Calculate all addresses in a burst for a given data width."""
    # Ensure proper alignment
    bytes_per_beat = data_width // 8
    alignment = 1 << burst_size
    aligned_addr = (start_addr // alignment) * alignment
    
    # Calculate addresses based on burst type
    addresses = []
    
    if burst_type == 0:  # FIXED
        # Same address for all beats
        return [aligned_addr] * (burst_len + 1)
    
    elif burst_type == 1:  # INCR
        # Increment by size
        for i in range(burst_len + 1):
            addr = aligned_addr + (i * alignment)
            addresses.append(addr)
    
    elif burst_type == 2:  # WRAP
        # Wrap at boundaries determined by burst length and size
        beats = burst_len + 1
        
        # For WRAP, beats must be 2, 4, 8, or 16
        if not (beats & (beats - 1) == 0 and beats <= 16):
            raise ValueError(f"WRAP burst length+1 must be 2, 4, 8, or 16, got {beats}")
        
        # Calculate wrap boundary mask
        wrap_size = beats * alignment
        lower_bits = wrap_size - 1
        upper_bits = ~lower_bits & 0xFFFFFFFF
        
        # Calculate wrap boundary
        wrap_boundary = aligned_addr & upper_bits
        
        # Generate addresses
        for i in range(beats):
            offset = (aligned_addr + (i * alignment)) & lower_bits
            addr = wrap_boundary | offset
            addresses.append(addr)
    
    else:
        raise ValueError(f"Invalid burst type: {burst_type}")
    
    return addresses

# Example showing how addresses change with data width
start_addr = 0x1020
burst_len = 3  # 4 beats
burst_type = 1  # INCR

for data_width in [32, 64, 128]:
    bytes_per_beat = data_width // 8
    max_burst_size = (bytes_per_beat).bit_length() - 1
    
    print(f"\nData width: {data_width} bits ({bytes_per_beat} bytes/beat)")
    
    for burst_size in range(max_burst_size + 1):
        size_bytes = 1 << burst_size
        addresses = calculate_burst_addresses(start_addr, burst_len, burst_size, burst_type, data_width)
        
        print(f"  Burst size {burst_size} ({size_bytes} bytes):")
        print(f"    Addresses: {[hex(addr) for addr in addresses]}")
```

## Sequence Composition

Complex test scenarios often require composing multiple sequences. This section explains different approaches to sequence composition.

### Sequential Composition

Executing sequences one after another:

```python
async def execute_sequences_sequentially(cmd_handler, sequences):
    """Execute a list of sequences sequentially."""
    results = []
    
    for i, sequence in enumerate(sequences):
        print(f"Executing sequence {i+1}/{len(sequences)}: {sequence.name}")
        
        # Process the sequence
        complete_event = await cmd_handler.process_transaction_sequence(sequence)
        
        # Wait for completion
        await complete_event.wait()
        
        # Get statistics
        stats = cmd_handler.get_stats()
        results.append({
            "sequence": sequence.name,
            "completed": stats.get("completed_transactions", 0),
            "errors": stats.get("error_count", 0)
        })
    
    return results

# Usage
sequences = [
    AXI4TransactionSequence.create_simple_writes(...),
    AXI4TransactionSequence.create_burst_variations(...),
    AXI4TransactionSequence.create_protocol_stress_test(...)
]

results = await execute_sequences_sequentially(cmd_handler, sequences)
```

### Dependency-Based Composition

Creating dependencies between sequences:

```python
def compose_sequences_with_dependencies(sequences):
    """Compose multiple sequences with dependencies between them."""
    if not sequences:
        return None
    
    # Create a new composite sequence
    composite = AXI4TransactionSequence(
        name="composite_sequence",
        id_width=sequences[0].id_width,
        addr_width=sequences[0].addr_width,
        data_width=sequences[0].data_width,
        user_width=sequences[0].user_width
    )
    
    # Track the last transaction IDs from each sequence
    last_write_ids = []
    last_read_ids = []
    
    for i, sequence in enumerate(sequences):
        # Collect all transactions from this sequence
        write_ids = sequence.get_write_ids()
        read_ids = sequence.get_read_ids()
        
        # Create dependencies for this sequence based on previous sequences
        write_dependencies = last_write_ids + last_read_ids if i > 0 else None
        
        # Add write transactions
        for write_id in write_ids:
            # Get original transaction details
            aw_packet = sequence.get_write_addr_packet(write_id)
            w_packets = sequence.get_write_data_packets(write_id)
            
            if not aw_packet or not w_packets:
                continue
            
            # Extract parameters from original packet
            addr = aw_packet.awaddr
            data_values = [packet.wdata for packet in w_packets]
            strb_values = [packet.wstrb for packet in w_packets]
            
            # Add to composite sequence with dependencies
            new_write_id = composite.add_write_transaction(
                addr=addr,
                data_values=data_values,
                strb_values=strb_values,
                burst_len=aw_packet.awlen,
                burst_size=aw_packet.awsize,
                burst_type=aw_packet.awburst,
                lock=aw_packet.awlock,
                cache=aw_packet.awcache,
                prot=aw_packet.awprot,
                qos=aw_packet.awqos,
                dependencies=write_dependencies
            )
            
            # Get expected response if available
            b_packet = sequence.get_write_response_packet(write_id)
            if b_packet:
                composite.add_write_response(
                    id_value=new_write_id,
                    resp=b_packet.bresp,
                    user=b_packet.buser
                )
        
        # Add read transactions (with dependency on all writes)
        read_dependencies = write_dependencies + [new_write_id] if new_write_id is not None else write_dependencies
        
        for read_id in read_ids:
            # Get original transaction details
            ar_packet = sequence.get_read_addr_packet(read_id)
            r_packets = sequence.get_read_response_packets(read_id)
            
            if not ar_packet:
                continue
            
            # Extract parameters from original packet
            addr = ar_packet.araddr
            
            # Add to composite sequence with dependencies
            new_read_id = composite.add_read_transaction(
                addr=addr,
                burst_len=ar_packet.arlen,
                burst_size=ar_packet.arsize,
                burst_type=ar_packet.arburst,
                lock=ar_packet.arlock,
                cache=ar_packet.arcache,
                prot=ar_packet.arprot,
                qos=ar_packet.arqos,
                dependencies=read_dependencies
            )
            
            # Add expected response data
            if r_packets:
                data_values = [packet.rdata for packet in r_packets]
                resp_values = [packet.rresp for packet in r_packets]
                user_values = [packet.ruser for packet in r_packets]
                
                composite.add_read_response_data(
                    id_value=new_read_id,
                    data_values=data_values,
                    resp_values=resp_values,
                    user=user_values[0] if user_values else 0
                )
        
        # Update last IDs for next sequence
        if new_write_id is not None:
            last_write_ids = [new_write_id]
        if new_read_id is not None:
            last_read_ids = [new_read_id]
    
    return composite

# Usage
sequence1 = AXI4TransactionSequence.create_simple_writes(...)
sequence2 = AXI4TransactionSequence.create_simple_reads(...)
sequence3 = AXI4TransactionSequence.create_burst_variations(...)

composite = compose_sequences_with_dependencies([sequence1, sequence2, sequence3])
```

### Merging Sequences

Merging multiple sequences into one:

```python
def merge_sequences(sequences):
    """Merge multiple sequences into a single sequence, preserving original dependencies."""
    if not sequences:
        return None
    
    # Create a new merged sequence
    merged = AXI4TransactionSequence(
        name="merged_sequence",
        id_width=sequences[0].id_width,
        addr_width=sequences[0].addr_width,
        data_width=sequences[0].data_width,
        user_width=sequences[0].user_width
    )
    
    # Map from original IDs to new IDs
    id_mapping = {}
    
    for sequence in sequences:
        # Add write transactions
        for write_id in sequence.get_write_ids():
            # Get original transaction details
            aw_packet = sequence.get_write_addr_packet(write_id)
            w_packets = sequence.get_write_data_packets(write_id)
            
            if not aw_packet or not w_packets:
                continue
            
            # Map dependencies to new IDs
            original_deps = sequence.get_dependencies(write_id, is_read=False)
            mapped_deps = [id_mapping.get((dep, False), dep) for dep in original_deps]
            
            # Extract parameters from original packet
            addr = aw_packet.awaddr
            data_values = [packet.wdata for packet in w_packets]
            strb_values = [packet.wstrb for packet in w_packets]
            
            # Add to merged sequence
            new_write_id = merged.add_write_transaction(
                addr=addr,
                data_values=data_values,
                strb_values=strb_values,
                burst_len=aw_packet.awlen,
                burst_size=aw_packet.awsize,
                burst_type=aw_packet.awburst,
                lock=aw_packet.awlock,
                cache=aw_packet.awcache,
                prot=aw_packet.awprot,
                qos=aw_packet.awqos,
                dependencies=mapped_deps
            )
            
            # Store ID mapping
            id_mapping[(write_id, False)] = new_write_id
            
            # Get expected response if available
            b_packet = sequence.get_write_response_packet(write_id)
            if b_packet:
                merged.add_write_response(
                    id_value=new_write_id,
                    resp=b_packet.bresp,
                    user=b_packet.buser
                )
        
        # Add read transactions
        for read_id in sequence.get_read_ids():
            # Get original transaction details
            ar_packet = sequence.get_read_addr_packet(read_id)
            r_packets = sequence.get_read_response_packets(read_id)
            
            if not ar_packet:
                continue
            
            # Map dependencies to new IDs
            original_deps = sequence.get_dependencies(read_id, is_read=True)
            mapped_deps = [id_mapping.get((dep, is_read), dep) 
                          for dep, is_read in [(d, d in sequence.get_read_ids()) 
                                              for d in original_deps]]
            
            # Extract parameters from original packet
            addr = ar_packet.araddr
            
            # Add to merged sequence
            new_read_id = merged.add_read_transaction(
                addr=addr,
                burst_len=ar_packet.arlen,
                burst_size=ar_packet.arsize,
                burst_type=ar_packet.arburst,
                lock=ar_packet.arlock,
                cache=ar_packet.arcache,
                prot=ar_packet.arprot,
                qos=ar_packet.arqos,
                dependencies=mapped_deps
            )
            
            # Store ID mapping
            id_mapping[(read_id, True)] = new_read_id
            
            # Add expected response data
            if r_packets:
                data_values = [packet.rdata for packet in r_packets]
                resp_values = [packet.rresp for packet in r_packets]
                user_values = [packet.ruser for packet in r_packets]
                
                merged.add_read_response_data(
                    id_value=new_read_id,
                    data_values=data_values,
                    resp_values=resp_values,
                    user=user_values[0] if user_values else 0
                )
    
    return merged
```

## Performance Optimization

For large test scenarios, performance becomes important. This section covers techniques to optimize sequence generation and execution.

### Memory Usage Optimization

Reducing memory footprint:

```python
def optimize_sequence_memory(sequence):
    """Optimize a sequence to reduce memory usage."""
    # 1. Clean up completed transactions
    for write_id in sequence.get_write_ids():
        if not sequence.get_dependencies(write_id, is_read=False):
            # This transaction has no dependencies
            sequence.cleanup_transaction(write_id, is_read=False)
    
    for read_id in sequence.get_read_ids():
        if not sequence.get_dependencies(read_id, is_read=True):
            # This transaction has no dependencies
            sequence.cleanup_transaction(read_id, is_read=True)
    
    # 2. Run garbage collection
    import gc
    gc.collect()
    
    return sequence

# Add cleanup method to AXI4TransactionSequence
def cleanup_transaction(self, id_value, is_read=False):
    """Clean up a transaction's resources to reduce memory usage."""
    if is_read:
        if id_value in self.read_addr_packets:
            del self.read_addr_packets[id_value]
        if id_value in self.read_responses:
            del self.read_responses[id_value]
    else:
        if id_value in self.write_addr_packets:
            del self.write_addr_packets[id_value]
        if id_value in self.write_data_packets:
            del self.write_data_packets[id_value]
        if id_value in self.write_responses:
            del self.write_responses[id_value]

# Add the method to the class
AXI4TransactionSequence.cleanup_transaction = cleanup_transaction
```

### Batched Transaction Generation

Generating transactions in batches:

```python
def generate_batched_transactions(batch_size=100, total_count=1000):
    """Generate transactions in batches to improve performance."""
    sequence = AXI4TransactionSequence(name="batched_sequence")
    
    # Generate in batches
    for batch_start in range(0, total_count, batch_size):
        batch_end = min(batch_start + batch_size, total_count)
        print(f"Generating batch {batch_start} to {batch_end}")
        
        # Generate this batch
        for i in range(batch_start, batch_end):
            addr = 0x1000 + (i * 4)
            data = [0xA0000000 + i]
            
            sequence.add_write_transaction(
                addr=addr,
                data_values=data
            )
        
        # Run garbage collection after each batch
        import gc
        gc.collect()
    
    return sequence
```

### Optimizing Command Handler Execution

Improving command handler performance:

```python
async def optimized_transaction_execution(cmd_handler, sequence, batch_size=50):
    """Execute a large sequence optimally by processing in batches."""
    # Get all transaction IDs
    all_write_ids = sequence.get_write_ids()
    all_read_ids = sequence.get_read_ids()
    
    # Track which transactions have been executed
    executed_writes = set()
    executed_reads = set()
    
    # Process in batches until all transactions are complete
    while len(executed_writes) < len(all_write_ids) or len(executed_reads) < len(all_read_ids):
        # Create a batch sequence
        batch = AXI4TransactionSequence(
            name="batch_sequence",
            id_width=sequence.id_width,
            addr_width=sequence.addr_width,
            data_width=sequence.data_width,
            user_width=sequence.user_width
        )
        
        # Add ready write transactions to batch
        added_writes = 0
        for write_id in all_write_ids:
            if write_id in executed_writes:
                continue
                
            # Check if all dependencies are satisfied
            deps = sequence.get_dependencies(write_id, is_read=False)
            if all(dep in executed_writes for dep in deps):
                # All dependencies are satisfied
                aw_packet = sequence.get_write_addr_packet(write_id)
                w_packets = sequence.get_write_data_packets(write_id)
                
                if aw_packet and w_packets:
                    # Add to batch sequence
                    batch.add_write_transaction(
                        addr=aw_packet.awaddr,
                        data_values=[p.wdata for p in w_packets],
                        burst_len=aw_packet.awlen,
                        burst_size=aw_packet.awsize,
                        burst_type=aw_packet.awburst
                    )
                    
                    # Mark as executed
                    executed_writes.add(write_id)
                    added_writes += 1
                    
                    if added_writes >= batch_size:
                        break
        
        # Add ready read transactions to batch
        added_reads = 0
        for read_id in all_read_ids:
            if read_id in executed_reads:
                continue
                
            # Check if all dependencies are satisfied
            deps = sequence.get_dependencies(read_id, is_read=True)
            if all(dep in executed_writes if dep in all_write_ids else dep in executed_reads for dep in deps):
                # All dependencies are satisfied
                ar_packet = sequence.get_read_addr_packet(read_id)
                
                if ar_packet:
                    # Add to batch sequence
                    batch.add_read_transaction(
                        addr=ar_packet.araddr,
                        burst_len=ar_packet.arlen,
                        burst_size=ar_packet.arsize,
                        burst_type=ar_packet.arburst
                    )
                    
                    # Mark as executed
                    executed_reads.add(read_id)
                    added_reads += 1
                    
                    if added_reads >= batch_size:
                        break
        
        if added_writes > 0 or added_reads > 0:
            # Process the batch
            complete_event = await cmd_handler.process_transaction_sequence(batch)
            await complete_event.wait()
            
            print(f"Processed batch: {added_writes} writes, {added_reads} reads")
        else:
            # No transactions ready - possible dependency cycle
            print("Warning: No ready transactions found. Possible dependency cycle.")
            print(f"Remaining writes: {len(all_write_ids) - len(executed_writes)}")
            print(f"Remaining reads: {len(all_read_ids) - len(executed_reads)}")
            break
    
    print(f"Execution complete: {len(executed_writes)} writes, {len(executed_reads)} reads")
```

### Parallel Channel Processing

Improving throughput with parallel channel processing:

```python
def configure_handler_for_performance(cmd_handler):
    """Configure the command handler for maximum performance."""
    # Increase queue depths
    cmd_handler.aw_master.set_queue_depth(64)
    cmd_handler.w_master.set_queue_depth(64)
    cmd_handler.ar_master.set_queue_depth(64)
    
    # Set parallel processing options
    cmd_handler.set_max_outstanding_writes(32)
    cmd_handler.set_max_outstanding_reads(32)
    
    # Enable interleaving of reads and writes
    cmd_handler.set_interleave_reads_and_writes(True)
    
    # Set channel priorities
    cmd_handler.set_channel_priority("AW", 3)  # Highest
    cmd_handler.set_channel_priority("AR", 2)
    cmd_handler.set_channel_priority("W", 1)
    cmd_handler.set_channel_priority("B", 0)  # Lowest
    cmd_handler.set_channel_priority("R", 0)
    
    return cmd_handler
```

## Randomization Strategies

Effective randomization improves test coverage. This section covers strategies for creating effective randomized sequences.

### Configuring Randomization

```python
from CocoTBFramework.components.randomization_config import (
    RandomizationConfig, RandomizationMode, AXI4RandomizationConfig
)

# Create a randomization configuration
config = AXI4RandomizationConfig()

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

# Configure burst length
config.configure_field(
    field_name="aw_len",
    mode=RandomizationMode.CONSTRAINED,
    constraints={
        "bins": [(0, 0), (1, 3), (7, 15)],  # Single, small, and large bursts
        "weights": [0.5, 0.3, 0.2]
    }
)

# Configure burst type
config.configure_field(
    field_name="aw_burst",
    mode=RandomizationMode.ENUMERATED,
    constraints={
        "bins": [0, 1, 2],  # FIXED, INCR, WRAP
        "weights": [0.1, 0.7, 0.2]
    }
)

# Configure error injection
config.set_error_injection_rate(0.05)  # 5% error responses

# Configure QoS distribution
config.set_qos_distribution([
    (0, 0.6),   # 60% chance of QoS 0
    (8, 0.3),   # 30% chance of QoS 8
    (15, 0.1)   # 10% chance of QoS 15
])

# Use the configuration
sequence = AXI4TransactionSequence(
    name="random_sequence",
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    randomization_config=config
)
```

### Coverage-Driven Randomization

```python
class CoverageTracker:
    """Track coverage of AXI4 features."""
    
    def __init__(self):
        # Initialize coverage bins
        self.burst_type_coverage = {0: 0, 1: 0, 2: 0}  # FIXED, INCR, WRAP
        self.burst_len_coverage = {}
        self.burst_size_coverage = {}
        self.addr_region_coverage = {}
        self.exclusive_coverage = {0: 0, 1: 0}  # Normal, Exclusive
        self.protection_coverage = {}
        self.response_coverage = {0: 0, 1: 0, 2: 0, 3: 0}  # OKAY, EXOKAY, SLVERR, DECERR
        
        # Define address regions (4KB blocks)
        self.addr_regions = [(i*0x1000, (i+1)*0x1000 - 1) for i in range(16)]
        for region in self.addr_regions:
            self.addr_region_coverage[region] = 0
        
        # Initialize burst length bins
        for i in range(16):
            self.burst_len_coverage[i] = 0
        
        # Initialize burst size bins
        for i in range(4):
            self.burst_size_coverage[i] = 0
        
        # Initialize protection bins (8 combinations)
        for i in range(8):
            self.protection_coverage[i] = 0
    
    def update_from_packet(self, packet):
        """Update coverage from an AXI4 packet."""
        # Determine packet type
        if hasattr(packet, 'awaddr'):  # AW packet
            # Update burst type coverage
            self.burst_type_coverage[packet.awburst] += 1
            
            # Update burst length coverage
            self.burst_len_coverage[min(15, packet.awlen)] += 1
            
            # Update burst size coverage
            self.burst_size_coverage[min(3, packet.awsize)] += 1
            
            # Update address region coverage
            for region in self.addr_regions:
                if region[0] <= packet.awaddr <= region[1]:
                    self.addr_region_coverage[region] += 1
                    break
            
            # Update exclusive coverage
            self.exclusive_coverage[packet.awlock] += 1
            
            # Update protection coverage
            self.protection_coverage[packet.awprot] += 1
        
        elif hasattr(packet, 'araddr'):  # AR packet
            # Update burst type coverage
            self.burst_type_coverage[packet.arburst] += 1
            
            # Update burst length coverage
            self.burst_len_coverage[min(15, packet.arlen)] += 1
            
            # Update burst size coverage
            self.burst_size_coverage[min(3, packet.arsize)] += 1
            
            # Update address region coverage
            for region in self.addr_regions:
                if region[0] <= packet.araddr <= region[1]:
                    self.addr_region_coverage[region] += 1
                    break
            
            # Update exclusive coverage
            self.exclusive_coverage[packet.arlock] += 1
            
            # Update protection coverage
            self.protection_coverage[packet.arprot] += 1
        
        elif hasattr(packet, 'bresp'):  # B packet
            # Update response coverage
            self.response_coverage[packet.bresp] += 1
        
        elif hasattr(packet, 'rresp'):  # R packet
            # Update response coverage
            self.response_coverage[packet.rresp] += 1
    
    def get_coverage_report(self):
        """Generate a coverage report."""
        report = {}
        
        # Calculate burst type coverage
        total_bursts = sum(self.burst_type_coverage.values())
        if total_bursts > 0:
            report['burst_type'] = {
                'FIXED': self.burst_type_coverage[0] / total_bursts,
                'INCR': self.burst_type_coverage[1] / total_bursts,
                'WRAP': self.burst_type_coverage[2] / total_bursts
            }
        
        # Calculate burst length coverage
        total_lens = sum(self.burst_len_coverage.values())
        if total_lens > 0:
            report['burst_len'] = {
                f'LEN{i}': self.burst_len_coverage[i] / total_lens
                for i in range(16)
            }
        
        # Calculate burst size coverage
        total_sizes = sum(self.burst_size_coverage.values())
        if total_sizes > 0:
            report['burst_size'] = {
                f'SIZE{i}': self.burst_size_coverage[i] / total_sizes
                for i in range(4)
            }
        
        # Calculate address region coverage
        total_addrs = sum(self.addr_region_coverage.values())
        if total_addrs > 0:
            report['addr_region'] = {
                f'0x{region[0]:X}-0x{region[1]:X}': self.addr_region_coverage[region] / total_addrs
                for region in self.addr_regions
            }
        
        # Calculate exclusive coverage
        total_exclusive = sum(self.exclusive_coverage.values())
        if total_exclusive > 0:
            report['exclusive'] = {
                'Normal': self.exclusive_coverage[0] / total_exclusive,
                'Exclusive': self.exclusive_coverage[1] / total_exclusive
            }
        
        # Calculate protection coverage
        total_prot = sum(self.protection_coverage.values())
        if total_prot > 0:
            report['protection'] = {
                f'PROT{i}': self.protection_coverage[i] / total_prot
                for i in range(8)
            }
        
        # Calculate response coverage
        total_resp = sum(self.response_coverage.values())
        if total_resp > 0:
            report['response'] = {
                'OKAY': self.response_coverage[0] / total_resp,
                'EXOKAY': self.response_coverage[1] / total_resp,
                'SLVERR': self.response_coverage[2] / total_resp,
                'DECERR': self.response_coverage[3] / total_resp
            }
        
        return report
    
    def identify_coverage_gaps(self):
        """Identify areas with low coverage."""
        gaps = []
        
        # Check burst type coverage
        for burst_type, count in self.burst_type_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for burst type {burst_type}")
        
        # Check burst length coverage
        for burst_len, count in self.burst_len_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for burst length {burst_len}")
        
        # Check burst size coverage
        for burst_size, count in self.burst_size_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for burst size {burst_size}")
        
        # Check exclusive coverage
        for exclusive, count in self.exclusive_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for exclusive {exclusive}")
        
        # Check protection coverage
        for prot, count in self.protection_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for protection {prot}")
        
        # Check response coverage
        for resp, count in self.response_coverage.items():
            if count == 0:
                gaps.append(f"No coverage for response {resp}")
        
        return gaps
    
    def generate_coverage_driven_sequence(self):
        """Generate a sequence to cover identified gaps."""
        gaps = self.identify_coverage_gaps()
        
        # Create a new sequence
        sequence = AXI4TransactionSequence(
            name="coverage_driven",
            id_width=8,
            addr_width=32,
            data_width=32,
            user_width=1
        )
        
        # Address coverage gaps
        for gap in gaps:
            if "burst type" in gap:
                burst_type = int(gap.split()[-1])
                sequence.add_write_transaction(
                    addr=0x1000,
                    data_values=[0xDEADBEEF],
                    burst_type=burst_type
                )
            
            elif "burst length" in gap:
                burst_len = int(gap.split()[-1])
                # Create data for this burst length
                data_values = [0xA0000000 + i for i in range(burst_len + 1)]
                sequence.add_write_transaction(
                    addr=0x2000,
                    data_values=data_values,
                    burst_len=burst_len
                )
            
            elif "burst size" in gap:
                burst_size = int(gap.split()[-1])
                sequence.add_write_transaction(
                    addr=0x3000,
                    data_values=[0xCCCCCCCC],
                    burst_size=burst_size
                )
            
            elif "exclusive" in gap:
                exclusive = int(gap.split()[-1])
                sequence.add_read_transaction(
                    addr=0x4000,
                    lock=exclusive
                )
            
            elif "protection" in gap:
                prot = int(gap.split()[-1])
                sequence.add_write_transaction(
                    addr=0x5000,
                    data_values=[0xEEEEEEEE],
                    prot=prot
                )
            
            elif "response" in gap:
                resp = int(gap.split()[-1])
                id_value = sequence.add_read_transaction(addr=0x6000)
                sequence.add_read_response_data(
                    id_value=id_value,
                    data_values=[0],
                    resp_values=[resp]
                )
        
        return sequence

# Usage example
async def run_coverage_driven_test(dut):
    # [Initialize components]
    
    # Create coverage tracker
    coverage = CoverageTracker()
    
    # Create a monitor callback to update coverage
    def monitor_callback(packet):
        coverage.update_from_packet(packet)
    
    # Register the callback with monitor
    monitor.aw_monitor.add_callback(monitor_callback)
    monitor.w_monitor.add_callback(monitor_callback)
    monitor.b_monitor.add_callback(monitor_callback)
    monitor.ar_monitor.add_callback(monitor_callback)
    monitor.r_monitor.add_callback(monitor_callback)
    
    # Run an initial sequence
    sequence1 = AXI4TransactionSequence.create_simple_writes(...)
    await cmd_handler.process_transaction_sequence(sequence1)
    
    # Generate a coverage report
    report = coverage.get_coverage_report()
    print("Coverage after first sequence:")
    for category, values in report.items():
        print(f"  {category}:")
        for name, percentage in values.items():
            print(f"    {name}: {percentage:.2%}")
    
    # Identify gaps
    gaps = coverage.identify_coverage_gaps()
    print("Coverage gaps:")
    for gap in gaps:
        print(f"  {gap}")
    
    # Generate a sequence to address the gaps
    if gaps:
        gap_sequence = coverage.generate_coverage_driven_sequence()
        await cmd_handler.process_transaction_sequence(gap_sequence)
        
        # Check updated coverage
        report = coverage.get_coverage_report()
        print("Coverage after gap-filling sequence:")
        for category, values in report.items():
            print(f"  {category}:")
            for name, percentage in values.items():
                print(f"    {name}: {percentage:.2%}")
    
    # Remaining gaps?
    remaining_gaps = coverage.identify_coverage_gaps()
    if not remaining_gaps:
        print("Full coverage achieved!")
```

### Constrained Random Testing

```python
def generate_constrained_random_sequence(transaction_count=100, config=None):
    """Generate a constrained random sequence with good coverage properties."""
    if config is None:
        # Create a default randomization configuration
        config = AXI4RandomizationConfig()
        
        # Configure address range
        config.configure_field(
            field_name="aw_addr",
            mode=RandomizationMode.CONSTRAINED,
            constraints={
                "bins": [(0x1000, 0x1FFF), (0x2000, 0x2FFF), (0x3000, 0x3FFF)],
                "weights": [0.4, 0.4, 0.2]
            }
        )
        
        # Configure burst types
        config.configure_field(
            field_name="aw_burst",
            mode=RandomizationMode.ENUMERATED,
            constraints={
                "bins": [0, 1, 2],  # FIXED, INCR, WRAP
                "weights": [0.2, 0.6, 0.2]
            }
        )
        
        # Configure burst lengths
        config.configure_field(
            field_name="aw_len",
            mode=RandomizationMode.CONSTRAINED,
            constraints={
                "bins": [(0, 0), (1, 3), (4, 7), (8, 15)],
                "weights": [0.4, 0.3, 0.2, 0.1]
            }
        )
        
        # Configure transaction IDs
        config.configure_field(
            field_name="aw_id",
            mode=RandomizationMode.CONSTRAINED,
            constraints={
                "bins": [(0, 7)],
                "weights": [1.0]
            }
        )
    
    # Create the sequence
    sequence = AXI4TransactionSequence(
        name="constrained_random",
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1,
        randomization_config=config
    )
    
    # Add random transactions
    for i in range(transaction_count):
        # Randomly choose between write and read
        is_write = sequence.get_random_value("is_write", 0, 1) == 1
        
        if is_write:
            # Generate random parameters
            addr = sequence.get_random_value("aw_addr")
            id_value = sequence.get_random_value("aw_id", 0, 7)
            burst_type = sequence.get_random_value("aw_burst", 0, 2)
            burst_size = sequence.get_random_value("aw_size", 0, 2)
            
            # For WRAP bursts, ensure burst_len is valid
            if burst_type == 2:  # WRAP
                # Valid values: 1, 3, 7, 15 (2^n - 1)
                burst_lens = [1, 3, 7, 15]
                burst_len = burst_lens[sequence.get_random_value("wrap_len", 0, 3)]
            else:
                burst_len = sequence.get_random_value("aw_len")
            
            # Generate random data
            data_count = burst_len + 1
            data_values = [sequence.get_random_value("w_data") for _ in range(data_count)]
            
            # Add the transaction
            sequence.add_write_transaction(
                addr=addr,
                data_values=data_values,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=burst_type
            )
        else:
            # Generate random parameters
            addr = sequence.get_random_value("ar_addr")
            id_value = sequence.get_random_value("ar_id", 0, 7)
            burst_type = sequence.get_random_value("ar_burst", 0, 2)
            burst_size = sequence.get_random_value("ar_size", 0, 2)
            
            # For WRAP bursts, ensure burst_len is valid
            if burst_type == 2:  # WRAP
                # Valid values: 1, 3, 7, 15 (2^n - 1)
                burst_lens = [1, 3, 7, 15]
                burst_len = burst_lens[sequence.get_random_value("wrap_len", 0, 3)]
            else:
                burst_len = sequence.get_random_value("ar_len")
            
            # Add the transaction
            sequence.add_read_transaction(
                addr=addr,
                id_value=id_value,
                burst_len=burst_len,
                burst_size=burst_size,
                burst_type=burst_type
            )
    
    return sequence

# Usage example
async def run_constrained_random_test(dut):
    # [Initialize components]
    
    # Generate a constrained random sequence
    sequence = generate_constrained_random_sequence(transaction_count=100)
    
    # Process the sequence
    complete_event = await cmd_handler.process_transaction_sequence(sequence)
    await complete_event.wait()
    
    # Check results
    stats = cmd_handler.get_stats()
    print(f"Processed {stats['completed_transactions']} transactions")
```

## Sequence Visualization

Visualizing sequences helps with debugging and understanding test coverage. This section covers tools and techniques for sequence visualization.

### Transaction Diagram Generation

```python
def generate_transaction_diagram(sequence, output_file="transaction_diagram.html"):
    """Generate an HTML visualization of transactions and dependencies."""
    import html
    
    # Get all transaction IDs
    write_ids = sequence.get_write_ids()
    read_ids = sequence.get_read_ids()
    
    # Create HTML content
    html_content = """
    <!DOCTYPE html>
    <html>
    <head>
        <title>AXI4 Transaction Diagram</title>
        <style>
            body { font-family: Arial, sans-serif; }
            .container { display: flex; }
            .timeline { flex: 1; }
            .transaction { 
                margin: 5px; 
                padding: 5px; 
                border-radius: 5px;
            }
            .write { background-color: #ffe0e0; border: 1px solid #ff8080; }
            .read { background-color: #e0e0ff; border: 1px solid #8080ff; }
            .dependency {
                position: absolute;
                border-top: 1px dashed #808080;
                z-index: -1;
            }
            .details {
                font-size: 0.8em;
                margin-top: 5px;
                color: #404040;
            }
        </style>
    </head>
    <body>
        <h1>AXI4 Transaction Diagram</h1>
        <p>Sequence: """ + html.escape(sequence.name) + """</p>
        <div class="container">
            <div class="timeline" id="timeline">
    """
    
    # Add transactions
    for write_id in write_ids:
        packet = sequence.get_write_addr_packet(write_id)
        if packet:
            addr = packet.awaddr
            burst_type = ["FIXED", "INCR", "WRAP"][packet.awburst]
            burst_len = packet.awlen
            burst_size = packet.awsize
            
            # Get dependencies
            deps = sequence.get_dependencies(write_id, is_read=False)
            dep_str = ", ".join([str(d) for d in deps])
            
            html_content += f"""
                <div class="transaction write" id="W{write_id}">
                    <b>Write ID {write_id}</b>
                    <div class="details">
                        Address: 0x{addr:08X}<br>
                        Burst: {burst_type}, Length: {burst_len}, Size: {burst_size}<br>
                        Dependencies: {dep_str}
                    </div>
                </div>
            """
    
    for read_id in read_ids:
        packet = sequence.get_read_addr_packet(read_id)
        if packet:
            addr = packet.araddr
            burst_type = ["FIXED", "INCR", "WRAP"][packet.arburst]
            burst_len = packet.arlen
            burst_size = packet.arsize
            
            # Get dependencies
            deps = sequence.get_dependencies(read_id, is_read=True)
            dep_str = ", ".join([str(d) for d in deps])
            
            html_content += f"""
                <div class="transaction read" id="R{read_id}">
                    <b>Read ID {read_id}</b>
                    <div class="details">
                        Address: 0x{addr:08X}<br>
                        Burst: {burst_type}, Length: {burst_len}, Size: {burst_size}<br>
                        Dependencies: {dep_str}
                    </div>
                </div>
            """
    
    # Close HTML
    html_content += """
            </div>
        </div>
        
        <script>
            // Draw dependency arrows
            function drawDependencies() {
                var timeline = document.getElementById('timeline');
    """
    
    # Add JavaScript to draw dependencies
    for write_id in write_ids:
        deps = sequence.get_dependencies(write_id, is_read=False)
        for dep in deps:
            html_content += f"""
                drawArrow('W{write_id}', '{("W" if dep in write_ids else "R") + str(dep)}');
            """
    
    for read_id in read_ids:
        deps = sequence.get_dependencies(read_id, is_read=True)
        for dep in deps:
            html_content += f"""
                drawArrow('R{read_id}', '{("W" if dep in write_ids else "R") + str(dep)}');
            """
    
    html_content += """
            function drawArrow(fromId, toId) {
                var fromElem = document.getElementById(fromId);
                var toElem = document.getElementById(toId);
                
                if (!fromElem || !toElem) return;
                
                var fromRect = fromElem.getBoundingClientRect();
                var toRect = toElem.getBoundingClientRect();
                
                var arrow = document.createElement('div');
                arrow.className = 'dependency';
                
                // Position arrow
                var timeline = document.getElementById('timeline');
                var tlRect = timeline.getBoundingClientRect();
                
                arrow.style.left = (toRect.right - tlRect.left) + 'px';
                arrow.style.top = (toRect.bottom - tlRect.top + 10) + 'px';
                arrow.style.width = ((fromRect.left - toRect.right) * 0.8) + 'px';
                arrow.style.height = ((fromRect.top - toRect.bottom) * 0.8) + 'px';
                
                timeline.appendChild(arrow);
            }
            
            window.onload = drawDependencies;
        </script>
    </body>
    </html>
    """
    
    # Write to file
    with open(output_file, "w") as f:
        f.write(html_content)
    
    print(f"Transaction diagram generated: {output_file}")
    return output_file

# Usage example
sequence = AXI4TransactionSequence.create_protocol_stress_test(data_width=32)
diagram_file = generate_transaction_diagram(sequence)
```

### Timeline Visualization

```python
def generate_timeline_visualization(cmd_handler, sequence, output_file="timeline.html"):
    """Generate an HTML timeline visualization of transaction execution."""
    import html
    import time
    
    # Execute the sequence and collect timing information
    transaction_timings = []
    
    # Create callbacks to track transaction times
    def start_callback(transaction_type, id_value, timestamp):
        transaction_timings.append({
            'type': transaction_type,
            'id': id_value,
            'start': timestamp,
            'end': None  # Will be filled in by end callback
        })
    
    def end_callback(transaction_type, id_value, timestamp):
        # Find the matching transaction
        for tx in transaction_timings:
            if tx['type'] == transaction_type and tx['id'] == id_value and tx['end'] is None:
                tx['end'] = timestamp
                break
    
    # Register callbacks with command handler
    cmd_handler.register_transaction_callback('start', start_callback)
    cmd_handler.register_transaction_callback('end', end_callback)
    
    # Process the sequence
    complete_event = await cmd_handler.process_transaction_sequence(sequence)
    await complete_event.wait()
    
    # Unregister callbacks
    cmd_handler.unregister_transaction_callback('start', start_callback)
    cmd_handler.unregister_transaction_callback('end', end_callback)
    
    # Find time range
    start_time = min(tx['start'] for tx in transaction_timings)
    end_time = max(tx['end'] for tx in transaction_timings if tx['end'] is not None)
    duration = end_time - start_time
    
    # Create HTML content
    html_content = """
    <!DOCTYPE html>
    <html>
    <head>
        <title>AXI4 Transaction Timeline</title>
        <style>
            body { font-family: Arial, sans-serif; }
            .timeline { position: relative; margin: 20px; height: 600px; }
            .time-axis { position: absolute; top: 0; left: 0; height: 100%; width: 100%; }
            .time-mark { position: absolute; width: 100%; border-top: 1px solid #e0e0e0; }
            .time-label { position: absolute; left: 0; font-size: 0.8em; color: #808080; }
            .transaction { 
                position: absolute; 
                height: 20px; 
                border-radius: 5px;
                font-size: 0.8em;
                text-align: center;
                overflow: hidden;
                white-space: nowrap;
            }
            .write { background-color: #ffe0e0; border: 1px solid #ff8080; }
            .read { background-color: #e0e0ff; border: 1px solid #8080ff; }
            .tooltip {
                position: absolute;
                background-color: white;
                border: 1px solid #c0c0c0;
                padding: 5px;
                border-radius: 3px;
                font-size: 0.8em;
                display: none;
                z-index: 100;
            }
        </style>
    </head>
    <body>
        <h1>AXI4 Transaction Timeline</h1>
        <p>Sequence: """ + html.escape(sequence.name) + """</p>
        <div class="timeline" id="timeline">
            <div class="time-axis" id="time-axis">
    """
    
    # Add time marks
    step = duration / 10
    for i in range(11):
        time_val = start_time + i * step
        percent = i * 10
        html_content += f"""
                <div class="time-mark" style="top: {percent}%"></div>
                <div class="time-label" style="top: {percent}%">{time_val:.2f} ns</div>
        """
    
    # Add transactions
    for i, tx in enumerate(transaction_timings):
        if tx['end'] is None:
            continue  # Skip incomplete transactions
        
        tx_start_percent = ((tx['start'] - start_time) / duration) * 100
        tx_duration_percent = ((tx['end'] - tx['start']) / duration) * 100
        tx_type_class = "write" if tx['type'].startswith("write") else "read"
        
        # Position horizontally based on ID
        lane = tx['id'] % 10  # Use 10 lanes
        left_percent = 10 + (lane * 9)  # Distribute across 90% of width
        
        html_content += f"""
                <div class="transaction {tx_type_class}" 
                     style="top: {tx_start_percent}%; height: {max(0.5, tx_duration_percent)}%; left: {left_percent}%; width: 8%;"
                     onmouseover="showTooltip(event, {i})" onmouseout="hideTooltip()">
                    {tx['type']} {tx['id']}
                </div>
        """
    
    # Add tooltip div
    html_content += """
            </div>
        </div>
        <div id="tooltip" class="tooltip"></div>
        
        <script>
            // Transaction data
            var transactions = [
    """
    
    # Add transaction data for tooltips
    for tx in transaction_timings:
        if tx['end'] is None:
            continue  # Skip incomplete transactions
        
        # Format transaction details
        tx_data = {
            'type': tx['type'],
            'id': tx['id'],
            'start': f"{tx['start']:.2f}",
            'end': f"{tx['end']:.2f}",
            'duration': f"{tx['end'] - tx['start']:.2f}"
        }
        
        html_content += f"                {str(tx_data)},\n"
    
    html_content += """
            ];
            
            function showTooltip(event, index) {
                var tooltip = document.getElementById('tooltip');
                var tx = transactions[index];
                
                tooltip.innerHTML = `
                    <div><b>${tx.type} ${tx.id}</b></div>
                    <div>Start: ${tx.start} ns</div>
                    <div>End: ${tx.end} ns</div>
                    <div>Duration: ${tx.duration} ns</div>
                `;
                
                tooltip.style.left = (event.pageX + 10) + 'px';
                tooltip.style.top = (event.pageY + 10) + 'px';
                tooltip.style.display = 'block';
            }
            
            function hideTooltip() {
                document.getElementById('tooltip').style.display = 'none';
            }
        </script>
    </body>
    </html>
    """
    
    # Write to file
    with open(output_file, "w") as f:
        f.write(html_content)
    
    print(f"Timeline visualization generated: {output_file}")
    return output_file
```

### Coverage Visualization

```python
def generate_coverage_visualization(coverage_tracker, output_file="coverage.html"):
    """Generate an HTML visualization of test coverage."""
    import html
    
    # Get coverage report
    report = coverage_tracker.get_coverage_report()
    
    # Create HTML content
    html_content = """
    <!DOCTYPE html>
    <html>
    <head>
        <title>AXI4 Coverage Report</title>
        <style>
            body { font-family: Arial, sans-serif; }
            .report { margin: 20px; }
            .category { margin-bottom: 30px; }
            .category-title { font-weight: bold; margin-bottom: 10px; }
            .bar-container { width: 100%; height: 20px; background-color: #f0f0f0; margin: 5px 0; }
            .bar { height: 100%; background-color: #4CAF50; }
            .item { margin-bottom: 5px; }
            .label { display: inline-block; width: 150px; }
            .value { display: inline-block; width: 50px; text-align: right; }
        </style>
    </head>
    <body>
        <h1>AXI4 Coverage Report</h1>
        <div class="report">
    """
    
    # Add coverage data for each category
    for category, values in report.items():
        html_content += f"""
            <div class="category">
                <div class="category-title">{html.escape(category)}</div>
        """
        
        for name, percentage in values.items():
            bar_width = percentage * 100
            html_content += f"""
                <div class="item">
                    <span class="label">{html.escape(name)}</span>
                    <span class="value">{percentage:.1%}</span>
                    <div class="bar-container">
                        <div class="bar" style="width: {bar_width}%;"></div>
                    </div>
                </div>
            """
        
        html_content += """
            </div>
        """
    
    html_content += """
        </div>
    </body>
    </html>
    """
    
    # Write to file
    with open(output_file, "w") as f:
        f.write(html_content)
    
    print(f"Coverage visualization generated: {output_file}")
    return output_file
```

## Advanced Test Patterns

This section covers advanced test patterns that can be implemented using AXI4 sequences.

### Cache Coherency Testing

```python
def create_cache_coherency_test(data_width=32):
    """Create a sequence that tests cache coherency between multiple masters."""
    # Create a sequence to test cache coherency
    sequence = AXI4TransactionSequence(
        name="cache_coherency_test",
        id_width=8,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )
    
    # Define test addresses
    addresses = [0x1000, 0x2000, 0x3000, 0x4000]
    
    # Master 1: Initial writes
    master1_write_ids = []
    for i, addr in enumerate(addresses):
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xA0000000 + i],
            id_value=0x10  # Master 1 ID range: 0x10-0x1F
        )
        master1_write_ids.append(write_id)
    
    # Master 2: Read initial values
    master2_read_ids = []
    for i, addr in enumerate(addresses):
        read_id = sequence.add_read_transaction(
            addr=addr,
            id_value=0x20,  # Master 2 ID range: 0x20-0x2F
            dependencies=[master1_write_ids[i]]
        )
        master2_read_ids.append(read_id)
        
        # Add expected data (should see Master 1's writes)
        sequence.add_read_response_data(
            id_value=read_id,
            data_values=[0xA0000000 + i]
        )
    
    # Master 2: Update values
    master2_write_ids = []
    for i, addr in enumerate(addresses):
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xB0000000 + i],
            id_value=0x21,  # Master 2 ID range: 0x20-0x2F
            dependencies=[master2_read_ids[i]]
        )
        master2_write_ids.append(write_id)
    
    # Master 1: Read updated values
    master1_read_ids = []
    for i, addr in enumerate(addresses):
        read_id = sequence.add_read_transaction(
            addr=addr,
            id_value=0x11,  # Master 1 ID range: 0x10-0x1F
            dependencies=[master2_write_ids[i]]
        )
        master1_read_ids.append(read_id)
        
        # Add expected data (should see Master 2's writes)
        sequence.add_read_response_data(
            id_value=read_id,
            data_values=[0xB0000000 + i]
        )
    
    # Master 3: Read values directly after Master 2's writes
    for i, addr in enumerate(addresses):
        read_id = sequence.add_read_transaction(
            addr=addr,
            id_value=0x30,  # Master 3 ID range: 0x30-0x3F
            dependencies=[master2_write_ids[i]]
        )
        
        # Add expected data (should see Master 2's writes)
        sequence.add_read_response_data(
            id_value=read_id,
            data_values=[0xB0000000 + i]
        )
    
    return sequence
```

### Memory Access Patterns

```python
def create_memory_access_pattern_test(data_width=32):
    """Create a sequence with various memory access patterns."""
    sequence = AXI4TransactionSequence(
        name="memory_access_patterns",
        id_width=8,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )
    
    # Initialize test area
    base_addr = 0x10000
    region_size = 0x1000
    
    # 1. Sequential Access
    seq_write_ids = []
    for i in range(16):
        addr = base_addr + (i * 4)
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xA0000000 + i]
        )
        seq_write_ids.append(write_id)
    
    # Sequential read (depends on all writes)
    for i in range(16):
        addr = base_addr + (i * 4)
        read_id = sequence.add_read_transaction(
            addr=addr,
            dependencies=seq_write_ids
        )
        sequence.add_read_response_data(read_id, [0xA0000000 + i])
    
    # 2. Strided Access
    stride_base = base_addr + region_size
    stride_write_ids = []
    stride = 64  # 16 words stride
    
    for i in range(16):
        addr = stride_base + (i * stride)
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xB0000000 + i]
        )
        stride_write_ids.append(write_id)
    
    # Strided read (depends on all stride writes)
    for i in range(16):
        addr = stride_base + (i * stride)
        read_id = sequence.add_read_transaction(
            addr=addr,
            dependencies=stride_write_ids
        )
        sequence.add_read_response_data(read_id, [0xB0000000 + i])
    
    # 3. Random Access
    random_base = base_addr + (2 * region_size)
    random_write_ids = []
    # Use fixed "random" pattern for repeatability
    random_offsets = [0x123, 0x234, 0x345, 0x456, 0x567, 0x678, 0x789, 0x89A,
                     0x9AB, 0xABC, 0xBCD, 0xCDE, 0xDEF, 0xEF0, 0xF01, 0x012]
    
    for i, offset in enumerate(random_offsets):
        addr = random_base + offset
        write_id = sequence.add_write_transaction(
            addr=addr,
            data_values=[0xC0000000 + i]
        )
        random_write_ids.append(write_id)
    
    # Random read (depends on all random writes)
    for i, offset in enumerate(random_offsets):
        addr = random_base + offset
        read_id = sequence.add_read_transaction(
            addr=addr,
            dependencies=random_write_ids
        )
        sequence.add_read_response_data(read_id, [0xC0000000 + i])
    
    # 4. Row-major vs Column-major Access
    matrix_base = base_addr + (3 * region_size)
    matrix_size = 8  # 8x8 matrix
    word_size = 4    # 4 bytes per word
    
    # Initialize matrix with row * 1000 + col pattern
    matrix_write_ids = []
    for row in range(matrix_size):
        for col in range(matrix_size):
            addr = matrix_base + (row * matrix_size + col) * word_size
            value = 0xD0000000 + (row * 100) + col
            write_id = sequence.add_write_transaction(
                addr=addr,
                data_values=[value]
            )
            matrix_write_ids.append(write_id)
    
    # Row-major read (all rows in sequence)
    for row in range(matrix_size):
        burst_data = []
        for col in range(matrix_size):
            burst_data.append(0xD0000000 + (row * 100) + col)
        
        read_id = sequence.add_read_transaction(
            addr=matrix_base + (row * matrix_size) * word_size,
            burst_len=matrix_size - 1,
            dependencies=matrix_write_ids
        )
        sequence.add_read_response_data(read_id, burst_data)
    
    # Column-major read (read each column in sequence)
    for col in range(matrix_size):
        # Need separate reads for each element in column (non-contiguous)
        for row in range(matrix_size):
            addr = matrix_base + (row * matrix_size + col) * word_size
            value = 0xD0000000 + (row * 100) + col
            
            read_id = sequence.add_read_transaction(
                addr=addr,
                dependencies=matrix_write_ids
            )
            sequence.add_read_response_data(read_id, [value])
    
    return sequence
```

### Boundary Conditions

```python
def create_boundary_condition_test(data_width=32):
    """Create a sequence that tests various boundary conditions."""
    sequence = AXI4TransactionSequence(
        name="boundary_conditions",
        id_width=8,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )
    
    # Calculate derived parameters
    bytes_per_beat = data_width // 8
    max_burst_size = (bytes_per_beat).bit_length() - 1
    
    # 1. 4KB Boundary Tests
    boundary = 0x1000  # 4KB boundary
    
    # Just before boundary
    boundary_addr = boundary - bytes_per_beat
    sequence.add_write_transaction(
        addr=boundary_addr,
        data_values=[0xA1A1A1A1],
        burst_size=max_burst_size
    )
    
    # At boundary
    sequence.add_write_transaction(
        addr=boundary,
        data_values=[0xA2A2A2A2],
        burst_size=max_burst_size
    )
    
    # Burst crossing boundary
    cross_addr = boundary - (4 * bytes_per_beat)
    cross_data = [0xB1B1B1B1, 0xB2B2B2B2, 0xB3B3B3B3, 0xB4B4B4B4,
                 0xB5B5B5B5, 0xB6B6B6B6, 0xB7B7B7B7, 0xB8B8B8B8]
    sequence.add_write_transaction(
        addr=cross_addr,
        data_values=cross_data,
        burst_type=1  # INCR
    )
    
    # 2. Alignment Tests
    for size in range(max_burst_size + 1):
        size_bytes = 1 << size
        aligned_addr = 0x2000 + (size * 0x100)
        
        # Aligned access
        sequence.add_write_transaction(
            addr=aligned_addr,
            data_values=[0xC1C1C1C1],
            burst_size=size
        )
        
        # Unaligned access (should be automatically aligned)
        if size > 0:  # Only test unaligned if size > byte
            unaligned_addr = aligned_addr + 1  # Unaligned by 1 byte
            sequence.add_write_transaction(
                addr=unaligned_addr,
                data_values=[0xC2C2C2C2],
                burst_size=size
            )
    
    # 3. Burst Size Tests
    for size in range(max_burst_size + 1):
        addr = 0x3000 + (size * 0x100)
        size_bytes = 1 << size
        
        # Create appropriate data for this burst size
        if size_bytes >= 4:
            data_values = [0xD1D1D1D1, 0xD2D2D2D2, 0xD3D3D3D3, 0xD4D4D4D4]
        else:
            # For small burst sizes, truncate data appropriately
            mask = (1 << (size_bytes * 8)) - 1
            data_values = [0xD1D1D1D1 & mask, 0xD2D2D2D2 & mask, 
                          0xD3D3D3D3 & mask, 0xD4D4D4D4 & mask]
        
        sequence.add_write_transaction(
            addr=addr,
            data_values=data_values,
            burst_size=size,
            burst_type=1  # INCR
        )
    
    # 4. WRAP Burst Address Tests
    for length in [1, 3, 7, 15]:  # 2, 4, 8, 16 beats
        bytes_in_burst = (length + 1) * bytes_per_beat
        
        # Normal case
        wrap_addr = 0x4000 + (length * 0x100)
        data_values = [0xE0 + i for i in range(length + 1)]
        sequence.add_write_transaction(
            addr=wrap_addr,
            data_values=data_values,
            burst_len=length,
            burst_type=2  # WRAP
        )
        
        # Wrap boundary case - halfway through wrap boundary
        boundary_addr = 0x4000 + (length * 0x100) + bytes_in_burst // 2
        sequence.add_write_transaction(
            addr=boundary_addr,
            data_values=data_values,
            burst_len=length,
            burst_type=2  # WRAP
        )
    
    # 5. Maximum Burst Length Test
    max_addr = 0x5000
    # Use a practical max length instead of 255 for simulation efficiency
    practical_max = 31  # 32 beats
    max_data = [0xF000 + i for i in range(practical_max + 1)]
    sequence.add_write_transaction(
        addr=max_addr,
        data_values=max_data,
        burst_len=practical_max,
        burst_type=1  # INCR
    )
    
    return sequence
```

### Error Injection

```python
def create_error_injection_test(data_width=32):
    """Create a sequence with various error conditions."""
    sequence = AXI4TransactionSequence(
        name="error_injection",
        id_width=8,
        addr_width=32,
        data_width=data_width,
        user_width=1
    )
    
    # 1. SLVERR Response - Read from invalid peripheral address
    read_id = sequence.add_read_transaction(
        addr=0xF0000000  # Assumed to be unmapped/invalid
    )
    # Expect SLVERR response
    sequence.add_read_response_data(
        id_value=read_id,
        data_values=[0],  # Data doesn't matter for error response
        resp_values=[2]   # SLVERR
    )
    
    # 2. DECERR Response - Access to non-existent memory region
    read_id = sequence.add_read_transaction(
        addr=0xFFFFFFFC  # Assumed to be decode error region
    )
    # Expect DECERR response
    sequence.add_read_response_data(
        id_value=read_id,
        data_values=[0],  # Data doesn't matter for error response
        resp_values=[3]   # DECERR
    )
    
    # 3. Exclusive Access Failure
    # First, normal write to initialize
    write_id = sequence.add_write_transaction(
        addr=0x6000,
        data_values=[0xA5A5A5A5]
    )
    
    # Then exclusive read
    ex_read_id = sequence.add_read_transaction(
        addr=0x6000,
        lock=1,  # Exclusive
        dependencies=[write_id]
    )
    sequence.add_read_response_data(
        id_value=ex_read_id,
        data_values=[0xA5A5A5A5]
    )
    
    # Normal write from another master that breaks exclusivity
    break_id = sequence.add_write_transaction(
        addr=0x6000,
        data_values=[0xB5B5B5B5],
        id_value=0x20,  # Different ID range to simulate another master
        dependencies=[ex_read_id]
    )
    
    # Exclusive write that should fail
    ex_write_id = sequence.add_write_transaction(
        addr=0x6000,
        data_values=[0xC5C5C5C5],
        lock=1,  # Exclusive
        id_value=0x10,  # Original master
        dependencies=[break_id]
    )
    
    # Expect normal OKAY response (not EXOKAY) for failed exclusive write
    sequence.add_write_response(
        id_value=ex_write_id,
        resp=0  # OKAY
    )
    
    # 4. Timeout Simulation - Read with no response
    # This typically requires special handling in the testbench
    timeout_id = sequence.add_read_transaction(
        addr=0x7000,  # Address that won't respond
        id_value=0x30
    )
    
    # 5. Protocol Violation
    # Generate a "bad" transaction that violates protocol
    # For example, an unaligned address for a burst size
    protocol_id = sequence.add_write_transaction(
        addr=0x8001,  # Unaligned for word access
        data_values=[0xD5D5D5D5],
        burst_size=2   # Word (4 bytes) requires alignment
    )
    
    return sequence
```

## Best Practices

This section provides best practices for effectively using AXI4 sequences in your verification environment.

### Guidelines for Creating Sequences

1. **Build from Standard Factory Methods**: Start with the provided factory methods and customize as needed
2. **Use Proper Memory Alignment**: Always use proper alignment for the data width and burst size
3. **Validate Protocol Parameters**: Validate burst parameters before execution
4. **Manage Transaction IDs**: Use sequentially allocated IDs to avoid conflicts
5. **Create Dependencies Carefully**: Avoid circular dependencies between transactions
6. **Build Composable Sequences**: Create small, focused sequences that can be combined
7. **Scale for Data Width**: Make sequences data-width aware
8. **Document Sequence Purpose**: Add comments explaining test goals and expected results
9. **Clean Up Resources**: Use `cleanup()` to free memory after use
10. **Add Expected Responses**: Include expected responses for verification

### Guidelines for Executing Sequences

1. **Start Small**: Begin with simple sequences to verify basic functionality
2. **Use Timeouts**: Always use timeouts to detect stalled transactions
3. **Verify Completion**: Check that all transactions have completed
4. **Monitor Statistics**: Track performance metrics to detect issues
5. **Use Protocol Checking**: Enable protocol validation during testing
6. **Batch Large Sequences**: Process large sequences in manageable batches
7. **Track Coverage**: Use coverage tracking to ensure thorough testing
8. **Enable Detailed Logging**: Start with verbose logging for debugging
9. **Visualize Complex Sequences**: Use visualization for complex test scenarios
10. **Check Error Counts**: Always verify error counts after execution

### Testbench Integration Tips

1. **Separate Sequence Generation from Execution**: Create sequences independently from their execution
2. **Use Command Handlers**: Leverage command handlers for coordination
3. **Add Multiple Monitors**: Monitor both master and slave sides
4. **Create Reusable Components**: Build a library of common sequences
5. **Add Coverage Callbacks**: Register coverage callbacks with monitors
6. **Use Memory Models**: Connect memory models to slaves for validation
7. **Create Test Libraries**: Organize tests into libraries by functionality
8. **Parameterize Tests**: Make tests configurable for different scenarios
9. **Automate Regression Testing**: Create a framework for running sequence batches
10. **Document Test Coverage**: Map sequences to verification requirements

### Debug Recommendations

1. **Use Signal Dumping**: Enable waveform dumping for detailed analysis
2. **Enable Detailed Logging**: Set log level to DEBUG for more information
3. **Track Transaction IDs**: Trace specific transactions through the system
4. **Visualize Dependencies**: Create dependency diagrams for complex sequences
5. **Check for Timeouts**: Watch for transactions that never complete
6. **Verify Protocol Parameters**: Double-check burst parameters are valid
7. **Check Address Calculations**: Verify burst address calculations are correct
8. **Isolate Problems**: Run problematic sequences in isolation
9. **Simplify Complex Sequences**: Reduce complexity to identify issues
10. **Compare with Reference Model**: Validate against a reference implementation

### Performance Optimization Tips

1. **Use Parallelism**: Enable concurrent processing of multiple channels
2. **Set Proper Queue Depths**: Adjust queue depths based on transaction patterns
3. **Manage Memory Usage**: Clean up completed transactions
4. **Batch Processing**: Process transactions in batches
5. **Optimize Randomization**: Use targeted randomization for better coverage
6. **Address Alignment**: Ensure proper address alignment for optimal performance
7. **Use Multiple IDs**: Leverage multiple IDs for parallel transactions
8. **Pipeline Transactions**: Overlap address and data phases
9. **Prioritize Channels**: Set appropriate channel priorities
10. **Limit Unnecessary Dependencies**: Only add dependencies when needed
