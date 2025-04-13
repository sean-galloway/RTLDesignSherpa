# AXI4 Scoreboard Component Documentation

## Introduction

The AXI4 Scoreboard is a verification component responsible for checking the correctness of AXI4 transactions. It compares expected transaction data with actual observed data to detect discrepancies. This document details how to configure and use the AXI4 Scoreboard for effective verification.

## Scoreboard Types

The AXI4 verification environment provides two types of scoreboards:

1. **AXI4Scoreboard**: Basic scoreboard for comparing individual transactions
2. **AXI4MemoryScoreboard**: Extended scoreboard that uses a memory model for expected data

## Basic Scoreboard Instantiation

### Creating a Basic Scoreboard

```python
from axi4_factory import create_axi4_scoreboard

# Create a basic scoreboard
scoreboard = create_axi4_scoreboard(
    name="my_scoreboard",        # Scoreboard name
    id_width=8,                  # ID width in bits
    addr_width=32,               # Address width in bits
    data_width=32,               # Data width in bits
    user_width=1,                # User signal width in bits
    log=logger                   # Logger instance
)
```

### Creating a Memory-Based Scoreboard

```python
from axi4_factory import create_axi4_memory_scoreboard
from CocoTBFramework.memory_models import SimpleMemoryModel

# Create a memory model
memory = SimpleMemoryModel(size=0x10000, byte_width=4)

# Create a memory-based scoreboard
memory_scoreboard = create_axi4_memory_scoreboard(
    name="memory_scoreboard",    # Scoreboard name
    memory_model=memory,         # Memory model for expected data
    id_width=8,                  # ID width in bits
    addr_width=32,               # Address width in bits
    data_width=32,               # Data width in bits
    user_width=1,                # User signal width in bits
    log=logger                   # Logger instance
)
```

## Connecting to Monitors

The scoreboard should be connected to AXI4 Monitors to receive transaction data:

```python
# Connect monitor to scoreboard
monitor.set_write_callback(scoreboard.check_write)
monitor.set_read_callback(scoreboard.check_read)
```

## Basic Scoreboard Operations

### Adding Expected Write Transactions

For the basic scoreboard, you need to add expected write transactions:

```python
# Add expected write transaction
scoreboard.add_expected_write(
    id_value=0,                 # Transaction ID
    address=0x1000,             # Target address
    data=[0xDEADBEEF],          # Data values
    strobes=[0xF],              # Byte strobes
    burst_type=1,               # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    burst_size=2,               # Size (log2 of bytes)
    burst_len=0,                # Burst length (0 = 1 beat)
    resp=0                      # Expected response: 0=OKAY, 1=EXOKAY, etc.
)
```

### Adding Expected Read Transactions

```python
# Add expected read transaction
scoreboard.add_expected_read(
    id_value=0,                 # Transaction ID
    address=0x1000,             # Target address
    data=[0xDEADBEEF],          # Expected data values
    burst_type=1,               # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    burst_size=2,               # Size (log2 of bytes)
    burst_len=0,                # Burst length (0 = 1 beat)
    resp=0                      # Expected response: 0=OKAY, 1=EXOKAY, etc.
)
```

### Setting Expected Memory Values

For the memory-based scoreboard, you set expected values in the memory model:

```python
# Set expected value in memory
memory_scoreboard.memory_model.write(
    address=0x1000,
    data=bytearray([0xDE, 0xAD, 0xBE, 0xEF]),
    mask=0xFF
)
```

## Checking Transactions

The scoreboard automatically checks transactions when they are received through the callbacks:

### Write Transaction Checking

```python
# Check a write transaction (typically called by the monitor)
scoreboard.check_write(
    id_value=0,                  # Transaction ID
    transaction_info={           # Transaction information from monitor
        'aw_transaction': aw_packet,
        'w_transactions': w_packets,
        'b_transaction': b_packet,
        'addresses': addresses,
        'start_time': start_time,
        'end_time': end_time,
        'duration': duration,
        'complete': True
    }
)
```

### Read Transaction Checking

```python
# Check a read transaction (typically called by the monitor)
scoreboard.check_read(
    id_value=0,                  # Transaction ID
    transaction_info={           # Transaction information from monitor
        'ar_transaction': ar_packet,
        'r_transactions': r_packets,
        'addresses': addresses,
        'data': data_values,
        'start_time': start_time,
        'end_time': end_time,
        'duration': duration,
        'complete': True
    }
)
```

## Checking Results

To check the results of the verification:

```python
# Get error count
error_count = scoreboard.get_error_count()

# Get error messages
errors = scoreboard.get_errors()

# Print errors
for error in errors:
    print(f"Error: {error}")

# Check if verification passed
passed = (error_count == 0)
```

## Memory-Based Scoreboard Operations

The memory-based scoreboard automatically handles expected data through its memory model:

### Memory Access Methods

```python
# Write to memory model for expected values
memory_scoreboard.memory_model.write(
    address=0x1000,
    data=bytearray([0x11, 0x22, 0x33, 0x44]),
    mask=0xFF
)

# Read from memory model
data = memory_scoreboard.memory_model.read(
    address=0x1000,
    size=4
)
```

### Address Mapping

The memory-based scoreboard supports address mapping for cases where the AXI4 address space does not directly map to the memory model:

```python
# Set address mapping function
def my_address_mapper(axi_addr):
    # Convert AXI address to memory model address
    # For example, strip off the top bits
    return axi_addr & 0x0FFFFFFF

# Configure scoreboard with address mapper
memory_scoreboard.set_address_mapper(my_address_mapper)
```

## Advanced Configuration

### Checking Modes

The scoreboard supports different checking modes:

```python
# Configure checking modes
scoreboard.set_check_data(True)           # Check data values
scoreboard.set_check_response(True)       # Check response codes
scoreboard.set_check_id(True)             # Check transaction IDs
scoreboard.set_check_addr(True)           # Check addresses
scoreboard.set_check_burst_params(True)   # Check burst parameters
```

### Tolerance Settings

For performance testing, you can configure tolerance levels:

```python
# Configure tolerance levels
scoreboard.set_response_timeout(1000)     # Maximum time to wait for response (ns)
scoreboard.set_data_tolerance(0.0)        # Data value tolerance (0.0 = exact match)
scoreboard.set_timing_tolerance(100)      # Timing tolerance (ns)
```

### Burst Transaction Handling

For burst transactions, the scoreboard handles address generation based on burst parameters:

```python
# Configure burst handling
scoreboard.set_auto_calculate_addresses(True)  # Auto-calculate burst addresses
```

## Integration with Command Handler

For more complex verification scenarios, the scoreboard can be integrated with the AXI4CommandHandler:

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

# Create scoreboard with the same memory model
scoreboard = create_axi4_memory_scoreboard(
    name="memory_scoreboard",
    memory_model=memory_model,
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    log=logger
)

# Connect monitor to scoreboard
monitor.set_write_callback(scoreboard.check_write)
monitor.set_read_callback(scoreboard.check_read)

# Execute transactions and verify
await cmd_handler.start()
await cmd_handler.process_transaction_sequence(sequence)
```

## Example Usage

Here's a complete example of using the AXI4 Scoreboard:

```python
async def run_scoreboard_test(dut):
    # Create memory model
    memory = SimpleMemoryModel(size=0x10000, byte_width=4)
    
    # Create components
    master = create_simple_axi4_master(dut, "master", "m_axi", dut.clk)
    slave = create_memory_axi4_slave(dut, "slave", "s_axi", dut.clk, memory)
    monitor = create_axi4_monitor(dut, "monitor", "m_axi", dut.clk)
    
    # Create scoreboard
    scoreboard = create_axi4_memory_scoreboard(
        name="scoreboard",
        memory_model=memory,
        id_width=8,
        addr_width=32,
        data_width=32,
        user_width=1,
        log=logger
    )
    
    # Connect monitor to scoreboard
    monitor.set_write_callback(scoreboard.check_write)
    monitor.set_read_callback(scoreboard.check_read)
    
    # Start slave
    await slave.start_processor()
    
    # Initialize memory with expected values
    test_data = [0xA1A1A1A1, 0xB2B2B2B2, 0xC3C3C3C3, 0xD4D4D4D4]
    for i, data in enumerate(test_data):
        addr = 0x1000 + (i * 4)
        data_bytes = memory.integer_to_bytearray(data, 4)
        memory.write(addr, data_bytes, 0xF)
    
    # Execute transactions
    for i in range(10):
        addr = 0x1000 + (i * 16)
        
        # Write transaction
        await master.write(
            addr=addr,
            data=test_data,
            size=2,
            burst=1,
            id=i
        )
        
        # Wait a few cycles
        for _ in range(10):
            await RisingEdge(dut.clk)
        
        # Read transaction
        read_result = await master.read(
            addr=addr,
            size=2,
            burst=1,
            length=3,
            id=i + 10
        )
        
        # Manual check (in addition to scoreboard)
        assert read_result['data'] == test_data, f"Data mismatch at address 0x{addr:08X}"
    
    # Check final results
    error_count = scoreboard.get_error_count()
    if error_count > 0:
        print(f"Test failed with {error_count} errors:")
        for error in scoreboard.get_errors():
            print(f"  {error}")
    else:
        print("Test passed successfully")
    
    # Stop slave
    await slave.stop_processor()
    
    return error_count == 0
```

## Performance Considerations

For high-performance simulations, consider these optimizations:

1. **Disable Unnecessary Checks**: Disable checks that aren't needed for your verification scenario
2. **Use Memory-Based Scoreboard**: For large data transfers, the memory-based scoreboard is more efficient
3. **Batch Transactions**: Add expected transactions in batches rather than individually
4. **Increase Timeouts**: For heavy loads, increase response timeouts
5. **Consider Sampling**: For extremely large tests, consider checking only a sample of transactions

## Scoreboard Statistics

The scoreboard maintains statistics about the checked transactions:

```python
# Get scoreboard statistics
stats = scoreboard.get_stats()

print(f"Write Transactions Checked: {stats['write_transactions']}")
print(f"Read Transactions Checked: {stats['read_transactions']}")
print(f"Errors Detected: {stats['errors']}")
print(f"Warnings Generated: {stats['warnings']}")
```

## Memory Model Extensions

The memory model used by the memory-based scoreboard can be extended with additional capabilities:

### Custom Memory Model

```python
class MyCustomMemoryModel(SimpleMemoryModel):
    def __init__(self, size=0x10000, byte_width=4):
        super().__init__(size, byte_width)
        self.access_log = []
    
    def write(self, address, data, mask=0xFF):
        # Log access
        self.access_log.append(('write', address, data))
        # Call parent implementation
        super().write(address, data, mask)
    
    def read(self, address, size):
        # Log access
        self.access_log.append(('read', address, size))
        # Call parent implementation
        return super().read(address, size)
    
    def get_access_log(self):
        return self.access_log

# Create scoreboard with custom memory model
custom_memory = MyCustomMemoryModel()
scoreboard = create_axi4_memory_scoreboard(
    name="custom_scoreboard",
    memory_model=custom_memory,
    id_width=8,
    addr_width=32,
    data_width=32
)

# Later, check access log
access_log = custom_memory.get_access_log()
for access_type, address, data in access_log:
    print(f"{access_type.upper()} - Address: 0x{address:08X}, Data: {data}")
```

## AXI4 Protocol Checking

In addition to data checking, the scoreboard can perform protocol compliance checking:

```python
# Enable protocol checking
scoreboard.set_check_protocol(True)

# Configure protocol checking options
scoreboard.set_check_alignment(True)          # Check address alignment
scoreboard.set_check_exclusive(True)          # Check exclusive access sequence
scoreboard.set_check_response_codes(True)     # Check response code validity
scoreboard.set_check_burst_sequence(True)     # Check burst sequence validity
```

## Error Handling and Reporting

The scoreboard provides detailed error information:

```python
# Get errors by category
data_errors = scoreboard.get_errors_by_category("data")
response_errors = scoreboard.get_errors_by_category("response")
protocol_errors = scoreboard.get_errors_by_category("protocol")

# Get errors by severity
fatal_errors = scoreboard.get_errors_by_severity("fatal")
warning_errors = scoreboard.get_errors_by_severity("warning")

# Generate error report
report = scoreboard.generate_error_report()
print(report)
```

## Conclusion

The AXI4 Scoreboard is a powerful verification component that enables thorough checking of AXI4 transactions. By comparing expected and actual transactions, it detects discrepancies and protocol violations, helping ensure correct implementation of AXI4 interfaces.

The two scoreboard types (basic and memory-based) offer flexibility for different verification scenarios. The basic scoreboard is suitable for focused tests with specific expected values, while the memory-based scoreboard excels at large-scale tests with a consistent memory model.

By properly configuring and using the scoreboard in your testbench, you can achieve high confidence in the correctness of your AXI4 implementation.
