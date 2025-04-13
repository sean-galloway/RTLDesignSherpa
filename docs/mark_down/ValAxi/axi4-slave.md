# AXI4 Slave Component Documentation

## Introduction

The AXI4 Slave component acts as a responder in the AXI4 environment, processing requests from master components and generating appropriate responses. It receives transactions on the AW (Write Address), W (Write Data), and AR (Read Address) channels, and drives responses on the B (Write Response) and R (Read Data) channels. This document covers the configuration and usage of the AXI4 Slave component.

## Architecture

The AXI4 Slave integrates multiple channel components into a coordinated response engine:

- **AW Channel Slave**: Receives write address transactions
- **W Channel Slave**: Receives write data transactions
- **B Channel Master**: Drives write response transactions
- **AR Channel Slave**: Receives read address transactions
- **R Channel Master**: Drives read data transactions

The slave component handles coordination between these channels, manages transaction queues, and implements response ordering strategies for adhering to the AXI4 protocol.

## Instantiation

### Basic Instantiation

To create an AXI4 Slave, use the factory function:

```python
from axi4_factory import create_axi4_slave

slave = create_axi4_slave(
    dut=dut,                 # Device under test
    title="my_axi4_slave",   # Component name
    prefix="s_axi",          # Signal prefix
    divider="_",             # Signal divider
    suffix="",               # Signal suffix
    clock=dut.clk,           # Clock signal
    channels=["AW", "W", "B", "AR", "R"],  # Channels to instantiate
    id_width=8,              # ID width in bits
    addr_width=32,           # Address width in bits
    data_width=32,           # Data width in bits
    user_width=1,            # User signal width in bits
    memory_model=memory,     # Memory model for data storage
    check_protocol=True,     # Enable protocol checking
    inorder=False,           # Allow out-of-order responses
    ooo_strategy='random',   # Out-of-order strategy
    log=logger               # Logger instance
)
```

### Memory-Based Slave Instantiation

For a slave that automatically manages memory operations:

```python
from axi4_factory_specialized import create_memory_axi4_slave
from CocoTBFramework.memory_models import SimpleMemoryModel

# Create a memory model
memory = SimpleMemoryModel(size=0x10000, byte_width=4)

# Create a slave with memory model
slave = create_memory_axi4_slave(
    dut=dut,                 # Device under test
    title="memory_slave",    # Component name
    prefix="s_axi",          # Signal prefix
    clock=dut.clk,           # Clock signal
    memory_model=memory,     # Memory model
    data_width=32,           # Data width in bits
    log=logger               # Logger instance
)
```

## Basic Operations

Unlike the AXI4 Master which actively drives transactions, the AXI4 Slave is primarily reactive. Its main operation is to process incoming transactions and generate responses according to the AXI4 protocol.

### Starting the Processor

The slave component needs its internal transaction processor running to handle requests:

```python
# Start the transaction processor
await slave.start_processor()

# Later, when done:
await slave.stop_processor()
```

### Reset

To reset the slave:

```python
await slave.reset_bus()
```

## Response Control

### Response Ordering

The AXI4 Slave supports different response ordering strategies:

```python
# Configure for in-order responses
slave.inorder = True

# Configure for out-of-order responses
slave.inorder = False
slave.ooo_strategy = 'random'  # Options: 'random', 'round_robin', 'weighted'
```

### Response Weighting

For the 'weighted' out-of-order strategy, you can assign different weights to transaction IDs:

```python
# Give higher priority to transactions with ID=3
slave.set_ooo_weight(id_value=3, weight=2.0)
```

Higher weights increase the probability of selecting those transactions for response.

## Memory Model Interface

When a memory model is attached to the slave, it automatically handles read and write operations:

### Automatic Memory Operations

The slave will:
1. For writes: Store data at the specified address when W channel transactions are received
2. For reads: Retrieve data from the specified address and return it in R channel responses

### Manual Memory Access

You can also directly access the memory model:

```python
# Access memory directly
data = slave.memory_model.read(address=0x1000, size=4)
slave.memory_model.write(address=0x2000, data=bytearray([0xDE, 0xAD, 0xBE, 0xEF]), mask=0xFF)
```

## Advanced Features

### Exclusive Access Regions

To designate memory regions for exclusive access:

```python
await slave.register_exclusive_region(
    start_address=0x1000,
    end_address=0x1FFF
)
```

Exclusive access operations within these regions will be monitored and enforced according to the AXI4 protocol.

### Protocol Extensions

The slave supports various protocol extensions:

#### Quality of Service (QoS)

QoS values from incoming transactions are respected when determining response order. Higher QoS values result in higher response priority.

#### Exclusive Access Handling

The slave automatically handles exclusive access operations:
1. Monitors exclusive reads
2. Validates exclusive writes
3. Returns appropriate response codes (OKAY or EXOKAY)

#### Atomic Operations

If configured, atomic operations are processed by the atomic extension handler.

#### Barrier Transactions

If configured, barrier transactions are respected for transaction ordering.

## Response Customization

### Error Responses

You can configure the slave to return error responses for specific addresses:

```python
# Configure a memory region to return SLVERR
slave.extensions['error_handler'].register_error_region(
    start_address=0xF000,
    end_address=0xFFFF,
    response_code=2  # SLVERR
)
```

Response codes:
- `0`: OKAY - Normal successful completion
- `1`: EXOKAY - Exclusive access success
- `2`: SLVERR - Slave error
- `3`: DECERR - Decode error

## Statistics and Monitoring

To get statistics from the slave:

```python
# Get extension statistics
stats = slave.get_extension_stats()

# Example statistics:
# - QoS queue sizes and priorities
# - Exclusive access counts (reads, writes, successes, failures)
# - Atomic operation counts by type
# - Barrier counts and states
```

## Implementation Details

### Transaction Processing Flow

1. **Write Processing**:
   - AW transaction received → Stored in `pending_writes`
   - W transactions received → Matched with AW by ID, stored in `pending_writes`
   - When all W beats received → Write to memory model
   - B response queued → Sent according to ordering strategy

2. **Read Processing**:
   - AR transaction received → Stored in `pending_reads`
   - Read from memory model → R responses generated
   - R responses queued → Sent according to ordering strategy

### Response Ordering Strategies

1. **In-Order**: Responses are sent in the same order as requests were received, across all IDs
2. **Random**: Responses are sent in random order between different IDs (but in order within each ID)
3. **Round-Robin**: Each ID is serviced in rotation
4. **Weighted**: IDs are selected based on assigned weights and QoS values

## Example Usage

Here's a complete example of setting up and using the AXI4 Slave:

```python
async def setup_slave(dut):
    # Create memory model
    memory = SimpleMemoryModel(size=0x10000, byte_width=4)
    
    # Create slave with memory model
    slave = create_memory_axi4_slave(
        dut=dut,
        title="memory_slave",
        prefix="s_axi",
        clock=dut.clk,
        memory_model=memory,
        data_width=32,
        log=logger
    )
    
    # Configure response behavior
    slave.inorder = False
    slave.ooo_strategy = 'weighted'
    
    # Set weights for different transaction IDs
    slave.set_ooo_weight(id_value=0, weight=1.0)  # Normal priority
    slave.set_ooo_weight(id_value=1, weight=2.0)  # High priority
    
    # Register exclusive access region
    await slave.register_exclusive_region(
        start_address=0x2000,
        end_address=0x2FFF
    )
    
    # Reset and start
    await slave.reset_bus()
    await slave.start_processor()
    
    return slave, memory
```

## Custom Response Handling

For more complex scenarios where the default memory model behavior isn't sufficient, you can add custom callbacks:

```python
# Custom handling for AW transactions
def custom_aw_handler(transaction):
    addr = transaction.awaddr
    id_value = transaction.awid
    
    # Custom logic here
    
# Register the callback
slave.aw_slave.add_callback(custom_aw_handler)
```

## Troubleshooting

Common issues and their solutions:

1. **Missing responses**: Ensure the slave processor is started with `await slave.start_processor()`

2. **Protocol violations**: Check the configuration of the slave, particularly address alignment and burst parameters

3. **Memory access errors**: Verify the memory model is properly sized and initialized

4. **Performance bottlenecks**: Consider using out-of-order responses (`inorder=False`) for higher throughput

5. **Exclusive access failures**: Ensure exclusive regions are properly registered and that masters follow the correct sequence (read then write)

6. **QoS handling issues**: Verify that QoS values are properly set in master transactions
