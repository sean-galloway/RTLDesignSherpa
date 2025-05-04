# AXI4 Protocol Extensions Documentation

## Introduction

AXI4 Protocol Extensions enhance the base AXI4 protocol with additional functionality for specialized use cases. This document details the protocol extensions supported by the AXI4 verification environment, including Quality of Service (QoS), exclusive access, atomic operations, and barrier transactions.

## Extension Handlers

The AXI4 verification environment provides extension handlers for each protocol feature:

1. **QoSHandler**: Manages Quality of Service prioritization
2. **ExclusiveAccessHandler**: Controls exclusive access operations
3. **AtomicOperationHandler**: Implements atomic memory operations
4. **BarrierHandler**: Enforces transaction ordering across barriers

### Creating Extension Handlers

Extension handlers can be created individually or as a complete set:

```python
from axi4_extensions import create_axi4_extension_handlers

# Create all extension handlers
extensions = create_axi4_extension_handlers(
    memory_model=memory_model,
    log=logger
)

# Access individual handlers
qos_handler = extensions['qos']
exclusive_handler = extensions['exclusive']
atomic_handler = extensions['atomic']
barrier_handler = extensions['barrier']
```

### Integrating Extensions with Components

Extensions can be used with AXI4 Master and Slave components:

```python
# Create master with extensions
master = create_axi4_master(
    dut=dut,
    title="master",
    prefix="m_axi",
    divider="_",
    suffix="",
    clock=dut.clk,
    channels=["AW", "W", "B", "AR", "R"],
    extensions=extensions
)

# Create slave with extensions
slave = create_axi4_slave(
    dut=dut,
    title="slave",
    prefix="s_axi",
    divider="_",
    suffix="",
    clock=dut.clk,
    channels=["AW", "W", "B", "AR", "R"],
    memory_model=memory_model,
    extensions=extensions
)
```

### Extended AXI4 Master

For more direct access to extension features:

```python
from axi4_extensions import ExtendedAXI4Master

# Create extended master
extended_master = ExtendedAXI4Master(
    master=standard_master,
    extensions=extensions,
    log=logger
)
```

## Quality of Service (QoS)

The Quality of Service extension provides prioritization of transactions based on QoS values.

### QoSHandler Configuration

```python
# Configure QoS handler
qos_handler = extensions['qos']

# Set number of priority levels (default is 16)
qos_handler = QoSHandler(num_priority_levels=16)

# Set starvation threshold to prevent lower priorities from being starved
qos_handler.starvation_threshold = 20

# Set starvation priority bump (how many levels to promote starved transactions)
qos_handler.starvation_bump = 4
```

### Using QoS Values in Transactions

```python
# Write with QoS priority
result = await master.write(
    addr=0x1000,
    data=0xDEADBEEF,
    qos=8,                   # QoS value (0-15, higher is higher priority)
    id=0
)

# Read with QoS priority
result = await master.read(
    addr=0x1000,
    qos=8,                   # QoS value (0-15)
    id=0
)
```

### QoS Prioritization

Transactions with higher QoS values will be processed before transactions with lower QoS values:

```python
# Queue transactions with different QoS values
await master.write(addr=0x1000, data=0x1, qos=0)    # Low priority
await master.write(addr=0x2000, data=0x2, qos=15)   # Highest priority
await master.write(addr=0x3000, data=0x3, qos=8)    # Medium priority
```

The QoS handler processes these transactions in QoS order: QoS=15 first, then QoS=8, then QoS=0.

### QoS Statistics

```python
# Get QoS statistics
stats = qos_handler.get_stats()

# Example statistics:
# - write_queue_sizes: Queue sizes for each priority level
# - read_queue_sizes: Queue sizes for each priority level
# - write_counters: Counters for starvation detection
# - read_counters: Counters for starvation detection
```

## Exclusive Access

The exclusive access extension implements AXI4 exclusive access operations for atomic read-modify-write transactions.

### ExclusiveAccessHandler Configuration

```python
# Configure exclusive access handler
exclusive_handler = extensions['exclusive']

# Register memory regions for exclusive access
exclusive_handler.register_exclusive_region(
    start_address=0x1000,
    end_address=0x1FFF
)
```

### Performing Exclusive Access Operations

With standard master:

```python
# Exclusive read
result = await master.exclusive_read(
    addr=0x1000,
    size=2,                   # Size: 0=byte, 1=halfword, 2=word, 3=doubleword
    id=0
)

# Exclusive write (returns success/failure)
result = await master.exclusive_write(
    addr=0x1000,
    data=0xDEADBEEF,
    size=2,
    id=0
)
exclusive_success = result['exclusive_success']
```

With extended master:

```python
# Exclusive read
result = await extended_master.exclusive_read(
    addr=0x1000,
    size=2,
    id=0
)

# Exclusive write
result = await extended_master.exclusive_write(
    addr=0x1000,
    data=0xDEADBEEF,
    size=2,
    id=0
)
```

### Exclusive Access Pattern

The correct sequence for exclusive access is:

1. Perform an exclusive read (sets up exclusive monitor)
2. Modify the data
3. Perform an exclusive write to the same address
4. Check the response to determine success/failure

```python
# Complete exclusive access pattern
read_result = await master.exclusive_read(addr=0x1000, size=2, id=0)
old_value = read_result['data'][0]
new_value = old_value + 1  # Increment value

write_result = await master.exclusive_write(addr=0x1000, data=new_value, size=2, id=0)
if write_result['exclusive_success']:
    print("Exclusive access succeeded")
else:
    print("Exclusive access failed")
```

### Exclusive Access Statistics

```python
# Get exclusive access statistics
stats = exclusive_handler.get_stats()

# Example statistics:
# - exclusive_reads: Number of exclusive reads
# - exclusive_writes: Number of exclusive writes
# - successful_exclusive_writes: Number of successful exclusive writes
# - failed_exclusive_writes: Number of failed exclusive writes
# - active_monitors: Number of active exclusive monitors
```

## Atomic Operations

The atomic operations extension implements atomic memory operations like add, swap, and compare-and-swap.

### AtomicOperationHandler

```python
# Access atomic operation handler
atomic_handler = extensions['atomic']
```

### Atomic Operation Types

Available atomic operation types:

- **ATOMIC_ADD**: Add value to memory
- **ATOMIC_SWAP**: Replace memory with value
- **ATOMIC_COMPARE_SWAP**: Replace if memory matches compare_value
- **ATOMIC_MIN**: Write minimum of memory and value
- **ATOMIC_MAX**: Write maximum of memory and value
- **ATOMIC_AND**: Bitwise AND with memory
- **ATOMIC_OR**: Bitwise OR with memory
- **ATOMIC_XOR**: Bitwise XOR with memory

### Performing Atomic Operations

```python
# Atomic add operation
success, old_value = await extended_master.atomic_operation(
    op_type=atomic_handler.ATOMIC_ADD,  # Operation type
    addr=0x1000,                        # Target address
    value=1,                            # Value to add
    id=0
)

# Atomic swap operation
success, old_value = await extended_master.atomic_operation(
    op_type=atomic_handler.ATOMIC_SWAP,
    addr=0x1000,
    value=0xDEADBEEF,
    id=0
)

# Compare and swap operation
success, old_value = await extended_master.atomic_operation(
    op_type=atomic_handler.ATOMIC_COMPARE_SWAP,
    addr=0x1000,
    value=0xDEADBEEF,                  # New value
    compare_value=0x12345678,          # Expected current value
    id=0
)
```

### Atomic Operation Example

```python
# Atomic increment operation
success, old_value = await extended_master.atomic_operation(
    op_type=atomic_handler.ATOMIC_ADD,
    addr=0x1000,
    value=1,
    id=0
)

if success:
    print(f"Successfully incremented value from {old_value} to {old_value + 1}")
else:
    print("Atomic operation failed")
```

### Atomic Operation Statistics

```python
# Get atomic operation statistics
stats = atomic_handler.get_stats()

# Example statistics:
# - operations: Counts of each type of operation
# - successful_operations: Number of successful operations
# - failed_operations: Number of failed operations
```

## Barrier Transactions

The barrier extension enforces ordering between transactions, ensuring that certain transactions complete before others begin.

### BarrierHandler

```python
# Access barrier handler
barrier_handler = extensions['barrier']
```

### Barrier Types

Available barrier types:

- **BARRIER_MEMORY**: Memory barrier
- **BARRIER_DEVICE**: Device barrier
- **BARRIER_SYSTEM**: System barrier

### Creating and Using Barriers

```python
# Create a barrier
barrier_id = await extended_master.create_barrier(
    barrier_type=barrier_handler.BARRIER_MEMORY
)

# Order transactions with respect to barrier
await extended_master.order_transaction_before_barrier(
    barrier_id=barrier_id,
    transaction_id=tx_id1
)

await extended_master.order_transaction_after_barrier(
    barrier_id=barrier_id,
    transaction_id=tx_id2
)

# Mark a transaction as complete (normally done by component automatically)
await extended_master.complete_transaction(transaction_id=tx_id1)
```

### Barrier Example

```python
# Create transactions and a barrier to enforce ordering
write_id1 = await master.execute_write_transaction(
    addr=0x1000,
    data_values=[0x11111111]
)

# Create a barrier
barrier_id = await extended_master.create_barrier(
    barrier_type=barrier_handler.BARRIER_MEMORY
)

# First write must complete before barrier
await extended_master.order_transaction_before_barrier(
    barrier_id=barrier_id,
    transaction_id=write_id1
)

# Second write must start after barrier
write_id2 = await master.execute_write_transaction(
    addr=0x2000,
    data_values=[0x22222222]
)
await extended_master.order_transaction_after_barrier(
    barrier_id=barrier_id,
    transaction_id=write_id2
)
```

### Barrier Statistics

```python
# Get barrier statistics
stats = barrier_handler.get_stats()

# Example statistics:
# - barriers_created: Number of barriers created
# - barriers_completed: Number of barriers completed
# - transactions_ordered: Number of transactions ordered with barriers
# - active_barriers: Number of active barriers
```

## Combined Protocol Extensions

### Implementing a Lock-Free Counter

This example shows how to implement a thread-safe counter using atomic operations:

```python
async def increment_counter(master, address, count=1):
    atomic_handler = master.extensions['atomic']
    
    success, old_value = await master.atomic_operation(
        op_type=atomic_handler.ATOMIC_ADD,
        addr=address,
        value=count,
        id=0
    )
    
    return success, old_value, old_value + count

# Usage
success, old_value, new_value = await increment_counter(extended_master, 0x1000)
```

### Exclusive Access with Retry

This example shows how to implement an exclusive operation with retry on failure:

```python
async def atomic_update(master, address, update_function, max_retries=3):
    """Perform an atomic update with retry on failure"""
    for attempt in range(max_retries):
        # Exclusive read
        read_result = await master.exclusive_read(
            addr=address,
            size=2,
            id=0
        )
        
        old_value = read_result['data'][0]
        new_value = update_function(old_value)
        
        # Exclusive write
        write_result = await master.exclusive_write(
            addr=address,
            data=new_value,
            size=2,
            id=0
        )
        
        if write_result['exclusive_success']:
            return True, old_value, new_value
    
    # Failed after max retries
    return False, None, None

# Usage - Increment a value
success, old_value, new_value = await atomic_update(master, 0x1000, lambda x: x + 1)
```

### Memory Barrier for Cache Flush

This example uses a memory barrier to ensure cache operations complete:

```python
async def flush_cache_with_barrier(master, cache_control_addr, memory_addr):
    """Flush cache and ensure memory access sees the flush"""
    # Write to cache control register to initiate flush
    write_id = await master.execute_write_transaction(
        addr=cache_control_addr,
        data_values=[0x1]  # Flush command
    )
    
    # Create memory barrier
    barrier_id = await extended_master.create_barrier(
        barrier_type=barrier_handler.BARRIER_MEMORY
    )
    
    # Flush must complete before barrier
    await extended_master.order_transaction_before_barrier(
        barrier_id=barrier_id,
        transaction_id=write_id
    )
    
    # Memory access must start after barrier
    read_id = await master.execute_read_transaction(
        addr=memory_addr,
        burst_len=0
    )
    
    await extended_master.order_transaction_after_barrier(
        barrier_id=barrier_id,
        transaction_id=read_id
    )
    
    # Return read data
    return read_id[1]  # Data values
```

### Priority-Based Transaction Processing

This example uses QoS to implement priority-based transaction processing:

```python
async def perform_prioritized_operations(master, operations):
    """Execute operations based on priority"""
    results = []
    
    # Group operations by priority
    for priority, addr, is_write, data in operations:
        qos = min(max(priority, 0), 15)  # Clamp to 0-15
        
        if is_write:
            result = await master.write(
                addr=addr,
                data=data,
                qos=qos,
                id=0
            )
        else:
            result = await master.read(
                addr=addr,
                qos=qos,
                id=0
            )
        
        results.append(result)
    
    return results

# Usage
operations = [
    (15, 0x1000, True, 0x1),  # High priority write
    (8, 0x2000, False, None),  # Medium priority read
    (0, 0x3000, True, 0x3)    # Low priority write
]
results = await perform_prioritized_operations(master, operations)
```

## Extension Statistics and Monitoring

All extension handlers provide statistics through their `get_stats()` method:

```python
# Get statistics from all extensions
def print_extension_stats(extensions):
    for name, handler in extensions.items():
        if hasattr(handler, 'get_stats'):
            stats = handler.get_stats()
            print(f"{name.upper()} Extension Statistics:")
            for key, value in stats.items():
                print(f"  {key}: {value}")
            print()

# Get statistics from master
stats = extended_master.get_extension_stats()
```

## Combining Extensions for Complex Operations

This example shows a complex operation using multiple extensions:

```python
async def complex_operation(master, data_addr, flag_addr):
    """Perform a complex operation using multiple extensions"""
    # Read current data with QoS=8
    read_result = await master.read(
        addr=data_addr,
        qos=8,
        id=0
    )
    current_data = read_result['data'][0]
    
    # Create a barrier
    barrier_id = await extended_master.create_barrier(
        barrier_type=barrier_handler.BARRIER_MEMORY
    )
    
    # Modify data atomically
    atomic_handler = master.extensions['atomic']
    success, old_value = await extended_master.atomic_operation(
        op_type=atomic_handler.ATOMIC_ADD,
        addr=data_addr,
        value=1,
        id=1
    )
    
    # Order transactions with barrier
    await extended_master.order_transaction_before_barrier(
        barrier_id=barrier_id,
        transaction_id=1
    )
    
    # Set flag after data modification (with highest QoS)
    write_id = await master.write(
        addr=flag_addr,
        data=1,
        qos=15,
        id=2
    )
    
    await extended_master.order_transaction_after_barrier(
        barrier_id=barrier_id,
        transaction_id=2
    )
    
    return success, old_value, old_value + 1
```

## Conclusion

AXI4 Protocol Extensions provide powerful capabilities for advanced SoC designs and verification. By leveraging Quality of Service, exclusive access, atomic operations, and barriers, you can implement complex system behaviors and verify their correctness.

These extensions integrate seamlessly with the AXI4 verification environment, allowing you to create sophisticated test scenarios that cover the full range of AXI4 protocol features. The extension handlers provide a clean, object-oriented interface for using these features, with comprehensive statistics and monitoring capabilities for debugging and performance analysis.

By using these extensions effectively, you can ensure that your AXI4 implementation properly handles the advanced features of the protocol, leading to robust and reliable system designs.

## Navigation

[↑ AXI4 Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
