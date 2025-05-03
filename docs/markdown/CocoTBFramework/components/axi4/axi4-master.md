# AXI4 Master Component Documentation

## Introduction

The AXI4 Master component is responsible for initiating transactions on the AXI4 bus. It drives the AW (Write Address), W (Write Data), and AR (Read Address) channels, and receives responses on the B (Write Response) and R (Read Data) channels. This document details how to configure and use the AXI4 Master component for verification.

## Architecture

The AXI4 Master integrates multiple channel components into a coordinated transaction engine:

- **AW Channel Master**: Drives write address transactions
- **W Channel Master**: Drives write data transactions
- **B Channel Slave**: Receives write response transactions
- **AR Channel Master**: Drives read address transactions
- **R Channel Slave**: Receives read data transactions

The master component handles coordination between these channels, ensuring correct transaction sequencing and protocol compliance.

## Instantiation

### Basic Instantiation

To create an AXI4 Master, use the factory function:

```python
from axi4_factory import create_axi4_master

master = create_axi4_master(
    dut=dut,                 # Device under test
    title="my_axi4_master",  # Component name
    prefix="m_axi",          # Signal prefix
    divider="_",             # Signal divider
    suffix="",               # Signal suffix
    clock=dut.clk,           # Clock signal
    channels=["AW", "W", "B", "AR", "R"],  # Channels to instantiate
    id_width=8,              # ID width in bits
    addr_width=32,           # Address width in bits
    data_width=32,           # Data width in bits
    user_width=1,            # User signal width in bits
    log=logger               # Logger instance
)
```

### Simplified Instantiation

For basic testing, a simplified creation function is available:

```python
from axi4_factory_specialized import create_simple_axi4_master

master = create_simple_axi4_master(
    dut=dut,                 # Device under test
    title="my_axi4_master",  # Component name
    prefix="m_axi",          # Signal prefix
    clock=dut.clk,           # Clock signal
    data_width=32,           # Data width in bits
    log=logger               # Logger instance
)
```

This creates a master with sensible default settings for simple test cases.

## Basic Operations

### Write Transaction

To perform a write transaction:

```python
# Single beat write
result = await master.write(
    addr=0x1000,             # Target address
    data=0xDEADBEEF,         # Data to write
    size=2,                  # Size: 0=byte, 1=halfword, 2=word, 3=doubleword
    burst=1,                 # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    id=0                     # Transaction ID
)

# Multi-beat burst write
result = await master.write(
    addr=0x2000,
    data=[0x11111111, 0x22222222, 0x33333333, 0x44444444],
    size=2,                  # Word size
    burst=1,                 # INCR burst
    id=1
)
```

### Read Transaction

To perform a read transaction:

```python
# Single beat read
result = await master.read(
    addr=0x1000,             # Target address
    size=2,                  # Size: 0=byte, 1=halfword, 2=word, 3=doubleword
    burst=1,                 # Burst type: 0=FIXED, 1=INCR, 2=WRAP
    id=0                     # Transaction ID
)
read_data = result['data'][0]  # Extract data from response

# Multi-beat burst read
result = await master.read(
    addr=0x2000,
    size=2,                  # Word size
    burst=1,                 # INCR burst
    length=3,                # 4 beats (length=N means N+1 beats)
    id=1
)
read_data = result['data']   # List of data values
```

### Transaction Results

The transaction methods return result dictionaries containing:

- **For writes**:
  - `aw_packet`: Write address packet
  - `w_packets`: List of write data packets
  - `response`: Write response packet (B channel)
  - `start_time`: Transaction start time
  - `end_time`: Transaction end time
  - `duration`: Transaction duration
  - `exclusive_success`: Boolean indicating exclusive access success (if applicable)

- **For reads**:
  - `ar_packet`: Read address packet
  - `responses`: List of read data packets (R channel)
  - `data`: List of read data values (for convenience)
  - `start_time`: Transaction start time
  - `end_time`: Transaction end time
  - `duration`: Transaction duration

## Advanced Features

### Exclusive Access

For exclusive access operations:

```python
# Exclusive read
result = await master.exclusive_read(
    addr=0x1000,
    size=2,
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

### Atomic Operations

For atomic operations (add, swap, compare-and-swap, etc.):

```python
success, old_value = await master.atomic_operation(
    op_type=master.extensions['atomic'].ATOMIC_ADD,  # Operation type
    addr=0x1000,                                     # Target address
    value=1,                                         # Value to add
    id=0
)
```

Available operation types:
- `ATOMIC_ADD`: Add value to memory
- `ATOMIC_SWAP`: Replace memory with value
- `ATOMIC_COMPARE_SWAP`: Replace if memory matches compare_value
- `ATOMIC_MIN`: Write minimum of memory and value
- `ATOMIC_MAX`: Write maximum of memory and value
- `ATOMIC_AND`: Bitwise AND with memory
- `ATOMIC_OR`: Bitwise OR with memory
- `ATOMIC_XOR`: Bitwise XOR with memory

### Quality of Service (QoS)

To specify QoS priority for transactions:

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

### Barrier Transactions

To create transaction barriers for ordering:

```python
# Create a barrier
barrier_id = await master.create_barrier(master.extensions['barrier'].BARRIER_MEMORY)

# Order transactions with respect to barrier
await master.order_transaction_before_barrier(barrier_id, transaction_id1)
await master.order_transaction_after_barrier(barrier_id, transaction_id2)

# Mark a transaction as complete
await master.complete_transaction(transaction_id1)
```

Barrier types:
- `BARRIER_MEMORY`: Memory barrier
- `BARRIER_DEVICE`: Device barrier
- `BARRIER_SYSTEM`: System barrier

## Transaction Sequences

For more complex test scenarios, you can use transaction sequences:

```python
# Execute a write transaction and add it to the sequence
tx_id = await master.execute_write_transaction(
    addr=0x1000,
    data_values=[0x11111111, 0x22222222],
    burst_type=1             # INCR
)

# Execute a read transaction and add it to the sequence
tx_id, data_values = await master.execute_read_transaction(
    addr=0x1000,
    burst_len=1,             # 2 beats
    dependencies=[tx_id]     # Make read depend on previous write
)
```

## Protocol Customization

### Burst Types

AXI4 supports three burst types:
- `0`: FIXED - Address remains fixed for all transfers
- `1`: INCR - Address increments after each transfer
- `2`: WRAP - Address increments and wraps at boundaries

### Protection Types

Protection attributes allow different access types:
- Bit 0: `0`=Unprivileged, `1`=Privileged
- Bit 1: `0`=Secure, `1`=Non-secure
- Bit 2: `0`=Data, `1`=Instruction

### Cache Types

Cache attributes control memory behavior:
- `0000`: Device Non-bufferable
- `0001`: Device Bufferable
- `0010`: Normal Non-cacheable Non-bufferable
- `0011`: Normal Non-cacheable Bufferable
- `01xx`: Write-through
- `10xx`: Write-back
- `11xx`: Write-back with read and write allocate

## Reset and Cleanup

To reset the master:

```python
await master.reset_bus()
```

## Statistics and Monitoring

To get statistics from extensions:

```python
stats = master.get_extension_stats()
```

This returns information such as:
- Transaction counts
- QoS queue statistics
- Exclusive access statistics
- Atomic operation statistics

## Example Test Sequence

Here's a complete example of a test sequence using the AXI4 Master:

```python
async def run_test(dut):
    # Create master
    master = create_simple_axi4_master(dut, "master", "m_axi", dut.clk)
    
    # Reset
    await master.reset_bus()
    
    # Perform a write
    write_result = await master.write(
        addr=0x1000,
        data=[0xA1A1A1A1, 0xB2B2B2B2, 0xC3C3C3C3, 0xD4D4D4D4],
        size=2,
        burst=1,
        id=0
    )
    
    # Perform a read to the same address
    read_result = await master.read(
        addr=0x1000,
        size=2,
        burst=1,
        length=3,
        id=1
    )
    
    # Check the results
    assert read_result['data'] == [0xA1A1A1A1, 0xB2B2B2B2, 0xC3C3C3C3, 0xD4D4D4D4]
    
    # Try exclusive access
    ex_read_result = await master.exclusive_read(
        addr=0x2000,
        size=2,
        id=2
    )
    
    ex_write_result = await master.exclusive_write(
        addr=0x2000,
        data=0xE5E5E5E5,
        size=2,
        id=2
    )
    
    if ex_write_result['exclusive_success']:
        print("Exclusive write succeeded")
    else:
        print("Exclusive write failed")
```

## Troubleshooting

Common issues and their solutions:

1. **Timeout waiting for response**: Check if the slave is properly responding. If using a real RTL design, ensure it's properly configured.

2. **Protocol violation errors**: Check the transaction parameters for compliance with AXI4 rules, particularly address alignment, burst length, and burst type combinations.

3. **Data mismatches**: Verify the data width, strobe settings, and endianness.

4. **Performance issues**: For bandwidth-intensive tests, consider using the `create_performance_test_environment` function to set up specialized components.
