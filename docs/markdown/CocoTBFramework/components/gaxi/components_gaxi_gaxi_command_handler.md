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

# gaxi_command_handler.py

Enhanced GAXI command handler for transaction processing with sequential data generation and improved field extraction. This module provides a comprehensive command handler that bridges master and slave components, supporting both forwarding mode and response generation mode.

## Overview

The `gaxi_command_handler.py` module provides the `GAXICommandHandler` class, which manages transaction processing between GAXI masters and slaves. It offers two operational modes: forwarding mode (master→slave) and response generation mode (slave→master), with enhanced sequential data generation for predictable testing.

### Key Features
- **Dual operational modes**: Forwarding and response generation
- **Sequential data generation** for predictable read responses
- **Enhanced field extraction** supporting both APB and GAXI style packets
- **Memory model integration** with automatic fallback to sequential data
- **Comprehensive error handling** and recovery
- **Transaction dependency tracking** and ordering
- **Performance statistics** and latency measurement

## Core Class

### GAXICommandHandler

Enhanced command handler for GAXI transactions with comprehensive transaction processing capabilities.

#### Constructor

```python
GAXICommandHandler(master, slave, memory_model=None, log=None,
                   response_generation_mode=False, **kwargs)
```

**Parameters:**
- `master`: Master component instance
- `slave`: Slave component instance
- `memory_model`: Optional memory model for transactions (uses base MemoryModel)
- `log`: Logger instance (defaults to master's logger)
- `response_generation_mode`: If True, generate responses; if False, forward transactions
- `**kwargs`: Additional configuration options

```python
# Forwarding mode (master → slave)
handler = GAXICommandHandler(
    master=gaxi_master,
    slave=gaxi_slave,
    memory_model=memory_model,
    log=log,
    response_generation_mode=False
)

# Response generation mode (slave → master)
handler = GAXICommandHandler(
    master=gaxi_master,
    slave=gaxi_slave,
    memory_model=memory_model,
    log=log,
    response_generation_mode=True
)
```

#### Core Properties

- `master`: Master component
- `slave`: Slave component
- `memory_model`: Memory model for transactions
- `response_generation_mode`: Current operational mode
- `sequential_data_counter`: Counter for sequential data generation
- `pending_transactions`: Dictionary of pending transactions
- `completed_transactions`: Dictionary of completed transactions
- `pending_responses`: Dictionary of pending responses (response mode)
- `generated_responses`: Dictionary of generated responses (response mode)

## Lifecycle Management

### `async start()`

Start the command handler processing task.

**Returns:** Self for chaining

```python
# Start the handler
await handler.start()
```

### `async stop()`

Stop the command handler processing task.

**Returns:** Self for chaining

```python
# Stop the handler
await handler.stop()
```

## Transaction Processing (Forwarding Mode)

### `async _forward_transactions()`

Forward transactions from master to slave with dependency tracking.

**Internal method** - called automatically in forwarding mode

### `_is_dependency_satisfied(txn_id)`

Check if a transaction's dependencies are satisfied.

**Parameters:**
- `txn_id`: Transaction ID to check

**Returns:** True if dependencies are satisfied

### `async _send_to_slave(txn_id)`

Send a transaction to the slave component.

**Parameters:**
- `txn_id`: Transaction ID to send

## Response Generation (Response Mode)

### `async _generate_response_for_transaction(cmd_transaction)`

Generate a response for a received command transaction with sequential data generation.

**Parameters:**
- `cmd_transaction`: Command transaction to respond to

**Features:**
- **Sequential data generation** for reads when memory is empty
- **Memory integration** with automatic fallback
- **Field extraction** supporting multiple packet formats
- **Error handling** with comprehensive logging

```python
# This method is called automatically in response generation mode
# when slave receives transactions
```

### `_generate_sequential_data(address)`

Generate sequential data based on address for predictable testing.

**Parameters:**
- `address`: Address being read

**Returns:** Sequential data value

**Algorithm:**
- Combines sequential counter with address for predictability
- Uses word-aligned addressing (address >> 2)
- Maintains 32-bit data range
- Increments counter for each generation

```python
# Generates predictable data patterns:
# Address 0x1000 → 0x10000400 (first read)
# Address 0x1004 → 0x10000401 (next read)
# Address 0x1000 → 0x10000800 (later read)
```

## Field Extraction and Response Handling

### `_extract_field_value(transaction, field_name, alt_field_name=None, default=0)`

Extract a field value from a transaction supporting both storage methods.

**Parameters:**
- `transaction`: Transaction object
- `field_name`: Primary field name
- `alt_field_name`: Alternative field name
- `default`: Default value if field not found

**Returns:** Field value or default

**Supports:**
- GAXI-style fields dictionary
- APB-style attributes
- Lowercase field names
- Alternative field names

```python
# Extracts from multiple field formats:
pwrite = handler._extract_field_value(transaction, 'pwrite', 'cmd_pwrite')
address = handler._extract_field_value(transaction, 'paddr', 'cmd_paddr')
data = handler._extract_field_value(transaction, 'pwdata', 'cmd_pwdata')
```

### `_set_response_field(response_packet, field_name, alt_field_name=None, value=0)`

Set a field value in a response packet supporting both storage methods.

**Parameters:**
- `response_packet`: Response packet to modify
- `field_name`: Primary field name
- `alt_field_name`: Alternative field name
- `value`: Value to set

```python
# Sets response fields in multiple formats:
handler._set_response_field(response_packet, 'prdata', 'rsp_prdata', read_data)
handler._set_response_field(response_packet, 'pslverr', 'rsp_pslverr', 0)
```

## Memory Operations

### `async _handle_memory_write(address, data, strobe)`

Handle memory write operation with error handling.

**Parameters:**
- `address`: Target address
- `data`: Data to write
- `strobe`: Write strobe mask

**Returns:** Success status

```python
# Memory write with proper address masking and error handling
success = await handler._handle_memory_write(0x1000, 0xDEADBEEF, 0xF)
```

### `async _handle_memory_read(address)`

Handle memory read operation with error handling.

**Parameters:**
- `address`: Address to read from

**Returns:** Tuple of (success, data)

```python
# Memory read with automatic fallback to sequential data
success, data = await handler._handle_memory_read(0x1000)
if not success:
    # Will use sequential data generation
    pass
```

## Sequence Processing

### `async process_sequence(sequence)`

Process a GAXI sequence through the master-slave connection.

**Parameters:**
- `sequence`: GAXISequence to process

**Returns:** Dictionary of responses by transaction index

**Features:**
- **Dependency tracking**: Handles transaction dependencies
- **Completion monitoring**: Waits for transaction completion
- **Response mapping**: Maps responses to sequence indexes

```python
# Process sequence with dependencies
sequence = GAXISequence("test_sequence")
sequence.add_data_transaction(0x1000)
sequence.add_data_transaction(0x2000, depends_on=0)

response_map = await handler.process_sequence(sequence)
print(f"Response 0: {response_map[0]}")
print(f"Response 1: {response_map[1]}")
```

## Statistics and Monitoring

### `get_stats()`

Get comprehensive handler statistics.

**Returns:** Dictionary with statistics including:
- Transaction counts and timing
- Memory operation statistics
- Sequential data generation stats
- Component statistics
- Error tracking

```python
stats = handler.get_stats()
print(f"Completed transactions: {stats['completed_transactions']}")
print(f"Sequential reads: {stats['sequential_reads']}")
print(f"Memory operations: {stats['memory_operations']}")
print(f"Average latency: {stats['avg_latency']} ns")
```

### `get_transaction_status(txn_id=None)`

Get status of specific transaction or all transactions.

**Parameters:**
- `txn_id`: Transaction ID to check (None for all)

**Returns:** Transaction status information

```python
# Get status of all transactions
status = handler.get_transaction_status()
print(f"Pending: {status['pending']}")
print(f"Completed: {status['completed']}")

# Get status of specific transaction
specific_status = handler.get_transaction_status(txn_id)
```

### `reset()`

Reset the command handler to initial state.

```python
# Reset all tracking and statistics
handler.reset()
```

## Usage Patterns

### Basic Forwarding Setup

```python
async def setup_forwarding_handler():
    """Set up command handler for master→slave forwarding"""
    
    # Create memory model
    memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)
    
    # Create handler in forwarding mode
    handler = GAXICommandHandler(
        master=gaxi_master,
        slave=gaxi_slave,
        memory_model=memory,
        log=log,
        response_generation_mode=False
    )
    
    # Start processing
    await handler.start()
    
    return handler

async def test_forwarding():
    handler = await setup_forwarding_handler()
    
    # Send transactions through master
    for i in range(10):
        packet = gaxi_master.create_packet(addr=0x1000 + i*4, data=i*0x100)
        await gaxi_master.send(packet)
    
    # Wait for completion
    while handler.get_transaction_status()['pending'] > 0:
        await RisingEdge(dut.clk)
    
    # Get statistics
    stats = handler.get_stats()
    log.info(f"Forwarding test completed: {stats}")
    
    await handler.stop()
```

### Response Generation Setup

```python
async def setup_response_handler():
    """Set up command handler for slave→master response generation"""
    
    # Create memory model with initial data
    memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)
    
    # Populate memory with test data
    for addr in range(0, 0x1000, 4):
        data = bytearray([(addr + i) & 0xFF for i in range(4)])
        memory.write(addr, data)
    
    # Create handler in response generation mode
    handler = GAXICommandHandler(
        master=gaxi_master,
        slave=gaxi_slave,
        memory_model=memory,
        log=log,
        response_generation_mode=True
    )
    
    await handler.start()
    return handler

async def test_response_generation():
    handler = await setup_response_handler()
    
    # Send commands to slave
    for i in range(10):
        # Write command
        write_cmd = create_write_command(addr=0x1000 + i*4, data=i*0x100)
        gaxi_slave._recvQ.append(write_cmd)
        
        # Read command
        read_cmd = create_read_command(addr=0x1000 + i*4)
        gaxi_slave._recvQ.append(read_cmd)
    
    # Wait for responses
    await Timer(1000, units='ns')
    
    # Check response statistics
    stats = handler.get_stats()
    log.info(f"Generated {stats['generated_responses']} responses")
    log.info(f"Sequential reads: {stats['sequential_reads']}")
    
    await handler.stop()
```

### Advanced Dependency Testing

```python
async def test_dependency_handling():
    """Test transaction dependency handling"""
    
    handler = await setup_forwarding_handler()
    
    # Create sequence with dependencies
    sequence = GAXISequence("dependency_test")
    
    # Transaction 0: Base transaction
    sequence.add_data_transaction(0x1000, delay=0)
    
    # Transaction 1: Depends on transaction 0
    sequence.add_data_transaction(0x2000, delay=0, depends_on=0)
    
    # Transaction 2: Also depends on transaction 0
    sequence.add_data_transaction(0x3000, delay=0, depends_on=0)
    
    # Transaction 3: Depends on transaction 1
    sequence.add_data_transaction(0x4000, delay=0, depends_on=1)
    
    # Process sequence with dependency resolution
    response_map = await handler.process_sequence(sequence)
    
    # Verify responses
    assert len(response_map) == 4
    log.info("Dependency test completed successfully")
    
    # Check dependency statistics
    stats = handler.get_stats()
    assert stats['dependency_violations'] == 0
    
    await handler.stop()
```

### Memory Integration Testing

```python
async def test_memory_integration():
    """Test memory model integration with fallback"""
    
    # Create memory with limited data
    memory = MemoryModel(num_lines=64, bytes_per_line=4, log=log)
    
    # Only populate some addresses
    for addr in range(0x0000, 0x0100, 4):
        data = bytearray([addr & 0xFF, (addr >> 8) & 0xFF, 0x00, 0x00])
        memory.write(addr, data)
    
    handler = GAXICommandHandler(
        master=gaxi_master,
        slave=gaxi_slave,
        memory_model=memory,
        log=log,
        response_generation_mode=True
    )
    
    await handler.start()
    
    # Test memory reads (should use memory data)
    memory_read_cmd = create_read_command(addr=0x0010)
    gaxi_slave._recvQ.append(memory_read_cmd)
    
    # Test unmapped reads (should use sequential data)
    sequential_read_cmd = create_read_command(addr=0x8000)
    gaxi_slave._recvQ.append(sequential_read_cmd)
    
    await Timer(1000, units='ns')
    
    # Check statistics
    stats = handler.get_stats()
    log.info(f"Memory reads: {stats['memory_reads']}")
    log.info(f"Sequential reads: {stats['sequential_reads']}")
    
    await handler.stop()
```

### Performance Monitoring

```python
class PerformanceMonitor:
    def __init__(self, handler):
        self.handler = handler
        self.monitoring = True
        
    async def monitor_performance(self):
        """Continuously monitor handler performance"""
        while self.monitoring:
            await Timer(1000000, units='ns')  # Every 1ms
            
            stats = self.handler.get_stats()
            
            # Check performance metrics
            if stats['completed_transactions'] > 0:
                avg_latency = stats['avg_latency']
                if avg_latency > 10000:  # > 10µs
                    log.warning(f"High latency detected: {avg_latency:.1f}ns")
            
            # Check error rates
            if stats.get('dependency_violations', 0) > 0:
                log.warning(f"Dependency violations: {stats['dependency_violations']}")
            
            # Report throughput
            if stats['completed_transactions'] % 100 == 0:
                log.info(f"Processed {stats['completed_transactions']} transactions")

async def test_with_monitoring():
    handler = await setup_forwarding_handler()
    monitor = PerformanceMonitor(handler)
    
    # Start monitoring
    monitor_task = cocotb.start_soon(monitor.monitor_performance())
    
    # Run test
    await run_high_throughput_test(handler)
    
    # Stop monitoring
    monitor.monitoring = False
    monitor_task.kill()
    
    await handler.stop()
```

## Error Handling and Recovery

### Automatic Error Recovery

```python
try:
    # Process transaction with automatic error handling
    await handler._generate_response_for_transaction(transaction)
except Exception as e:
    # Handler automatically:
    # - Logs detailed error information
    # - Updates error statistics
    # - Continues processing other transactions
    # - Maintains system stability
    pass
```

### Field Extraction Fallbacks

```python
# Handler automatically tries multiple field extraction methods:
# 1. Fields dictionary (GAXI style)
# 2. Direct attributes (APB style)
# 3. Alternative field names
# 4. Lowercase versions
# 5. Returns default value if none found

value = handler._extract_field_value(
    transaction, 
    'paddr',           # Primary name
    'cmd_paddr',       # Alternative name
    default=0x0        # Safe default
)
```

### Memory Operation Fallbacks

```python
# For read operations:
# 1. Try memory model read
# 2. On failure, generate sequential data
# 3. Log the fallback for debugging
# 4. Continue operation seamlessly

success, data = await handler._handle_memory_read(address)
if not success:
    # Automatic fallback to sequential data generation
    data = handler._generate_sequential_data(address)
```

## Integration with Other Components

### Master Integration

```python
# Handler integrates seamlessly with GAXIMaster
master = GAXIMaster(dut, "TestMaster", "", clock, field_config)
handler = GAXICommandHandler(master, slave, response_generation_mode=False)

# Transactions from master are automatically forwarded
await master.send(packet)
```

### Slave Integration

```python
# Handler monitors slave receive queue for transactions
slave = GAXISlave(dut, "TestSlave", "", clock, field_config)
handler = GAXICommandHandler(master, slave, response_generation_mode=True)

# Received transactions automatically generate responses
```

### Memory Model Integration

```python
# Uses base MemoryModel directly for maximum compatibility
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)
handler = GAXICommandHandler(master, slave, memory_model=memory)

# Automatic memory operations with proper error handling
```

## Best Practices

### 1. **Choose Appropriate Mode**
```python
# Use forwarding mode for master→slave testing
handler = GAXICommandHandler(master, slave, response_generation_mode=False)

# Use response generation mode for slave→master testing
handler = GAXICommandHandler(master, slave, response_generation_mode=True)
```

### 2. **Initialize Memory Model**
```python
# Always provide memory model for realistic testing
memory = MemoryModel(num_lines=1024, bytes_per_line=4, log=log)
handler = GAXICommandHandler(master, slave, memory_model=memory)
```

### 3. **Monitor Statistics**
```python
# Regular statistics monitoring
async def monitor_handler():
    while True:
        await Timer(1000000, units='ns')
        stats = handler.get_stats()
        if stats['error_count'] > 0:
            log.warning(f"Errors detected: {stats}")
```

### 4. **Handle Dependencies Properly**
```python
# Always validate dependencies in sequences
sequence.validate_dependencies()
response_map = await handler.process_sequence(sequence)
```

### 5. **Use Sequential Data for Testing**
```python
# Sequential data generation provides predictable test patterns
# Address-based: Different addresses generate different patterns
# Counter-based: Each read increments the pattern
# Useful for debugging and verification
```

The GAXICommandHandler provides a comprehensive solution for GAXI transaction processing with enhanced data generation, robust error handling, and flexible operational modes for comprehensive verification scenarios.
