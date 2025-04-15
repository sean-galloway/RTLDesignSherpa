# GAXICommandHandler Component

## Overview

The `GAXICommandHandler` component coordinates transactions between GAXI Master and Slave components, managing packet routing, timing, and response matching. It provides a higher-level abstraction for controlling the flow of transactions through a GAXI interface, handling dependencies, and collecting performance statistics.

## Key Features

- Coordinates communication between GAXIMaster and GAXISlave components
- Handles packet routing from master to slave with dependency tracking
- Manages transaction timing and ordering
- Matches responses from slave to appropriate transactions
- Provides transaction statistics and diagnostics
- Supports processing of GAXI sequences
- Offers specialized variants for specific protocols (e.g., APB)

## Class Definition

```python
class GAXICommandHandler:
    def __init__(self, master, slave, memory_model=None, log=None):
        # ...
```

## Parameters

- **master**: GAXIMaster instance
- **slave**: GAXISlave instance
- **memory_model**: Optional memory model (if None, uses master's memory model)
- **log**: Logger instance

## Key Methods

### Lifecycle Management

```python
async def start(self):
    """Start the command handler processing task"""
    
async def stop(self):
    """Stop the command handler processing task"""
```

### Transaction Processing

```python
async def process_sequence(self, sequence):
    """Process a GAXI sequence through the master-slave connection"""
```

### Status and Statistics

```python
def get_stats(self):
    """Get handler statistics"""
    
def get_transaction_status(self, txn_id=None):
    """Get status of a specific transaction or all transactions"""
```

## Internal Methods

```python
async def _process_transactions(self):
    """Main processing loop for transactions from master to slave"""
    
async def _forward_transactions(self):
    """Forward transactions from master to slave"""
    
def _is_dependency_satisfied(self, txn_id):
    """Check if a transaction's dependencies are satisfied"""
    
async def _send_to_slave(self, txn_id):
    """Send a transaction to the slave"""
    
def _handle_slave_response(self, response):
    """Handle a response from the slave"""
    
def _check_waiting_transactions(self):
    """Check if any waiting transactions now have satisfied dependencies"""
    
def _update_statistics(self):
    """Update handler statistics"""
```

## Usage Example

```python
# Create master, slave and memory model components
field_config = FieldConfig()
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})

memory_model = MemoryModel(num_lines=1024, bytes_per_line=4)

master = GAXIMaster(
    dut, 'Master', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model
)

slave = GAXISlave(
    dut, 'Slave', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model
)

# Create command handler
command_handler = GAXICommandHandler(master, slave, memory_model)

# Start the command handler
await command_handler.start()

# Create and send transactions (will be automatically coordinated by the handler)
for i in range(10):
    packet = GAXIPacket(field_config)
    packet.data = i
    await master.send(packet)

# Wait for all transactions to be processed
await RisingEdge(dut.clk)

# Get transaction statistics
stats = command_handler.get_stats()
print(f"Completed transactions: {stats['completed_transactions']}")
print(f"Average latency: {stats['avg_latency']} ns")

# Stop the command handler
await command_handler.stop()
```

## Sequence Processing Example

```python
# Create a sequence
sequence = GAXISequence("test_sequence", field_config)

# Add transactions to the sequence
sequence.add_data_incrementing(count=10, data_start=0, data_step=1, delay=0)
sequence.add_walking_ones(data_width=32, delay=1)

# Create command handler and start it
command_handler = GAXICommandHandler(master, slave, memory_model)
await command_handler.start()

# Process the entire sequence
response_map = await command_handler.process_sequence(sequence)

# Examine the responses
for seq_index, response in response_map.items():
    print(f"Response for transaction {seq_index}: {response.formatted(compact=True)}")

# Stop the command handler
await command_handler.stop()
```

## Dependency Handling Example

```python
# Create a sequence with dependencies
sequence = GAXISequence("dependency_sequence", field_config)

# Add a transaction with no dependencies
first_index = sequence.add_data_value(0x1000, delay=0)

# Add transactions that depend on the first one
for i in range(1, 5):
    sequence.add_transaction_with_dependency(
        {'data': 0x1000 + i},
        delay=0,
        depends_on_index=first_index
    )

# Create command handler and start it
command_handler = GAXICommandHandler(master, slave, memory_model)
await command_handler.start()

# Process the sequence
response_map = await command_handler.process_sequence(sequence)

# Verify that dependencies were respected
print(f"First transaction completed at: {response_map[first_index].end_time} ns")
for i in range(1, 5):
    print(f"Dependent transaction {i} completed at: {response_map[i].end_time} ns")

# Get status of all transactions
status = command_handler.get_transaction_status()
print(f"Transaction ordering: {status['ordering']}")

# Stop the command handler
await command_handler.stop()
```

## Performance Monitoring Example

```python
# Create command handler
command_handler = GAXICommandHandler(master, slave, memory_model)
await command_handler.start()

# Send a batch of transactions
for i in range(100):
    packet = GAXIPacket(field_config)
    packet.data = i
    await master.send(packet)

# Wait for processing to complete
await Timer(1000, units='ns')

# Get performance statistics
stats = command_handler.get_stats()
print(f"Total transactions: {stats['total_transactions']}")
print(f"Completed transactions: {stats['completed_transactions']}")
print(f"Pending transactions: {stats['pending_transactions']}")
print(f"Average latency: {stats['avg_latency']:.2f} ns")
print(f"Minimum latency: {stats['min_latency']:.2f} ns")
print(f"Maximum latency: {stats['max_latency']:.2f} ns")

# Stop the command handler
await command_handler.stop()
```

## Specialized Command Handler Example

The framework also includes a specialized variant for APB slave interfaces:

```python
# Create APB-specific command handler
apb_handler = GAXICommandHandler_APBSlave(
    gaxi_master=response_master,
    gaxi_slave=command_slave,
    cmd_field_config=cmd_field_config,
    rsp_field_config=rsp_field_config
)

# Start the command handler
await apb_handler.start()

# The handler will automatically:
# 1. Take packets from the command slave
# 2. Create appropriate response packets
# 3. Send them through the response master

# Stop the command handler
await apb_handler.stop()
```

## Tips and Best Practices

1. **Start/Stop Management**: Always start the command handler before sending transactions and stop it after completion
2. **Memory Model Integration**: Provide a shared memory model for consistent data handling
3. **Dependency Tracking**: Use dependency information in transactions for complex test scenarios
4. **Sequence Processing**: Use the process_sequence method for handling entire sequences of transactions
5. **Statistics Monitoring**: Regularly check handler statistics to detect performance issues or bottlenecks
6. **Error Handling**: Implement timeout handling for scenarios where transactions might get stuck
7. **Transaction Status**: Use get_transaction_status to track the state of individual transactions
8. **Specialized Handlers**: Use specialized handler variants for specific protocols when available
9. **Log Integration**: Provide a logger instance for better debugging information
10. **Callbacks**: Implement custom callbacks for advanced transaction processing logic
