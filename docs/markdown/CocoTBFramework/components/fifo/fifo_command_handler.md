# FIFO Command Handler Documentation

## Overview

`fifo_command_handler.py` implements the FIFOCommandHandler class, which coordinates transactions between FIFO Master and Slave components. It serves as an orchestrator that handles transaction routing, timing, response matching, and provides enhanced error detection and dependency management.

## Class: FIFOCommandHandler

```python
class FIFOCommandHandler:
    """
    Command handler for FIFO transactions between master and slave components.
    
    This class coordinates communication between FIFOMaster and FIFOSlave
    components, handling packet routing, timing, and response matching.
    It supports transaction dependencies, provides monitoring
    capabilities for transaction flow, and includes enhanced error detection.
    """
```

### Key Features

- **Transaction Coordination**:
  - Routes transactions from master to slave
  - Manages transaction timing and flow control
  - Handles response matching and correlation
  
- **Dependency Management**:
  - Supports transactions that depend on previous ones
  - Enforces transaction ordering constraints
  - Prevents deadlocks from dependency violations
  
- **FIFO State Modeling**:
  - Tracks FIFO depth to model fullness
  - Prevents overflow and underflow conditions
  - Models backpressure and capacity constraints
  
- **Enhanced Error Detection**:
  - Detects protocol violations
  - Identifies potential deadlock conditions
  - Tracks errors with timestamps and details
  
- **Statistics Collection**:
  - Tracks transaction latency (min/max/avg)
  - Records FIFO utilization metrics
  - Maintains comprehensive error counts

### Initialization

```python
def __init__(self, master, slave, memory_model=None, log=None, fifo_capacity=8):
    """
    Initialize the FIFO command handler.
    
    Args:
        master: FIFOMaster instance
        slave: FIFOSlave instance
        memory_model: Optional memory model (if None, uses master's memory model)
        log: Logger instance
        fifo_capacity: FIFO capacity in entries for modeling
    """
```

### Key Methods

#### Basic Operations

- **start()**:
  Start the command handler processing task.
  
- **stop()**:
  Stop the command handler processing task.
  
- **add_callback(callback)**:
  Add a callback function to be called when slave responds.
  
- **remove_callback(callback)**:
  Remove a previously added callback function.

#### Transaction Management

- **_forward_transactions()**:
  Forward transactions from master to slave when FIFO is not full.
  
- **_is_dependency_satisfied(txn_id)**:
  Check if a transaction's dependencies are satisfied.
  
- **_send_to_slave(txn_id)**:
  Send a transaction to the slave.
  
- **_handle_slave_response(response)**:
  Handle a response from the slave.
  
- **_check_waiting_transactions()**:
  Check if any waiting transactions now have satisfied dependencies.

#### FIFO State Management

- **_update_fifo_state()**:
  Update the FIFO state (empty, full, etc.).
  
- **_check_protocol_violations()**:
  Check for potential protocol violations based on component signals.
  
- **_update_statistics()**:
  Update handler statistics.

#### Information Retrieval

- **get_stats()**:
  Get handler statistics.
  
- **get_fifo_state()**:
  Get current FIFO state.
  
- **get_transaction_status(txn_id=None)**:
  Get status of a specific transaction or all transactions.
  
- **get_error_log()**:
  Get log of detected errors.

#### Sequence Processing

- **process_sequence(sequence)**:
  Process a FIFO sequence through the master-slave connection.
  
- **add_error_handler(handler_function)**:
  Add a function to be called when errors are detected.
  
- **clear_error_log()**:
  Clear the error log.

### Transaction Tracking

The command handler maintains several data structures for transaction tracking:

- **pending_transactions**: Dictionary of transactions in progress
- **completed_transactions**: Dictionary of completed transactions
- **transaction_ordering**: List of transaction IDs in order of receipt
- **responses**: Dictionary mapping transaction IDs to responses
- **callbacks**: List of callback functions to invoke for responses

### FIFO State Tracking

The handler models the FIFO state with detailed attributes:

```python
self.fifo_state = {
    'depth': 0,               # Current depth in entries
    'empty': True,            # True if empty
    'full': False,            # True if full
    'overflow_prevented': 0,  # Count of prevented overflows
    'underflow_prevented': 0, # Count of prevented underflows
    'last_check_time': 0,     # Last check timestamp
    'max_depth_reached': 0    # Maximum depth observed
}
```

### Error Tracking

The handler maintains comprehensive error tracking:

```python
self.error_log = []  # List of detected errors with timestamps
self.error_counts = {
    'overflow_attempts': 0,
    'underflow_attempts': 0,
    'dependency_violations': 0,
    'timeout_errors': 0,
    'protocol_violations': 0
}
```

Each error log entry includes:
- **time**: Timestamp when the error occurred
- **type**: Type of error (e.g., 'overflow_attempt')
- **details**: Detailed description of the error

### Statistics Collection

The handler collects comprehensive statistics:

```python
self.stats = {
    'total_transactions': 0,
    'completed_transactions': 0,
    'pending_transactions': 0,
    'avg_latency': 0,
    'min_latency': float('inf'),
    'max_latency': 0,
    'fifo_fullness_max': 0,
    'fifo_deadlocks_prevented': 0,
    'error_counts': self.error_counts
}
```

## Main Processing Loop

The command handler operates through a main processing loop:

```python
async def _process_transactions(self):
    """
    Main processing loop for transactions from master to slave.
    """
    # Set up callbacks for slave responses
    self.slave.add_callback(self._handle_slave_response)
    
    # Main processing loop
    while self.running:
        # Check for new transactions from master to forward to slave
        await self._forward_transactions()
        
        # Update FIFO state
        self._update_fifo_state()
        
        # Check for potential protocol violations
        self._check_protocol_violations()
        
        # Update statistics
        self._update_statistics()
        
        # Wait for next cycle
        await RisingEdge(self.master.clock)
```

## Transaction Flow

Transactions flow through the handler in the following sequence:

1. Master sends transaction to its `sent_queue`
2. Handler's `_forward_transactions()` takes it from master's queue
3. Handler assigns a unique transaction ID and records in `pending_transactions`
4. If dependencies are satisfied, handler sends to slave via `_send_to_slave()`
5. Slave processes the transaction and generates a response
6. Handler's `_handle_slave_response()` receives the response
7. Handler matches response to pending transaction and marks as completed
8. Handler executes callbacks with the response
9. Handler checks if any waiting transactions now have satisfied dependencies

## Dependency Management

The handler supports transaction dependencies:

```python
def _is_dependency_satisfied(self, txn_id):
    """
    Check if a transaction's dependencies are satisfied.
    """
    transaction_info = self.pending_transactions.get(txn_id)
    if not transaction_info:
        return False
        
    depends_on = transaction_info.get('depends_on')
    if depends_on is None:
        return True  # No dependency
        
    # Find the dependent transaction in our tracking
    dependent_txn_id = None
    for i, tx_id in enumerate(self.transaction_ordering):
        if i == depends_on:
            dependent_txn_id = tx_id
            break
            
    # Check if the dependent transaction is completed
    dependency_satisfied = dependent_txn_id in self.completed_transactions
    
    return dependency_satisfied
```

## Usage Examples

### Basic Setup and Transaction Processing

```python
# Create master and slave components
master = FIFOMaster(dut, "Master", "", clock, field_config)
slave = FIFOSlave(dut, "Slave", "", clock, field_config)

# Create command handler
handler = FIFOCommandHandler(master, slave, fifo_capacity=8)

# Start the handler
await handler.start()

# Create and send a transaction
packet = FIFOPacket(field_config)
packet.data = 0x12345678
await master.send(packet)

# Wait for transaction to complete
while len(handler.completed_transactions) == 0:
    await RisingEdge(clock)

# Check results
print(f"Completed transactions: {len(handler.completed_transactions)}")
print(f"FIFO state: {handler.get_fifo_state()}")
```

### Processing a Sequence

```python
# Create a sequence
sequence = FIFOSequence("test_seq", field_config)
sequence.add_data_value(0xAAAAAAAA)
sequence.add_data_value(0x55555555)
sequence.add_data_value(0x33333333)

# Process the sequence with the handler
response_map = await handler.process_sequence(sequence)

# Analyze responses
for seq_idx, response in response_map.items():
    print(f"Response for sequence index {seq_idx}: data=0x{response.data:X}")
```

### Working with Transaction Dependencies

```python
# Create a sequence with dependencies
sequence = FIFOSequence("dependency_seq", field_config)

# First transaction (base transaction)
base_idx = sequence.add_data_value(0x1000)

# Second transaction depends on first
idx2 = sequence.add_transaction_with_dependency(
    {'data': 0x2000}, 
    delay=0, 
    depends_on_index=base_idx
)

# Third transaction depends on second
idx3 = sequence.add_transaction_with_dependency(
    {'data': 0x3000}, 
    delay=0, 
    depends_on_index=idx2
)

# Process the sequence with dependencies enforced
responses = await handler.process_sequence(sequence)
```

### Using Callbacks for Response Handling

```python
# Define a callback function
def handle_response(response):
    print(f"Response received: data=0x{response.data:X}")
    # Additional processing...

# Register the callback
handler.add_callback(handle_response)

# Send a transaction - callback will be called when response is received
packet = FIFOPacket(field_config)
packet.data = 0x12345678
await master.send(packet)
```

### Error Handling and Logging

```python
# Define an error handler
def error_handler(error_info):
    error_type = error_info['type']
    error_time = error_info['time']
    details = error_info['details']
    print(f"Error detected at {error_time}ns: {error_type} - {details}")
    # Take corrective action...

# Register the error handler
handler.add_error_handler(error_handler)

# Check error log
errors = handler.get_error_log()
if errors:
    print(f"Found {len(errors)} errors:")
    for error in errors:
        print(f"  {error['type']} at {error['time']}ns: {error['details']}")
```

### Getting Statistics

```python
# Get handler statistics
stats = handler.get_stats()
print(f"Total transactions: {stats['total_transactions']}")
print(f"Completed transactions: {stats['completed_transactions']}")
print(f"Average latency: {stats['avg_latency']:.2f} ns")
print(f"FIFO fullness max: {stats['fifo_fullness_max']} entries")

# Get FIFO state
fifo_state = handler.get_fifo_state()
print(f"FIFO depth: {fifo_state['depth']}/{handler.fifo_capacity}")
print(f"Empty: {fifo_state['empty']}, Full: {fifo_state['full']}")
print(f"Overflow prevented: {fifo_state['overflow_prevented']} times")
```

## Advanced Features

### Protocol Violation Detection

The command handler actively monitors for protocol violations:

```python
def _check_protocol_violations(self):
    """Check for potential protocol violations based on component signals."""
    # Only perform checks if we have access to the relevant signals
    if not (hasattr(self.master, 'write_sig') and hasattr(self.master, 'full_sig') and 
            hasattr(self.slave, 'read_sig') and hasattr(self.slave, 'empty_sig')):
        return
        
    current_time = get_sim_time('ns')
    
    # Check for write-while-full violation
    if (self.master.write_sig.value.is_resolvable and 
        self.master.full_sig.value.is_resolvable and
        int(self.master.write_sig.value) == 1 and
        int(self.master.full_sig.value) == 1):
        
        self.log.warning(f"Protocol violation: Write while full at {current_time}ns")
        self.error_counts['protocol_violations'] += 1
        self.error_log.append({
            'time': current_time,
            'type': 'write_while_full',
            'details': "Write asserted while FIFO is full"
        })
```

### Deadlock Prevention

The handler can detect and prevent potential deadlocks:

```python
# Check for deadlock
if self.fifo_state['full'] and self.stats['pending_transactions'] > 0 and self.stats['completed_transactions'] == 0:
    # This could be a deadlock
    self.log.warning("Potential deadlock detected: FIFO full and no transactions completed")
    self.stats['fifo_deadlocks_prevented'] += 1
    self.error_log.append({
        'time': current_time,
        'type': 'potential_deadlock',
        'details': "FIFO full and no transactions completed"
    })
```

### Transaction Dependency Resolution

The handler carefully tracks and enforces transaction dependencies:

```python
def _check_waiting_transactions(self):
    """Check if any waiting transactions now have satisfied dependencies."""
    for txn_id in self.transaction_ordering:
        if (
            txn_id in self.pending_transactions 
            and not self.pending_transactions[txn_id]['completed']
            and self._is_dependency_satisfied(txn_id)
        ):
            # This transaction's dependencies are now satisfied, send it
            cocotb.start_soon(self._send_to_slave(txn_id))
```

### Response Matching

The handler uses several strategies to match responses to pending transactions:

```python
# First try matching by transaction_id if available
if hasattr(response, 'transaction_id') and response.transaction_id:
    if response.transaction_id in self.pending_transactions:
        matched_txn_id = response.transaction_id

# If no match by ID, match by order for compatibility
if matched_txn_id is None:
    # Try to match by going through pending transactions in order
    for txn_id in self.transaction_ordering:
        if txn_id in self.pending_transactions and not self.pending_transactions[txn_id]['completed']:
            # This is a simple matching strategy - in a real implementation, matching would
            # be based on protocol-specific identifiers
            matched_txn_id = txn_id
            break
```

## Integration with Other Components

The FIFOCommandHandler is designed to integrate with:

- **FIFOMaster**: Controls the write side of the FIFO
- **FIFOSlave**: Controls the read side of the FIFO
- **FIFOSequence**: Provides sequences of transactions to process
- **Memory Model**: Optional memory storage for transaction data
- **Test Bench**: Overall test coordination and verification

## Performance Considerations

1. **Efficient Transaction Processing**: Uses asynchronous coroutines to handle transactions efficiently
2. **Minimal Copy Design**: References transactions rather than copying them
3. **Dynamic Dependency Resolution**: Only processes transactions when dependencies are satisfied
4. **Comprehensive State Tracking**: Maintains accurate FIFO state model
5. **Distributed Callback System**: Allows flexible integration with other components

## Best Practices

1. **Start Early, Stop Late**: Start the handler before sending transactions and stop after all transactions are processed
2. **Use Callbacks**: Register callbacks to handle responses rather than polling
3. **Monitor Error Log**: Check the error log regularly to detect protocol violations
4. **Use Sequences for Complex Tests**: Use FIFOSequence to model complex transaction patterns
5. **Set Realistic Capacity**: Configure the fifo_capacity to match the actual DUT
6. **Handle Dependencies Carefully**: Ensure transaction dependencies form a directed acyclic graph (DAG)
7. **Check Statistics**: Analyze the handler statistics for performance issues

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
