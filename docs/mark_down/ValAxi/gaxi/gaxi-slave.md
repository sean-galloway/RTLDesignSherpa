# GAXISlave Component

## Overview

The `GAXISlave` component serves as the receiver for GAXI transactions, controlling the ready signal and capturing data from the bus. It works with both single-signal and multi-signal modes, supports multiple operating modes, and provides enhanced memory integration capabilities.

## Key Features

- Controls the ready signal and monitors valid signal
- Supports multiple operating modes: 'skid', 'fifo_mux', and 'fifo_flop'
- Works with both standard mode (single data bus) and multi-signal mode (individual signals per field)
- Provides flexible timing randomization through the `FlexRandomizer`
- Integrates with memory models for automated read/write operations
- Queues received transactions with optional field value masking
- Handles transaction reception with configurable timing constraints

## Class Definition

```python
class GAXISlave(BusMonitor):
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None,
                field_mode=False, multi_sig=False, log=None, mode='skid', 
                signal_map=None, optional_signal_map=None, **kwargs):
        # ...
```

## Parameters

- **dut**: Device under test
- **title**: Title of the component
- **prefix**: Signal prefix used in the bus code
- **clock**: Clock signal
- **field_config**: Field configuration for packets
- **packet_class**: Class to use for creating packets (default: `GAXIPacket`)
- **timeout_cycles**: Maximum cycles to wait before timeout (default: 1000)
- **randomizer**: FlexRandomizer instance for randomizing timing
- **memory_model**: Memory model instance for reading/writing data
- **memory_fields**: Dictionary mapping memory fields to packet field names
- **field_mode**: If True, use field mode with multiple fields packed into a single signal (default: False)
- **multi_sig**: If True, use multiple signals mode (default: False)
- **log**: Logger instance
- **mode**: Operating mode ('skid', 'fifo_mux', 'fifo_flop') (default: 'skid')
- **signal_map**: Dictionary mapping required GAXI signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional GAXI signals to DUT signals

## Operating Modes

The slave component supports three operating modes:

1. **skid**: Standard mode where data is captured immediately on valid/ready handshake
2. **fifo_mux**: FIFO multiplexer mode, uses 'ow_rd_data' signal instead of 'o_rd_data'
3. **fifo_flop**: FIFO flip-flop mode, captures data one clock after valid/ready handshake

## Signal Mapping

The slave component uses the following standard signal names that can be mapped to actual DUT signals:

- **m2s_valid**: Master to slave valid signal
- **s2m_ready**: Slave to master ready signal
- **m2s_pkt**: Master to slave packet data signal (standard mode)
- **m2s_pkt_<field_name>**: Individual field signals (multi-signal mode)

Default signal mapping for standard mode:
```python
slave_signal_map = {
    'm2s_valid': 'o_rd_valid',
    's2m_ready': 'i_rd_ready'
}
slave_skid_optional_signal_map = {
    'm2s_pkt': 'o_rd_data'
}
```

For 'fifo_mux' mode:
```python
slave_fifo_mux_optional_signal_map = {
    'm2s_pkt': 'ow_rd_data'
}
```

## Key Methods

### Configuration Methods

```python
def set_randomizer(self, randomizer):
    """Set a new randomizer for timing constraints"""
    
def set_memory_model(self, memory_model, memory_fields=None):
    """Set or update the memory model"""
```

### Bus Control Methods

```python
async def reset_bus(self):
    """Reset the bus to initial state"""
    
async def wait_cycles(self, cycles):
    """Wait for a specified number of clock cycles"""
```

### Transaction Methods

```python
async def process_request(self, transaction):
    """Process a transaction request, usually from a command handler"""
    
def get_memory_stats(self):
    """Get memory operation statistics"""
```

## Internal Methods

```python
# Reception pipeline
async def _monitor_recv(self):
    """Monitor for incoming transactions (read channel)"""
    
async def _recv_phase1(self, last_packet, last_xfer):
    """Receive phase 1: Handle pending transactions from previous cycle"""
    
async def _recv_phase2(self):
    """Receive phase 2: Handle ready delays and assert ready"""
    
async def _recv_phase3(self, current_time):
    """Receive phase 3: Check for valid handshake and process transaction"""

# Signal and packet handling
def _finish_packet(self, current_time, packet, data_dict=None):
    """Finish packet processing and trigger callbacks"""
    
def _get_data_dict(self):
    """Collect data from field signals in multi-signal mode"""
    
def _set_rd_ready(self, value):
    """Set the ready signal value"""

# Field value masking
def _check_field_value(self, field_name, field_value):
    """Check if a field value exceeds the maximum possible value for the field"""
```

## Usage Example

```python
# Create a field configuration
field_config = FieldConfig()
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})

# Create a slave component in standard mode
slave = GAXISlave(
    dut, 'Slave', '', dut.clk,
    field_config=field_config,
    timeout_cycles=1000,
    mode='skid'
)

# Create a custom randomizer
randomizer = FlexRandomizer({
    'ready_delay': ([[0, 1], [2, 8], [9, 30]], [5, 2, 1])
})
slave.set_randomizer(randomizer)

# Wait for transactions to be received
while True:
    await RisingEdge(dut.clk)
    
    # Check if any transactions were received
    if slave.received_queue:
        packet = slave.received_queue.popleft()
        print(f"Received data: 0x{packet.data:X}")
```

## Multi-Signal Mode Example

```python
# Create a field configuration with multiple fields
field_config = FieldConfig()
field_config.add_field_dict('addr', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Address value'
})
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})

# Signal mapping for multi-signal mode
signal_map = {
    'm2s_valid': 'o_rd_valid',
    's2m_ready': 'i_rd_ready'
}
optional_signal_map = {
    'm2s_pkt_addr': 'o_rd_addr',
    'm2s_pkt_data': 'o_rd_data'
}

# Create a slave component in multi-signal mode
slave = GAXISlave(
    dut, 'SlaveMulti', '', dut.clk,
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map,
    optional_signal_map=optional_signal_map,
    mode='skid'
)
```

## Memory Model Integration Example

```python
# Create a memory model
memory_model = MemoryModel(
    num_lines=1024,
    bytes_per_line=4
)

# Memory field mapping
memory_fields = {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}

# Create a slave with memory integration
slave = GAXISlave(
    dut, 'SlaveMem', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model,
    memory_fields=memory_fields
)

# When a packet is received, its addr field will be used to read from memory
# and update the data field automatically
while True:
    await RisingEdge(dut.clk)
    
    # Check if any transactions were received
    if slave.received_queue:
        packet = slave.received_queue.popleft()
        print(f"Received address: 0x{packet.addr:X}, data: 0x{packet.data:X}")

# Check memory statistics
stats = slave.get_memory_stats()
print(f"Memory reads: {stats['reads']}")
```

## FIFO_FLOP Mode Example

```python
# Create a slave in FIFO_FLOP mode
slave_fifo_flop = GAXISlave(
    dut, 'SlaveFF', '', dut.clk,
    field_config=field_config,
    mode='fifo_flop'
)

# In FIFO_FLOP mode, the slave will capture data one clock after
# the valid/ready handshake occurs
```

## Command Handler Integration Example

```python
# Create a slave with memory model
slave = GAXISlave(
    dut, 'Slave', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model
)

# Create a command handler that will use the slave's process_request method
command_handler = GAXICommandHandler(master, slave, memory_model)

# Start the command handler
await command_handler.start()

# The command handler will automatically process transactions
# from the master and send them to the slave

# Create and send a request packet directly to the slave
request = GAXIPacket(field_config)
request.addr = 0x1000
request.cmd = 0  # Read operation
response = await slave.process_request(request)

print(f"Response data: 0x{response.data:X}")
```

## Tips and Best Practices

1. **Mode Selection**: Choose the appropriate mode based on your DUT implementation
   - 'skid' for standard skid buffers
   - 'fifo_mux' for multiplexed FIFO outputs
   - 'fifo_flop' for flip-flop based FIFOs where data is valid one clock after handshake
2. **Signal Mapping**: Always provide explicit signal mappings for clarity, even if using default names
3. **Field Configuration**: Define field configurations carefully, especially bit widths
4. **Queue Management**: Regularly check and process the received_queue to avoid memory buildup
5. **Memory Integration**: Use the EnhancedMemoryIntegration for better error handling and diagnostics
6. **Multi-Signal Mode**: For complex interfaces, multi_sig=True with individual field signals provides better debug visibility
7. **Field Mode**: When memory is limited, field_mode=True allows packing multiple fields into a single signal
