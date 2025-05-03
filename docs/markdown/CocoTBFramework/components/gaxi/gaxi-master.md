# GAXIMaster Component

## Overview

The `GAXIMaster` component serves as the primary driver for GAXI transactions, controlling the valid signal and driving data onto the bus. It works with both single-signal and multi-signal modes and provides enhanced memory integration capabilities.

## Key Features

- Drives the valid signal and waits for ready signal assertion
- Supports standard mode (single data bus) and multi-signal mode (individual signals per field)
- Provides flexible timing randomization through the `FlexRandomizer`
- Integrates with memory models for automated read/write operations
- Queues and manages transactions with automatic field value masking
- Handles transmission pipeline with configurable timing constraints

## Class Definition

```python
class GAXIMaster(BusDriver):
    def __init__(self, dut, title, prefix, clock,
                field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                randomizer=None, memory_model=None, memory_fields=None, log=None,
                field_mode=False, multi_sig=False, signal_map=None, 
                optional_signal_map=None, **kwargs):
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
- **log**: Logger instance
- **field_mode**: If True, use field mode with multiple fields packed into a single signal (default: False)
- **multi_sig**: If True, use multiple signals mode (default: False)
- **signal_map**: Dictionary mapping required GAXI signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional GAXI signals to DUT signals

## Signal Mapping

The master component uses the following standard signal names that can be mapped to actual DUT signals:

- **m2s_valid**: Master to slave valid signal
- **s2m_ready**: Slave to master ready signal
- **m2s_pkt**: Master to slave packet data signal (standard mode)
- **m2s_pkt_<field_name>**: Individual field signals (multi-signal mode)

Default signal mapping for standard mode:
```python
master_signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
master_optional_signal_map = {
    'm2s_pkt': 'i_wr_data'
}
```

## Key Methods

### Configuration Methods

```python
def set_randomizer(self, randomizer):
    """Set a new randomizer for timing constraints"""
    
def set_packet_generator(self, generator_func):
    """Set a function that generates packets on demand"""
    
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
async def send(self, packet):
    """Send a packet through the master"""
    
async def send_packets(self, count=1):
    """Send multiple packets using the configured generator"""
    
async def busy_send(self, transaction):
    """Send a transaction and wait for completion"""

def get_memory_stats(self):
    """Get memory operation statistics"""
```

## Internal Methods

```python
# Transmission pipeline
async def _transmit_pipeline(self):
    """Pipeline for transmitting transactions"""
    
async def _xmit_phase1(self):
    """First phase of transmission - delay and prepare signals"""
    
async def _xmit_phase2(self, transaction):
    """Second phase - drive signals and wait for handshake"""
    
async def _xmit_phase3(self, transaction):
    """Third phase - capture handshake and prepare for next transaction"""

# Signal handling
def _drive_signals(self, transaction):
    """Drive transaction data onto the bus signals"""
    
def _assign_valid_value(self, value):
    """Set the valid signal value"""
    
def _clear_data_bus(self):
    """Clear data signals during delay"""

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

# Create a master component in standard mode
master = GAXIMaster(
    dut, 'Master', '', dut.clk,
    field_config=field_config,
    timeout_cycles=1000
)

# Create a custom randomizer
randomizer = FlexRandomizer({
    'valid_delay': ([[0, 0], [1, 8], [9, 20]], [5, 2, 1])
})
master.set_randomizer(randomizer)

# Create and send a packet
packet = GAXIPacket(field_config)
packet.data = 0x12345678
await master.send(packet)

# Wait for transmission to complete
while master.transfer_busy:
    await RisingEdge(dut.clk)
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
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
optional_signal_map = {
    'm2s_pkt_addr': 'i_wr_addr',
    'm2s_pkt_data': 'i_wr_data'
}

# Create a master component in multi-signal mode
master = GAXIMaster(
    dut, 'MasterMulti', '', dut.clk,
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map,
    optional_signal_map=optional_signal_map
)

# Create and send a packet
packet = GAXIPacket(field_config)
packet.addr = 0x1000
packet.data = 0xABCDEF01
await master.send(packet)
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

# Create a master with memory integration
master = GAXIMaster(
    dut, 'MasterMem', '', dut.clk,
    field_config=field_config,
    memory_model=memory_model,
    memory_fields=memory_fields
)

# The packet's data field will be automatically written to memory
# at the specified address when sent
packet = GAXIPacket(field_config)
packet.addr = 0x100
packet.data = 0x12345678
await master.send(packet)

# Check memory statistics
stats = master.get_memory_stats()
print(f"Memory writes: {stats['writes']}")
```

## Tips and Best Practices

1. **Signal Mapping**: Always provide explicit signal mappings for clarity, even if using default names
2. **Field Configuration**: Define field configurations carefully, especially bit widths
3. **Error Handling**: Always check the transfer_busy flag to ensure transactions complete
4. **Timeout Handling**: Set appropriate timeout_cycles based on expected system latency
5. **Memory Integration**: Use the EnhancedMemoryIntegration for better error handling and diagnostics
6. **Multi-Signal Mode**: For complex interfaces, multi_sig=True with individual field signals provides better debug visibility
7. **Field Mode**: When memory is limited, field_mode=True allows packing multiple fields into a single signal
