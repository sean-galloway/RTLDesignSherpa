# FIFO Master Documentation

## Overview

`fifo_master.py` implements the FIFOMaster component, which controls the write interface of a FIFO. It drives the write control signals and data signals according to the FIFO protocol, handles timing constraints, and manages the flow of transactions.

## Class: FIFOMaster

The FIFOMaster class extends `BusDriver` from `cocotb_bus` and provides comprehensive functionality for driving the write side of a FIFO interface.

```python
class FIFOMaster(BusDriver):
    """
    Master driver for FIFO transactions with enhanced memory integration.
    Controls i_write signal and monitors o_wr_full.
    """
```

### Key Features

- **Multiple Signal Modes**:
  - Standard mode with single data bus
  - Multi-signal mode with separate signals for each field
  
- **Field Mode Support**:
  - Treats standard data bus as containing multiple fields
  - Automatically packs fields into a combined value
  
- **Memory Integration**:
  - Optional integration with memory models
  - Automatic read/write of memory based on transactions
  
- **Timing Randomization**:
  - Configurable random delays between transactions
  - Supports various distribution patterns
  
- **Error Detection**:
  - Detects protocol violations (write while full)
  - Validates field values against field widths
  
- **Comprehensive Statistics**:
  - Tracks transactions, timeouts, and protocol violations
  - Records FIFO fullness metrics

### Initialization

```python
def __init__(self, dut, title, prefix, clock,
            field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
            randomizer=None, memory_model=None, memory_fields=None, log=None,
            field_mode=False, multi_sig=False, signal_map=None, 
            optional_signal_map=None, **kwargs):
    """Initialize the FIFO master."""
```

#### Parameters

- **dut**: Device under test
- **title**: Title of the bus
- **prefix**: Signal prefix
- **clock**: Clock signal
- **field_config**: Field configuration for packets
- **packet_class**: Class to use for creating packets
- **timeout_cycles**: Maximum cycles to wait before timeout
- **randomizer**: FlexRandomizer instance for randomizing timing
- **memory_model**: Optional MemoryModel instance
- **memory_fields**: Dictionary mapping memory fields to packet field names
- **log**: Logger instance
- **field_mode**: If True, treat data bus as containing multiple fields
- **multi_sig**: If True, use separate signals for each field
- **signal_map**: Dictionary mapping FIFO signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional FIFO signals to DUT signals

### Standard Signal Names

```python
# Standard Signal names
fifo_write = 'i_write'     # Write control signal
fifo_wr_full = 'o_wr_full' # FIFO full indicator
fifo_wr_data = 'i_wr_data' # Write data bus
```

### Key Methods

#### Basic Operations

- **send(transaction, sync=True, **kwargs)**:
  Send a transaction to the FIFO.
  
- **reset_bus()**:
  Reset the bus to initial state.
  
- **busy_send(transaction)**:
  Send a transaction and wait for completion.
  
- **send_packets(count=1)**:
  Send multiple packets using a configured generator.

#### Configuration

- **set_randomizer(randomizer)**:
  Set a new randomizer for timing constraints.
  
- **set_packet_generator(generator_func)**:
  Set a function that generates packets on demand.
  
- **set_memory_model(memory_model, memory_fields=None)**:
  Set or update the memory model.

#### Internal Pipeline Methods

- **_driver_send(transaction, sync, hold, **kwargs)**:
  Inner send implementation.
  
- **_transmit_pipeline()**:
  Main pipeline for transmitting transactions.
  
- **_xmit_phase1()**:
  First phase of transmission - delay and prepare signals.
  
- **_xmit_phase2(transaction)**:
  Second phase - drive signals and check if FIFO is full.
  
- **_xmit_phase3(transaction)**:
  Third phase - complete the transfer and prepare for next.

#### Signal Handling

- **_drive_signals(transaction)**:
  Drive transaction data onto the bus signals.
  
- **_drive_signals_helper(fifo_data)**:
  Helper for driving signals in field_mode.
  
- **_assign_write_value(value)**:
  Set the write signal to specified value.
  
- **_clear_data_bus()**:
  Reset all data signals to zero.

#### Utility Methods

- **wait_cycles(cycles)**:
  Wait for a specified number of clock cycles.
  
- **get_memory_stats()**:
  Get memory operation statistics.
  
- **get_stats()**:
  Get transaction statistics.
  
- **_check_field_value(field_name, field_value)**:
  Check if a field value exceeds the maximum possible value.

### Multi-Signal Mode

In multi-signal mode, the master creates individual signals for each field:

```python
# Example signal mapping in multi-signal mode
field_signal_name = f'i_wr_pkt_{field_name}'
```

The method `_initialize_multi_signal_mode()` handles setup of these signals.

### Transmit Pipeline

The transmission pipeline handles the complete lifecycle of a transaction:

1. **Queue**: Transactions are added to `transmit_queue`
2. **Pipeline**: The `_transmit_pipeline()` coroutine processes the queue
3. **Phases**: Each transaction goes through three phases:
   - Phase 1: Apply configured delay
   - Phase 2: Drive signals and check for FIFO full
   - Phase 3: Complete transfer and update statistics
4. **Completion**: Completed transactions are added to `sent_queue`

### Memory Integration

When a memory model is provided, the master can automatically update memory:

```python
if hasattr(self, 'memory_integration') and self.memory_model and 'write' in kwargs and kwargs['write']:
    success, error_msg = self.memory_integration.write(transaction)
    if not success:
        self.log.error(f"Master({self.title}): {error_msg}")
```

The `memory_integration` object handles the details of writing to memory.

### Statistics Tracking

The master tracks various statistics to aid in debugging and performance analysis:

```python
self.stats = {
    'transactions_sent': 0,
    'timeouts': 0,
    'write_while_full': 0,
    'full_cycles': 0
}
```

## Usage Examples

### Basic Usage

```python
# Create a FIFO master
field_config = FieldConfig.create_data_only(32)
master = FIFOMaster(dut, "FIFO1_Master", "", clock, field_config)

# Send a transaction
packet = FIFOPacket(field_config)
packet.data = 0x12345678
await master.send(packet)

# Check results
print(f"Transactions sent: {master.get_stats()['transactions_sent']}")
```

### With Memory Model

```python
# Create a memory model
memory_model = EnhancedMemoryModel(num_lines=8, bytes_per_line=4)

# Create master with memory integration
master = FIFOMaster(
    dut, "Master", "", clock,
    field_config=field_config,
    memory_model=memory_model
)

# Send a write transaction
packet = FIFOPacket(field_config)
packet.data = 0xABCDEF01
packet.addr = 0x00000004
await master.send(packet, write=True)  # 'write' triggers memory update
```

### Using Randomized Timing

```python
# Define timing constraints
constraints = {
    'write_delay': ([[0, 0], [1, 3], [4, 10]], [0.5, 0.3, 0.2])
}

# Create randomizer and master
randomizer = FlexRandomizer(constraints)
master = FIFOMaster(
    dut, "Master", "", clock,
    field_config=field_config,
    randomizer=randomizer
)

# Now sends will have randomized delays
for i in range(10):
    packet = FIFOPacket(field_config)
    packet.data = i
    await master.send(packet)
```

### Using Multi-Signal Mode

```python
# Create field config for multi-field packets
field_config = FieldConfig()
field_config.add_field(FieldDefinition(name="addr", bits=16))
field_config.add_field(FieldDefinition(name="data", bits=32))
field_config.add_field(FieldDefinition(name="strb", bits=4))

# Create signal map for multi-signal mode
signal_map = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full',
    'i_wr_pkt_addr': 'i_addr',
    'i_wr_pkt_data': 'i_data',
    'i_wr_pkt_strb': 'i_strb'
}

# Create master in multi-signal mode
master = FIFOMaster(
    dut, "Master", "", clock,
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map
)

# Send a transaction - fields will go to separate signals
packet = FIFOPacket(field_config)
packet.addr = 0x1234
packet.data = 0xABCDEF01
packet.strb = 0xF
await master.send(packet)
```

## Error Handling

The FIFOMaster implements several error handling mechanisms:

1. **Field Value Validation**:
   ```python
   field_value = self._check_field_value(field_name, field_value)
   ```

2. **FIFO Full Detection**:
   ```python
   if self.full_sig.value and self.write_sig.value:
       self.log.error(f"Error: {self.title} write while fifo full")
       self.stats['write_while_full'] += 1
   ```

3. **Timeout Detection**:
   ```python
   if timeout_counter >= self.timeout_cycles:
       self.log.error(f"TIMEOUT waiting for FIFO not full")
       self.stats['timeouts'] += 1
       return False
   ```

4. **Memory Integration Errors**:
   ```python
   success, error_msg = self.memory_integration.write(transaction)
   if not success:
       self.log.error(f"Master({self.title}): {error_msg}")
   ```

## Integration with Other Components

The FIFOMaster is designed to work with:

- **FIFOSlave**: For reading from the other end of the FIFO
- **FIFOMonitor**: For observing FIFO activity
- **FIFOCommandHandler**: For coordinating master-slave communication
- **Memory Models**: For data storage integration

## Performance Considerations

1. **Caching**: The master caches field masks and other calculations
2. **Pipeline Structure**: The transmission pipeline efficiently processes queued transactions
3. **Memory Integration**: Direct memory access avoids redundant operations
4. **Flexible Timing**: Randomized delays can model real-world timing constraints

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
