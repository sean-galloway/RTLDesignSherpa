# FIFO Slave Documentation

## Overview

`fifo_slave.py` implements the FIFOSlave component, which controls the read interface of a FIFO. It drives the read control signal, monitors the empty signal, and processes data from the FIFO according to the protocol. The slave component supports various operation modes, timing constraints, and enhanced memory integration.

## Class: FIFOSlave

The FIFOSlave class extends `BusMonitor` from `cocotb_bus` and provides comprehensive functionality for operating the read side of a FIFO interface.

```python
class FIFOSlave(BusMonitor):
    """
    Slave driver for FIFO transactions with enhanced memory integration.
    Controls read signal and monitors empty signal.
    """
```

### Key Features

- **Multiple Signal Modes**:
  - Standard mode with single data bus
  - Multi-signal mode with separate signals for each field
  
- **Multiple Operating Modes**:
  - `fifo_mux`: Uses combinational signals (ow_rd_data)
  - `fifo_flop`: Uses registered signals (o_rd_data with one cycle delay)
  
- **Field Mode Support**:
  - Processes standard data bus as multiple fields
  - Automatically unpacks fields from combined values
  
- **Memory Integration**:
  - Optional integration with memory models
  - Automatic read from memory when receiving transactions
  
- **Timing Randomization**:
  - Configurable random delays between reads
  - Supports various distribution patterns
  
- **Error Detection**:
  - Detects protocol violations (read while empty)
  - Validates field values against field widths
  
- **Comprehensive Statistics**:
  - Tracks transactions, protocol violations, and timing
  - Records FIFO emptiness metrics

### Initialization

```python
def __init__(self, dut, title, prefix, clock,
            field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
            randomizer=None, memory_model=None, memory_fields=None,
            field_mode=False, multi_sig=False, log=None, mode='fifo_mux', 
            signal_map=None, optional_signal_map=None, **kwargs):
    """Initialize the FIFO slave."""
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
- **field_mode**: If True, treat data bus as containing multiple fields
- **multi_sig**: If True, use separate signals for each field
- **log**: Logger instance
- **mode**: 'fifo_mux' or 'fifo_flop'
- **signal_map**: Dictionary mapping FIFO signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional FIFO signals to DUT signals

### Standard Signal Names

```python
# Standard Signal names
fifo_read = 'i_read'         # Read control signal
fifo_rd_empty = 'o_rd_empty' # FIFO empty indicator
fifo_rd_data = 'o_rd_data'   # Read data bus (registered)
fifo_rd_data_wire = 'ow_rd_data'  # Read data bus (combinational, for fifo_mux mode)
```

### Valid Operation Modes

```python
fifo_valid_modes = ['fifo_mux', 'fifo_flop']
```

### Key Methods

#### Basic Operations

- **reset_bus()**:
  Reset the bus to initial state.
  
- **process_request(transaction)**:
  Process a transaction request directly from a command handler.
  
- **add_callback(callback)**:
  Add a callback function to be called when a packet is received.

#### Configuration

- **set_randomizer(randomizer)**:
  Set a new randomizer for timing constraints.
  
- **set_memory_model(memory_model, memory_fields=None)**:
  Set or update the memory model.

#### Internal Monitor Methods

- **_monitor_recv()**:
  Main monitoring loop for incoming transactions.
  
- **_recv_phase1(last_packet, last_xfer)**:
  First phase: Handle pending transactions from previous cycle.
  
- **_recv_phase2()**:
  Second phase: Handle read delays and assert read if not empty.
  
- **_recv_phase3(current_time)**:
  Third phase: Check for valid read and process transaction.

#### Signal Handling

- **_set_rd_ready(value)**:
  Set the read signal to specified value.
  
- **_get_data_dict()**:
  Collect data from field signals in multi-signal mode.
  
- **_finish_packet(current_time, packet, data_dict=None)**:
  Finish packet processing and trigger callbacks.
  
- **_finish_packet_helper(combined_value, unpacked_fields)**:
  Helper method to extract individual fields from combined value.

#### Utility Methods

- **wait_cycles(cycles)**:
  Wait for a number of clock cycles.
  
- **get_memory_stats()**:
  Get memory operation statistics.
  
- **get_stats()**:
  Get transaction statistics.
  
- **_check_field_value(field_name, field_value)**:
  Check if a field value exceeds the maximum possible value.

### Multi-Signal Mode

In multi-signal mode, the slave creates individual signals for each field:

```python
# Example signal mapping in multi-signal mode
field_signal_name = f'o_rd_pkt_{field_name}'
```

The method `_initialize_multi_signal_mode()` handles setup of these signals.

### Operation Modes

#### fifo_mux Mode

In `fifo_mux` mode, data values are available in the same cycle as the read handshake:

```
Clock        : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
i_read       : __|‾‾‾‾‾‾|_____________
o_rd_empty   : ‾‾|_______|‾‾‾‾‾‾‾‾‾‾‾‾‾
ow_rd_data   : --X Valid X--------------
```

The slave uses the `ow_rd_data` (wire) signal in this mode.

#### fifo_flop Mode

In `fifo_flop` mode, data values are available in the cycle after the read handshake:

```
Clock        : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
i_read       : __|‾‾‾‾‾‾|_____________
o_rd_empty   : ‾‾|_______|‾‾‾‾‾‾‾‾‾‾‾‾‾
o_rd_data    : ---------X Valid X-------
```

The slave uses the `o_rd_data` (registered) signal in this mode.

### Monitor Implementation

The slave extends the BusMonitor class but customizes the monitor behavior:

1. The `_monitor_recv()` method runs continuously in a coroutine
2. It calls different phase methods for each stage of transaction processing
3. When a valid read is detected, a packet is created and processed
4. The slave handles packet completion, memory integration, and callbacks

### Memory Integration

When a memory model is provided, the slave can automatically read from memory:

```python
if hasattr(self, 'memory_integration') and self.memory_model:
    success, data, error_msg = self.memory_integration.read(packet, update_transaction=True)
    if not success:
        self.log.warning(f"Slave({self.title}): {error_msg}")
```

The `memory_integration` object handles the details of reading from memory.

### Statistics Tracking

The slave tracks various statistics to aid in debugging and performance analysis:

```python
self.stats = {
    'transactions_received': 0,
    'empty_cycles': 0,
    'read_while_empty': 0,
    'received_transactions': 0
}
```

## Usage Examples

### Basic Usage

```python
# Create a FIFO slave
field_config = FieldConfig.create_data_only(32)
slave = FIFOSlave(dut, "FIFO1_Slave", "", clock, field_config)

# Start monitoring
cocotb.start_soon(slave._monitor_recv())

# Add a callback to process received packets
def process_packet(packet):
    print(f"Received packet with data: 0x{packet.data:08X}")

slave.add_callback(process_packet)
```

### With Memory Model

```python
# Create a memory model with initial data
memory_model = EnhancedMemoryModel(num_lines=8, bytes_per_line=4)
# Preset some values
for i in range(8):
    memory_model.write(i*4, bytearray([i, i+1, i+2, i+3]), 0xF)

# Create slave with memory integration
slave = FIFOSlave(
    dut, "Slave", "", clock,
    field_config=field_config,
    memory_model=memory_model
)

# Start monitoring - received packets will be populated with memory data
cocotb.start_soon(slave._monitor_recv())
```

### Using Different Operating Modes

```python
# Create a slave in fifo_flop mode
slave_flop = FIFOSlave(
    dut, "Slave_Flop", "", clock,
    field_config=field_config,
    mode='fifo_flop'
)

# Create a slave in fifo_mux mode
slave_mux = FIFOSlave(
    dut, "Slave_Mux", "", clock,
    field_config=field_config,
    mode='fifo_mux'
)
```

### Using Multi-Signal Mode

```python
# Create field config for multi-field packets
field_config = FieldConfig()
field_config.add_field(FieldDefinition(name="addr", bits=16))
field_config.add_field(FieldDefinition(name="data", bits=32))

# Create signal map for multi-signal mode
signal_map = {
    'i_read': 'i_read',
    'o_rd_empty': 'o_rd_empty'
}

optional_signal_map = {
    'o_rd_pkt_addr': 'o_addr',
    'o_rd_pkt_data': 'o_data'
}

# Create slave in multi-signal mode
slave = FIFOSlave(
    dut, "Slave", "", clock,
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map,
    optional_signal_map=optional_signal_map
)
```

### Direct Request Processing

```python
# Create a transaction to process
packet = FIFOPacket(field_config)
packet.addr = 0x1000
packet.data = 0x0  # Will be filled from memory

# Process directly without going through signals
response = await slave.process_request(packet)

# Check the response
print(f"Response data: 0x{response.data:08X}")
```

## Error Handling

The FIFOSlave implements several error handling mechanisms:

1. **Field Value Validation**:
   ```python
   field_value = self._check_field_value(field_name, field_value)
   ```

2. **Empty FIFO Detection**:
   ```python
   if (self.read_sig.value.is_resolvable and
       self.empty_sig.value.is_resolvable and
       int(self.read_sig.value) == 1 and
       int(self.empty_sig.value) == 1):
       self.stats['read_while_empty'] += 1
   ```

3. **Memory Integration Errors**:
   ```python
   success, data, error_msg = self.memory_integration.read(packet)
   if not success:
       self.log.warning(f"Slave({self.title}): {error_msg}")
   ```

4. **X/Z Value Handling**:
   ```python
   if not signal.value.is_resolvable:
       self.log.warning(f"Field {field_name} has X/Z value")
       data_dict[field_name] = -1  # Indicate X/Z value
   ```

## Integration with Other Components

The FIFOSlave is designed to work with:

- **FIFOMaster**: For writing to the other end of the FIFO
- **FIFOMonitor**: For observing FIFO activity
- **FIFOCommandHandler**: For coordinating master-slave communication
- **Memory Models**: For data storage integration

## Performance Considerations

1. **Caching**: The slave caches field masks and other calculations
2. **Phase Structure**: The monitor phases efficiently handle different timing requirements
3. **Memory Integration**: Direct memory access avoids redundant operations
4. **Flexible Timing**: Randomized delays can model real-world timing constraints

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
