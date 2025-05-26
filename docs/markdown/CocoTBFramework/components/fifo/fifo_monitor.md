# FIFO Monitor Documentation

## Overview

`fifo_monitor.py` implements the FIFOMonitor component, which passively observes FIFO interface signals without driving them. It detects protocol violations, tracks timing and protocol statistics, and provides visibility into FIFO operations for verification and debugging.

## Class: FIFOMonitor

The FIFOMonitor class extends `BusMonitor` from `cocotb_bus` and implements a non-intrusive monitoring capability for FIFO interfaces.

```python
class FIFOMonitor(BusMonitor):
    """
    Monitor for FIFO bus transactions with enhanced signal handling and error detection.
    Observes signals without driving anything.
    """
```

### Key Features

- **Dual Port Monitoring**:
  - Can monitor either read port (`is_slave=True`) or write port (`is_slave=False`)
  - Adapts to the appropriate signals for each port
  
- **Multiple Signal Modes**:
  - Standard mode with single data bus
  - Multi-signal mode with separate signals for each field
  
- **Multiple Operating Modes**:
  - `fifo_mux`: Monitors combinational signals
  - `fifo_flop`: Monitors registered signals with cycle delay handling
  
- **Protocol Validation**:
  - Detects read-while-empty violations
  - Detects write-while-full violations
  - Validates signal values against expected ranges
  
- **FIFO Depth Tracking**:
  - Estimates current FIFO depth based on operations
  - Calculates utilization statistics
  
- **Signal Quality Monitoring**:
  - Detects X/Z values on signals
  - Reports undefined signal states
  
- **Comprehensive Statistics**:
  - Tracks transactions, protocol violations, and timing
  - Records FIFO fullness/emptiness metrics

### Initialization

```python
def __init__(self, dut, title, prefix, clock, is_slave=False,
            field_config=None, packet_class=FIFOPacket, timeout_cycles=1000,
            field_mode=False, multi_sig=False, log=None, mode='fifo_mux', 
            signal_map=None, optional_signal_map=None, **kwargs):
    """Initialize the FIFO bus monitor."""
```

#### Parameters

- **dut**: Device under test
- **title**: Title of the bus
- **prefix**: Signal prefix
- **clock**: Clock signal
- **is_slave**: If True, monitor read port; if False, monitor write port
- **field_config**: Field configuration for packets
- **packet_class**: Class to use for creating packets
- **timeout_cycles**: Maximum cycles to wait before timeout
- **field_mode**: If True, treat data bus as containing multiple fields
- **multi_sig**: If True, use separate signals for each field
- **log**: Logger instance
- **mode**: 'fifo_mux' or 'fifo_flop'
- **signal_map**: Dictionary mapping FIFO signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional FIFO signals to DUT signals

### Standard Signal Names

```python
# Standard Signal names for write port
fifo_write = 'i_write'
fifo_wr_full = 'o_wr_full'
fifo_wr_data = 'i_wr_data'

# Standard Signal names for read port
fifo_read = 'i_read'
fifo_rd_empty = 'o_rd_empty'
fifo_rd_data = 'o_rd_data'
fifo_rd_data_wire = 'ow_rd_data'  # for fifo_mux mode
```

### Valid Operation Modes

```python
fifo_valid_modes = ['fifo_mux', 'fifo_flop']
```

### Key Methods

#### Basic Operations

- **set_fifo_capacity(capacity)**:
  Set the assumed FIFO capacity for depth tracking.
  
- **add_callback(callback)**:
  Add a callback function to be called when a packet is observed.
  
- **clear_queue()**:
  Clear the observed transactions queue.
  
- **get_observed_packets(count=None)**:
  Get observed packets from the queue.

#### Statistics and State

- **get_stats()**:
  Get statistics about observed transactions.
  
- **_update_fifo_depth(is_write)**:
  Update the estimated FIFO depth based on the operation.
  
- **_check_protocol_violation(is_write)**:
  Check for protocol violations based on signals.

#### Internal Monitor Methods

- **_monitor_recv()**:
  Main monitoring loop for transactions.
  
- **_call_callbacks(packet)**:
  Call all registered callbacks with the packet.
  
- **_finish_packet(current_time, packet, data_dict=None)**:
  Finish packet processing and add to the observed queue.

#### Signal Handling

- **_initialize_multi_signal_mode()**:
  Initialize signal mappings for multi-signal mode.
  
- **_register_field_signal(field_name, dut_signal_name, required=False)**:
  Register a field signal with appropriate error handling.
  
- **_get_data_dict()**:
  Collect data from field signals with robust X/Z handling.
  
- **_finish_packet_helper(combined_value, unpacked_fields)**:
  Helper method to extract individual fields from combined value.

#### Utility Methods

- **_check_field_value(field_name, field_value)**:
  Check if a field value exceeds the maximum possible value.

### How Monitoring Works

The monitor operates through a continuous monitoring loop:

1. Waits for a falling edge of the clock to sample signals
2. Checks for protocol violations
3. Detects valid operations (read or write) based on control signals
4. Creates packets for observed transactions
5. Captures data values from appropriate signals
6. Updates FIFO depth tracking
7. Adds completed packets to the observed queue
8. Calls registered callbacks with packets
9. Updates statistics

### Statistics Tracking

The monitor tracks comprehensive statistics:

```python
self.stats = {
    'transactions_observed': 0,
    'protocol_violations': 0,
    'x_z_values': 0,
    'empty_cycles': 0,
    'full_cycles': 0,
    'read_while_empty': 0,
    'write_while_full': 0,
    'received_transactions': 0
}
```

## Usage Examples

### Basic Write Port Monitoring

```python
# Create a monitor for the write port
field_config = FieldConfig.create_data_only(32)
write_monitor = FIFOMonitor(
    dut, "Write_Monitor", "", clock,
    is_slave=False,  # Monitor write port
    field_config=field_config
)

# Start monitoring
cocotb.start_soon(write_monitor._monitor_recv())

# Add a callback to process observed packets
def log_write(packet):
    print(f"Observed write: data=0x{packet.data:08X}")

write_monitor.add_callback(log_write)
```

### Read Port Monitoring with fifo_flop Mode

```python
# Create a monitor for the read port in fifo_flop mode
read_monitor = FIFOMonitor(
    dut, "Read_Monitor", "", clock,
    is_slave=True,  # Monitor read port
    field_config=field_config,
    mode='fifo_flop'  # Use registered data signals
)

# Start monitoring
cocotb.start_soon(read_monitor._monitor_recv())

# Add a callback to process observed packets
def log_read(packet):
    print(f"Observed read: data=0x{packet.data:08X}")

read_monitor.add_callback(log_read)
```

### Multi-Signal Mode Monitoring

```python
# Create field config for multi-field packets
field_config = FieldConfig()
field_config.add_field(FieldDefinition(name="addr", bits=16))
field_config.add_field(FieldDefinition(name="data", bits=32))

# Create signal map for multi-signal mode
signal_map = {
    'i_write': 'i_write',
    'o_wr_full': 'o_wr_full'
}

optional_signal_map = {
    'i_wr_pkt_addr': 'i_addr',
    'i_wr_pkt_data': 'i_data'
}

# Create monitor in multi-signal mode
monitor = FIFOMonitor(
    dut, "Multi_Monitor", "", clock,
    is_slave=False,
    field_config=field_config,
    multi_sig=True,
    signal_map=signal_map,
    optional_signal_map=optional_signal_map
)

# Start monitoring
cocotb.start_soon(monitor._monitor_recv())
```

### Collecting and Analyzing Statistics

```python
# Create a monitor with defined FIFO capacity
monitor = FIFOMonitor(
    dut, "Stats_Monitor", "", clock,
    field_config=field_config
)
monitor.set_fifo_capacity(8)  # 8 entry FIFO

# Start monitoring
cocotb.start_soon(monitor._monitor_recv())

# Run test sequence...

# Analyze statistics
stats = monitor.get_stats()
print(f"Transactions observed: {stats['transactions_observed']}")
print(f"Protocol violations: {stats['protocol_violations']}")
print(f"FIFO utilization: {stats['utilization_percentage']:.2f}%")

if stats['protocol_violations'] > 0:
    print("WARNING: Protocol violations detected!")
```

### Using with a Scoreboard

```python
# Create a FIFO scoreboard
scoreboard = FIFOScoreboard("FIFO_Scoreboard", field_config)

# Create write and read monitors
write_monitor = FIFOMonitor(dut, "Write_Monitor", "", clock, is_slave=False, field_config=field_config)
read_monitor = FIFOMonitor(dut, "Read_Monitor", "", clock, is_slave=True, field_config=field_config)

# Connect monitors to scoreboard
write_monitor.add_callback(scoreboard.add_expected)
read_monitor.add_callback(scoreboard.add_actual)

# Start monitoring
cocotb.start_soon(write_monitor._monitor_recv())
cocotb.start_soon(read_monitor._monitor_recv())

# At end of test
print(f"Scoreboard results: {scoreboard.get_stats()}")
```

## Error Handling

The FIFOMonitor implements several error handling mechanisms:

1. **Protocol Violation Detection**:
   ```python
   def _check_protocol_violation(self, is_write):
       if is_write:
           # Check for write while full violation
           if (self.control1_sig.value.is_resolvable and 
               self.control2_sig.value.is_resolvable and
               int(self.control1_sig.value) == 1 and
               int(self.control2_sig.value) == 1):
               self.log.warning(f"Protocol violation - write while full")
               self.stats['protocol_violations'] += 1
               return True
   ```

2. **X/Z Value Detection**:
   ```python
   if not signal.value.is_resolvable:
       self.log.warning(f"Field {field_name} has X/Z value")
       data_dict[field_name] = -1  # Use -1 to indicate X/Z
       self.stats['x_z_values'] += 1
   ```

3. **Field Value Validation**:
   ```python
   field_value = self._check_field_value(field_name, field_value)
   ```

4. **Exception Recovery**:
   ```python
   try:
       # Monitor loop implementation
   except Exception as e:
       self.log.error(f"Exception in _monitor_recv: {e}")
       import traceback
       self.log.error(traceback.format_exc())
       raise
   ```

## Integration with Other Components

The FIFOMonitor is designed to work with:

- **FIFOMaster**: For monitoring write operations
- **FIFOSlave**: For monitoring read operations
- **FIFOCommandHandler**: For end-to-end transaction tracing
- **FIFOScoreboard**: For comparing expected vs. actual transactions
- **Test Benches**: For verification and debugging

## Handling Different FIFO Modes

### fifo_mux Mode

In `fifo_mux` mode, data values are available in the same cycle as the handshake:

```
Clock        : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
i_read       : __|‾‾‾‾‾‾|_____________
o_rd_empty   : ‾‾|_______|‾‾‾‾‾‾‾‾‾‾‾‾‾
ow_rd_data   : --X Valid X--------------
```

The monitor captures data in the same cycle as the control handshake.

### fifo_flop Mode

In `fifo_flop` mode, data values are available in the cycle after the handshake:

```
Clock        : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
i_read       : __|‾‾‾‾‾‾|_____________
o_rd_empty   : ‾‾|_______|‾‾‾‾‾‾‾‾‾‾‾‾‾
o_rd_data    : ---------X Valid X-------
```

The monitor uses a pending capture mechanism to handle the delayed data:

```python
if pending_capture and self.mode == 'fifo_flop':
    data_dict = self._get_data_dict()
    self._finish_packet(current_time, pending_packet, data_dict)
    pending_capture = False
    pending_packet = None
```

## Performance Considerations

1. **Non-Intrusive**: The monitor only observes signals without driving them
2. **Efficient Sampling**: Uses falling edge to ensure stable signal values
3. **Caching**: Caches field calculations for better performance
4. **Minimal Processing**: Focuses on essential validation and statistics

## Navigation

[↑ FIFO Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
