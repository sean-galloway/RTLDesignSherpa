# GAXIMonitor Component

## Overview

The `GAXIMonitor` component observes GAXI transactions without driving any signals, capturing valid/ready handshakes and associated data. It can monitor either the master side or slave side of a GAXI interface and supports both standard and multi-signal modes.

## Key Features

- Monitors valid/ready handshakes without driving signals
- Works with both master side and slave side interfaces
- Supports multiple operating modes: 'skid', 'fifo_mux', and 'fifo_flop'
- Supports both standard mode (single data bus) and multi-signal mode (individual signals per field)
- Queues observed transactions for later analysis
- Unpacks fields from combined values when needed
- Provides callbacks for custom transaction handling

## Class Definition

```python
class GAXIMonitor(BusMonitor):
    def __init__(self, dut, title, prefix, clock, is_slave=False,
                field_config=None, packet_class=GAXIPacket, timeout_cycles=1000,
                field_mode=False, multi_sig=False, log=None, mode='skid', 
                signal_map=None, optional_signal_map=None, **kwargs):
        # ...
```

## Parameters

- **dut**: Device under test
- **title**: Title of the component
- **prefix**: Signal prefix used in the bus code
- **clock**: Clock signal
- **is_slave**: If True, monitor slave side; if False, monitor master side
- **field_config**: Field configuration for packets
- **packet_class**: Class to use for creating packets (default: `GAXIPacket`)
- **timeout_cycles**: Maximum cycles to wait before timeout (default: 1000)
- **field_mode**: If True, use field mode with multiple fields packed into a single signal (default: False)
- **multi_sig**: If True, use multiple signals mode (default: False)
- **log**: Logger instance
- **mode**: Operating mode ('skid', 'fifo_mux', 'fifo_flop') (default: 'skid')
- **signal_map**: Dictionary mapping required GAXI signals to DUT signals
- **optional_signal_map**: Dictionary mapping optional GAXI signals to DUT signals

## Operating Modes

The monitor component supports three operating modes:

1. **skid**: Standard mode where data is captured immediately on valid/ready handshake
2. **fifo_mux**: FIFO multiplexer mode, uses 'ow_rd_data' signal instead of 'o_rd_data'
3. **fifo_flop**: FIFO flip-flop mode, captures data one clock after valid/ready handshake

## Signal Mapping

The monitor component uses the same signal naming conventions as the master and slave components, with the appropriate mapping based on whether it's monitoring the master side or slave side.

For master side (is_slave=False):
```python
master_signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
master_optional_signal_map = {
    'm2s_pkt': 'i_wr_data'
}
```

For slave side (is_slave=True):
```python
slave_signal_map = {
    'm2s_valid': 'o_rd_valid',
    's2m_ready': 'i_rd_ready'
}
slave_optional_signal_map = {
    'm2s_pkt': 'o_rd_data'  # or 'ow_rd_data' for fifo_mux mode
}
```

## Key Methods

### Queue Management

```python
def clear_queue(self):
    """Clear the observed transactions queue after scoreboard validation"""
    
def add_callback(self, callback):
    """Add a callback function to be called when a transaction is received"""
```

## Internal Methods

```python
# Reception pipeline
async def _monitor_recv(self):
    """Monitor for GAXI transactions following valid/ready handshakes"""
    
async def _recv_phase1(self, current_time, last_packet, last_xfer):
    """Receive phase 1: Handle pending transactions from previous cycle"""
    
async def _recv_phase2(self, current_time, last_packet, last_xfer):
    """Receive phase 2: Check for valid handshake and process transaction"""

# Packet handling  
def _finish_packet(self, current_time, packet, data_dict=None):
    """Finish packet processing and trigger callbacks"""
    
def _get_data_dict(self):
    """Collect data from field signals and properly handle X/Z values"""

# Field value handling
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

# Create a monitor for the master side
master_monitor = GAXIMonitor(
    dut, 'MasterMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=False,  # Monitor master side
    mode='skid'
)

# Create a monitor for the slave side
slave_monitor = GAXIMonitor(
    dut, 'SlaveMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=True,  # Monitor slave side
    mode='skid'
)

# Add callback for transaction processing
def process_transaction(transaction):
    print(f"Observed transaction: {transaction.formatted(compact=True)}")

master_monitor.add_callback(process_transaction)
slave_monitor.add_callback(process_transaction)

# Run the test and let monitors capture transactions
await RisingEdge(dut.clk)

# After the test, check observed transactions
print(f"Master observed {len(master_monitor.observed_queue)} transactions")
print(f"Slave observed {len(slave_monitor.observed_queue)} transactions")

# Process observed transactions
while master_monitor.observed_queue:
    packet = master_monitor.observed_queue.popleft()
    print(f"Master observed data: 0x{packet.data:X}")

while slave_monitor.observed_queue:
    packet = slave_monitor.observed_queue.popleft()
    print(f"Slave observed data: 0x{packet.data:X}")
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

# Signal mapping for multi-signal mode (master side)
master_signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}
master_optional_signal_map = {
    'm2s_pkt_addr': 'i_wr_addr',
    'm2s_pkt_data': 'i_wr_data'
}

# Create a monitor in multi-signal mode
master_monitor = GAXIMonitor(
    dut, 'MasterMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=False,
    multi_sig=True,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_signal_map
)
```

## Scoreboard Integration Example

```python
# Create a GAXI scoreboard
scoreboard = GAXIScoreboard('TestScoreboard', field_config)

# Create monitors for master and slave sides
master_monitor = GAXIMonitor(
    dut, 'MasterMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=False
)

slave_monitor = GAXIMonitor(
    dut, 'SlaveMonitor', '', dut.clk,
    field_config=field_config,
    is_slave=True
)

# Add callbacks to send transactions to scoreboard
def master_callback(transaction):
    scoreboard.add_expected(transaction)

def slave_callback(transaction):
    scoreboard.add_actual(transaction)

master_monitor.add_callback(master_callback)
slave_monitor.add_callback(slave_callback)

# Run the test and let monitors capture transactions
await RisingEdge(dut.clk)

# Check scoreboard results
result = scoreboard.check_complete()
if result:
    print("Scoreboard check passed")
else:
    print("Scoreboard check failed")

# Clear the observed queues after scoreboard checking
master_monitor.clear_queue()
slave_monitor.clear_queue()
```

## FIFO_FLOP Mode Example

```python
# Create a monitor in FIFO_FLOP mode
monitor_fifo_flop = GAXIMonitor(
    dut, 'MonitorFF', '', dut.clk,
    field_config=field_config,
    is_slave=True,
    mode='fifo_flop'
)

# In FIFO_FLOP mode, the monitor will capture data one clock after
# the valid/ready handshake occurs
```

## Tips and Best Practices

1. **Mode Selection**: Choose the appropriate mode based on your DUT implementation
   - 'skid' for standard skid buffers
   - 'fifo_mux' for multiplexed FIFO outputs
   - 'fifo_flop' for flip-flop based FIFOs where data is valid one clock after handshake
2. **Signal Mapping**: Always provide explicit signal mappings for clarity, even if using default names
3. **is_slave Parameter**: Set is_slave=False for monitoring master side, is_slave=True for slave side
4. **Queue Management**: Regularly check and clear the observed_queue to avoid memory buildup
5. **Callbacks**: Use callbacks for real-time transaction processing instead of polling the queue
6. **Multi-Signal Mode**: For complex interfaces, multi_sig=True with individual field signals provides better debug visibility
7. **Field Mode**: When memory is limited, field_mode=True allows packing multiple fields into a single signal
8. **Scoreboard Integration**: Use monitors to feed transactions to a scoreboard for automatic checking
