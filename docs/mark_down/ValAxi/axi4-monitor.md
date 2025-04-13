# AXI4 Monitor Component Documentation

## Introduction

The AXI4 Monitor is a passive component that observes transactions on an AXI4 interface without interfering with them. It captures transaction details from all AXI4 channels and provides analysis capabilities for verification. This document details how to configure and use the AXI4 Monitor component.

## Architecture

The AXI4 Monitor consists of individual channel monitors for each AXI4 channel:

- **AW Channel Monitor**: Observes write address transactions
- **W Channel Monitor**: Observes write data transactions
- **B Channel Monitor**: Observes write response transactions
- **AR Channel Monitor**: Observes read address transactions
- **R Channel Monitor**: Observes read data transactions

The monitor component coordinates these channel monitors to reconstruct complete transactions and provide transaction-level visibility.

## Instantiation

### Basic Instantiation

To create an AXI4 Monitor, use the factory function:

```python
from axi4_factory import create_axi4_monitor

monitor = create_axi4_monitor(
    dut=dut,                 # Device under test
    title="my_axi4_monitor",  # Component name
    prefix="m_axi",          # Signal prefix
    divider="_",             # Signal divider
    suffix="",               # Signal suffix
    clock=dut.clk,           # Clock signal
    channels=["AW", "W", "B", "AR", "R"],  # Channels to monitor
    id_width=8,              # ID width in bits
    addr_width=32,           # Address width in bits
    data_width=32,           # Data width in bits
    user_width=1,            # User signal width in bits
    is_slave_side=False,     # Whether to monitor slave-side signals
    check_protocol=True,     # Enable protocol checking
    log=logger               # Logger instance
)
```

### Monitor Type

The `is_slave_side` parameter controls which side of the interface is monitored:

- `is_slave_side=False`: Monitor master-driven signals (default)
- `is_slave_side=True`: Monitor slave-driven signals

This is particularly important when monitoring B and R channels, which are driven by the slave.

## Transaction Tracking

The monitor automatically tracks and correlates transactions across channels:

- Write transactions are tracked from AW channel through W channel to B channel
- Read transactions are tracked from AR channel through R channel

The monitor maintains internal data structures to track pending transactions and match responses with requests.

## Callbacks

### Setting Callbacks

The primary way to use the monitor is to register callbacks that will be invoked when transactions are detected:

```python
# Set callback for completed write transactions
monitor.set_write_callback(my_write_callback)

# Set callback for completed read transactions
monitor.set_read_callback(my_read_callback)
```

### Callback Signatures

Callbacks should have the following signatures:

```python
# Write transaction callback
def my_write_callback(id_value, transaction_info):
    # id_value: Transaction ID
    # transaction_info: Dictionary with transaction details
    pass

# Read transaction callback
def my_read_callback(id_value, transaction_info):
    # id_value: Transaction ID
    # transaction_info: Dictionary with transaction details
    pass
```

### Transaction Information

The `transaction_info` dictionary contains:

For write transactions:
- `aw_transaction`: AW channel transaction packet
- `w_transactions`: List of W channel transaction packets
- `b_transaction`: B channel transaction packet
- `addresses`: List of addresses accessed in the burst
- `start_time`: Transaction start time
- `end_time`: Transaction end time
- `duration`: Transaction duration
- `complete`: Boolean indicating transaction completion

For read transactions:
- `ar_transaction`: AR channel transaction packet
- `r_transactions`: List of R channel transaction packets
- `addresses`: List of addresses accessed in the burst
- `data`: List of data values read
- `start_time`: Transaction start time
- `end_time`: Transaction end time
- `duration`: Transaction duration
- `complete`: Boolean indicating transaction completion

## Protocol Checking

When `check_protocol=True`, the monitor validates transactions against AXI4 protocol rules:

- Address alignment for the specified burst size
- Valid burst types (FIXED, INCR, WRAP)
- Valid burst lengths (especially for WRAP bursts)
- Proper address increments for burst transactions
- Response code validity
- Last signal presence for multi-beat transactions

Protocol violations are logged at warning or error level.

## Advanced Usage

### Direct Channel Callbacks

For more detailed analysis, you can register callbacks for individual channels:

```python
# Register callback for AW channel
monitor.aw_monitor.add_callback(my_aw_callback)

# Register callback for AR channel
monitor.ar_monitor.add_callback(my_ar_callback)

# And similarly for other channels
```

These callbacks will be invoked for each individual channel transaction, rather than for complete transactions.

### Burst Address Calculation

The monitor automatically calculates all addresses in a burst based on the AXI4 protocol rules:

- **FIXED bursts**: Same address for all transfers
- **INCR bursts**: Address increments by the transfer size
- **WRAP bursts**: Address increments and wraps at boundaries

These calculated addresses are provided in the `addresses` field of the transaction info.

## Integration with Scoreboard

The monitor is commonly connected to a scoreboard for transaction checking:

```python
from axi4_factory import create_axi4_scoreboard

# Create a scoreboard
scoreboard = create_axi4_scoreboard(
    name="my_scoreboard",
    id_width=8,
    addr_width=32,
    data_width=32,
    user_width=1,
    log=logger
)

# Connect monitor to scoreboard
monitor.set_write_callback(scoreboard.check_write)
monitor.set_read_callback(scoreboard.check_read)
```

## Performance Considerations

For high-performance simulations with many transactions, consider the following:

- Disable protocol checking (`check_protocol=False`) to reduce overhead
- Use callbacks that perform minimal processing
- Monitor only the specific channels you need

## Example Usage

Here's a complete example of using the AXI4 Monitor:

```python
async def run_monitor_test(dut):
    # Create a monitor
    monitor = create_axi4_monitor(
        dut=dut,
        title="monitor",
        prefix="m_axi",
        divider="_",
        suffix="",
        clock=dut.clk,
        channels=["AW", "W", "B", "AR", "R"],
        id_width=8,
        addr_width=32,
        data_width=32,
        is_slave_side=False,
        check_protocol=True,
        log=logger
    )
    
    # Transaction counts for statistics
    write_count = 0
    read_count = 0
    
    # Define callbacks
    def write_callback(id_value, transaction_info):
        nonlocal write_count
        write_count += 1
        
        aw_transaction = transaction_info['aw_transaction']
        b_transaction = transaction_info['b_transaction']
        
        print(f"Write Transaction {write_count}:")
        print(f"  ID: {id_value}")
        print(f"  Address: 0x{aw_transaction.awaddr:08X}")
        print(f"  Response: {b_transaction.bresp}")
        print(f"  Duration: {transaction_info['duration']} ns")
    
    def read_callback(id_value, transaction_info):
        nonlocal read_count
        read_count += 1
        
        ar_transaction = transaction_info['ar_transaction']
        data = transaction_info['data']
        
        print(f"Read Transaction {read_count}:")
        print(f"  ID: {id_value}")
        print(f"  Address: 0x{ar_transaction.araddr:08X}")
        print(f"  Data: {[f'0x{d:08X}' for d in data]}")
        print(f"  Duration: {transaction_info['duration']} ns")
    
    # Register callbacks
    monitor.set_write_callback(write_callback)
    monitor.set_read_callback(read_callback)
    
    # Run simulation for specified time
    for _ in range(1000):
        await RisingEdge(dut.clk)
    
    print(f"Total Transactions - Writes: {write_count}, Reads: {read_count}")
```

## Creating a Transaction Logger

The monitor can be used to build a comprehensive transaction log:

```python
class AXI4TransactionLogger:
    def __init__(self, filename="axi4_transactions.log"):
        self.filename = filename
        self.log_file = open(filename, "w")
        self.write_count = 0
        self.read_count = 0
        
        # Write header
        self.log_file.write("Time,Type,ID,Address,BurstLen,BurstType,Size,Response,Data\n")
    
    def close(self):
        self.log_file.close()
    
    def handle_write(self, id_value, transaction_info):
        self.write_count += 1
        
        aw = transaction_info['aw_transaction']
        b = transaction_info['b_transaction']
        
        # Get data as comma-separated hex values
        data_values = [w.wdata for w in transaction_info['w_transactions']]
        data_str = ",".join([f"0x{d:08X}" for d in data_values])
        
        # Write to log
        self.log_file.write(f"{transaction_info['start_time']},WRITE,{id_value},"
                           f"0x{aw.awaddr:08X},{aw.awlen},{aw.awburst},{aw.awsize},"
                           f"{b.bresp},\"{data_str}\"\n")
        self.log_file.flush()
    
    def handle_read(self, id_value, transaction_info):
        self.read_count += 1
        
        ar = transaction_info['ar_transaction']
        
        # Get data as comma-separated hex values
        data_values = transaction_info['data']
        data_str = ",".join([f"0x{d:08X}" for d in data_values])
        
        # Get response from last R packet
        resp = transaction_info['r_transactions'][-1].rresp if transaction_info['r_transactions'] else 0
        
        # Write to log
        self.log_file.write(f"{transaction_info['start_time']},READ,{id_value},"
                           f"0x{ar.araddr:08X},{ar.arlen},{ar.arburst},{ar.arsize},"
                           f"{resp},\"{data_str}\"\n")
        self.log_file.flush()

# Usage:
logger = AXI4TransactionLogger()
monitor.set_write_callback(logger.handle_write)
monitor.set_read_callback(logger.handle_read)

# After simulation:
logger.close()
```

## Troubleshooting

Common issues and their solutions:

1. **Missing transactions**: Check that the monitor is connected to the correct signals and that the prefix/divider/suffix match the actual signal names.

2. **Incomplete transactions**: The monitor might not detect the end of a transaction if the simulation ends too early. Ensure the simulation runs long enough for all transactions to complete.

3. **Protocol violations**: These are reported by the monitor but might indicate issues in the AXI4 master or slave components. Review the reported violations to debug the source of the problem.

4. **Callbacks not invoked**: Ensure that the callbacks are correctly registered and that the monitored transactions are actually completing.

5. **Signal connectivity issues**: Use simulator waveform viewing to check that signals are actively changing during transactions.
