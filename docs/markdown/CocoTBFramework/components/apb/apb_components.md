# APB Components

## Overview

The APB Components module provides the core implementation of the APB (Advanced Peripheral Bus) protocol components within the CocoTBFramework. It includes the monitor, master driver, and slave responder classes needed to build a complete APB verification environment.

## Features

- Complete APB protocol implementation following AMBA specifications
- Configurable APB monitor for transaction capture
- APB master driver with customizable timing
- APB slave implementation with memory model integration
- Support for all standard APB signals
- Optional handling of extended signals (PPROT, PSLVERR, PSTRB)
- Built-in transaction formatting and logging

## Classes

### APBMonitor

The `APBMonitor` class observes APB bus activity and captures transactions.

#### Constructor

```python
def __init__(self, entity, title, prefix, clock, signals=None,
             bus_width=32, addr_width=12, log=None, **kwargs)
```

- `entity`: DUT (device under test) object
- `title`: Name for this monitor instance
- `prefix`: Signal name prefix
- `clock`: Clock signal
- `signals`: Optional list of signal names to monitor
- `bus_width`: Width of data bus in bits
- `addr_width`: Width of address bus in bits
- `log`: Logger instance
- `**kwargs`: Additional arguments for BusMonitor

#### Key Methods

- `is_signal_present(signal_name)`: Check if a signal is available
- `print(transaction)`: Format and log a transaction
- `_monitor_recv()`: Internal method for transaction capture

### APBSlave

The `APBSlave` class implements an APB slave with memory model.

#### Constructor

```python
def __init__(self, entity, title, prefix, clock, registers, signals=None,
                bus_width=32, addr_width=12, randomizer=None,
                log=None, error_overflow=False, **kwargs)
```

- `entity`: DUT object
- `title`: Name for this slave instance
- `prefix`: Signal name prefix
- `clock`: Clock signal
- `registers`: Register values or memory model
- `signals`: Optional list of signal names
- `bus_width`: Width of data bus in bits
- `addr_width`: Width of address bus in bits
- `randomizer`: Timing randomizer (default: FlexRandomizer)
- `log`: Logger instance
- `error_overflow`: Whether to generate errors on address overflow
- `**kwargs`: Additional arguments for BusMonitor

#### Key Methods

- `set_randomizer(randomizer)`: Update the timing randomizer
- `is_signal_present(signal_name)`: Check if a signal is available
- `dump_registers()`: Display current register values
- `reset_bus()`: Reset the bus interface
- `reset_registers()`: Reset registers to initial values
- `_monitor_recv()`: Internal method for transaction handling
- `_finish_recv(slv_error)`: Complete a transaction

### APBMaster

The `APBMaster` class drives APB transactions on the bus.

#### Constructor

```python
def __init__(self, entity, title, prefix, clock, signals=None,
                bus_width=32, addr_width=12, randomizer=None,
                log=None, **kwargs)
```

- `entity`: DUT object
- `title`: Name for this master instance
- `prefix`: Signal name prefix
- `clock`: Clock signal
- `signals`: Optional list of signal names
- `bus_width`: Width of data bus in bits
- `addr_width`: Width of address bus in bits
- `randomizer`: Timing randomizer (default: FlexRandomizer)
- `log`: Logger instance
- `**kwargs`: Additional arguments for BusDriver

#### Key Methods

- `set_randomizer(randomizer)`: Update the timing randomizer
- `is_signal_present(signal_name)`: Check if a signal is available
- `reset_bus()`: Reset the bus interface
- `busy_send(transaction)`: Send and wait for completion
- `_driver_send(transaction, sync=True, hold=False, **kwargs)`: Internal method to queue transactions
- `_transmit_pipeline()`: Process the transaction queue
- `_finish_xmit(transaction, psel_delay, penable_delay)`: Complete a transaction

## Configuration

### Signal Lists

The module defines standard APB signal lists:

```python
apb_signals = [
    "PSEL",
    "PWRITE",
    "PENABLE",
    "PADDR",
    "PWDATA",
    "PRDATA",
    "PREADY"
]

apb_optional_signals = [
    "PPROT",
    "PSLVERR",
    "PSTRB"
]
```

### PWRITE Mapping

```python
pwrite = ['READ', 'WRITE']
```

## APB Protocol Timing

The APB protocol follows this timing sequence:

1. **Setup Phase**:
   - PSEL is asserted
   - PADDR, PWRITE, PWDATA (for writes) are set
   - PENABLE is low

2. **Access Phase**:
   - PENABLE is asserted
   - Wait for PREADY to be asserted by the slave
   - For reads, sample PRDATA when PREADY is high
   - Check PSLVERR if available

3. **End of Transaction**:
   - PSEL and PENABLE are de-asserted
   - All signals can change for the next transaction

The APB master and slave components implement this protocol timing, with configurable randomization of delays for more realistic testing.

## Example Usage

### Monitoring APB Transactions

```python
# Create APB monitor
apb_mon = APBMonitor(
    dut,            # Device under test
    "APB Monitor",  # Title
    "s_apb",        # Signal prefix
    dut.clk,        # Clock signal
    bus_width=32    # Data width
)

# Add a callback function
def transaction_callback(transaction):
    print(f"Captured: {transaction.formatted()}")

apb_mon.add_callback(transaction_callback)
```

### Creating an APB Master

```python
# Create timing randomizer
master_randomizer = FlexRandomizer({
    'psel':    ([[0, 0], [1, 3]], [8, 2]),
    'penable': ([[0, 0], [1, 2]], [6, 1])
})

# Create APB master
apb_master = APBMaster(
    dut,            # Device under test
    "APB Master",   # Title
    "s_apb",        # Signal prefix
    dut.clk,        # Clock signal
    randomizer=master_randomizer,
    bus_width=32    # Data width
)

# Send a transaction
packet = APBPacket(pwrite=1, paddr=0x1000, pwdata=0xABCD)
await apb_master.send(packet)
```

### Creating an APB Slave

```python
# Create an array of register values
registers = [0] * 1024  # 1KB of memory

# Create APB slave
apb_slave = APBSlave(
    dut,            # Device under test
    "APB Slave",    # Title
    "m_apb",        # Signal prefix
    dut.clk,        # Clock signal
    registers=registers,
    bus_width=32    # Data width
)

# Dump register contents after test
apb_slave.dump_registers()
```

## Implementation Notes

- The APB monitor triggers on the falling edge of the clock to capture stable signals
- The APB slave uses a memory model for register storage and manipulation
- The APB master maintains a queue of transactions to be sent
- Transactions are converted to/from APBPacket format
- Signal availability is checked to handle optional signals correctly

## See Also

- [APB Packet](apb_packet.md) - Protocol packet structure for APB transactions
- [APB Factories](apb_factories.md) - Factory functions for creating APB components
- [Memory Model](../memory_model.md) - Used by APB slave for register storage
- [Flex Randomizer](../flex_randomizer.md) - Randomization of delays

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
