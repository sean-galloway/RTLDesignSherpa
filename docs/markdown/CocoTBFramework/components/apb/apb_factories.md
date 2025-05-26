# APB Factories

## Overview

The APB Factories module provides factory functions for creating and configuring APB (Advanced Peripheral Bus) components. These functions simplify the setup of APB verification environments by encapsulating the construction details and providing sensible defaults.

## Features

- Simplified creation of APB master, slave, monitor, and scoreboard components
- Standardized parameter handling with reasonable defaults
- Support for APB sequence generation with various test patterns
- Comprehensive component initialization and interconnection
- Consistent logging and configuration across components

## Factory Functions

### create_apb_master

Creates an APB Master component with configuration.

```python
def create_apb_master(dut, title, prefix, clock, addr_width=32, data_width=32,
                      randomizer=None, log=None)
```

- `dut`: Device under test
- `title`: Component title
- `prefix`: Signal prefix
- `clock`: Clock signal
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `randomizer`: Timing randomizer (optional)
- `log`: Logger instance (optional)

Returns:
- `APBMaster` instance

### create_apb_slave

Creates an APB Slave component with configuration.

```python
def create_apb_slave(dut, title, prefix, clock, addr_width=32, data_width=32,
                     registers=None, randomizer=None, log=None,
                     error_overflow=False)
```

- `dut`: Device under test
- `title`: Component title
- `prefix`: Signal prefix
- `clock`: Clock signal
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `registers`: Register values or number of registers (optional)
- `randomizer`: Timing randomizer (optional)
- `log`: Logger instance (optional)
- `error_overflow`: Whether to generate errors on address overflow

Returns:
- `APBSlave` instance

### create_apb_monitor

Creates an APB Monitor component with configuration.

```python
def create_apb_monitor(dut, title, prefix, clock, addr_width=32, data_width=32, log=None)
```

- `dut`: Device under test
- `title`: Component title
- `prefix`: Signal prefix
- `clock`: Clock signal
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `log`: Logger instance (optional)

Returns:
- `APBMonitor` instance

### create_apb_scoreboard

Creates an APB Scoreboard with configuration.

```python
def create_apb_scoreboard(name, addr_width=32, data_width=32, log=None)
```

- `name`: Scoreboard name
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `log`: Logger instance (optional)

Returns:
- `APBScoreboard` instance

### create_apb_command_handler

Creates an APB Command Handler for APB slave command/response interface.

```python
def create_apb_command_handler(dut, memory_model, log=None)
```

- `dut`: Device under test
- `memory_model`: Memory model for storage
- `log`: Logger instance (optional)

Returns:
- `APBCommandHandler` instance

### create_apb_components

Creates a complete set of APB components (master, slave, monitor, scoreboard).

```python
def create_apb_components(dut, clock, title_prefix="", addr_width=32, data_width=32,
                         memory_lines=1024, randomizer=None, log=None)
```

- `dut`: Device under test
- `clock`: Clock signal
- `title_prefix`: Prefix for component titles
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `memory_lines`: Number of memory lines for shared memory model
- `randomizer`: Timing randomizer for master (optional)
- `log`: Logger instance (optional)

Returns:
- Dictionary containing all created components

### create_apb_transformer

Creates a transformer from APB to GAXI protocol.

```python
def create_apb_transformer(gaxi_field_config, gaxi_packet_class, log=None)
```

- `gaxi_field_config`: GAXI field configuration
- `gaxi_packet_class`: GAXI packet class
- `log`: Logger instance (optional)

Returns:
- `APBtoGAXITransformer` instance

### create_apb_packet

Creates an APB packet with the given field values.

```python
def create_apb_packet(count=0, pwrite=0, paddr=0, pwdata=0, prdata=0, 
                     pstrb=0, pprot=0, pslverr=0, addr_width=32, data_width=32)
```

- `count`: Transaction count
- `pwrite`: Write enable (0=Read, 1=Write)
- `paddr`: Address
- `pwdata`: Write data (for writes)
- `prdata`: Read data (for reads)
- `pstrb`: Write strobes (for writes)
- `pprot`: Protection control
- `pslverr`: Slave error
- `addr_width`: Address width in bits
- `data_width`: Data width in bits

Returns:
- `APBPacket` instance

### create_apb_sequence

Creates an APB Sequence for testing.

```python
def create_apb_sequence(name="basic", num_regs=10, base_addr=0,
                       pattern="alternating", data_width=32,
                       randomize_delays=True)
```

- `name`: Sequence name
- `num_regs`: Number of registers to test
- `base_addr`: Base address
- `pattern`: Pattern type ("alternating", "burst", "strobe", "stress")
- `data_width`: Data width in bits
- `randomize_delays`: Whether to include random delays

Returns:
- `APBSequence` instance

## Sequence Patterns

The `create_apb_sequence` function supports several patterns:

### Alternating Pattern

Alternating write-read pairs for each register:

```
Write(reg0) → Read(reg0) → Write(reg1) → Read(reg1) → ...
```

### Burst Pattern

All writes followed by all reads:

```
Write(reg0) → Write(reg1) → ... → Read(reg0) → Read(reg1) → ...
```

### Strobe Pattern

Tests various strobe patterns with read-back verification:

```
Write(reg0, all_strobes) → Read(reg0) → Write(reg1, strobe_pattern1) → Read(reg1) → ...
```

### Stress Pattern

Random mix of reads and writes with various patterns:

```
Write → Write → Read → Write → Read → ...
```

## Example Usage

### Creating Basic Components

```python
# Create components individually
master = create_apb_master(dut, "APB Master", "s_apb", dut.clk)
slave = create_apb_slave(dut, "APB Slave", "m_apb", dut.clk, registers=256)
monitor = create_apb_monitor(dut, "APB Monitor", "s_apb", dut.clk)
scoreboard = create_apb_scoreboard("APB_Scoreboard")

# Connect monitor to scoreboard
monitor.add_callback(scoreboard.monitor_callback)
```

### Creating All Components at Once

```python
# Create a complete set of components
components = create_apb_components(
    dut,
    dut.clk,
    title_prefix="Test_",
    addr_width=32,
    data_width=32,
    memory_lines=1024
)

# Access individual components
master = components['master']
monitor = components['monitor']
scoreboard = components['scoreboard']
memory_model = components['memory_model']
```

### Creating and Using a Sequence

```python
# Create a test sequence
sequence = create_apb_sequence(
    name="register_test",
    num_regs=16,
    base_addr=0x1000,
    pattern="alternating",
    randomize_delays=True
)

# Send all transactions in the sequence
for _ in range(sequence.transaction_count):
    packet = sequence.next()
    await master.send(packet)
    await cocotb.triggers.Timer(sequence.next_delay(), units="ns")
```

### Creating and Sending APB Packets

```python
# Create a write packet
write_packet = create_apb_packet(
    pwrite=1,       # Write operation
    paddr=0x1000,   # Address
    pwdata=0xABCD,  # Write data
    pstrb=0xF       # All byte strobes enabled
)

# Send the packet
await master.send(write_packet)

# Create and send a read packet
read_packet = create_apb_packet(
    pwrite=0,       # Read operation
    paddr=0x1000    # Address
)

await master.send(read_packet)
```

## Implementation Details

### Default Randomizers

The factory functions create default randomizers when none are provided:

```python
# Default master randomizer
randomizer = FlexRandomizer({
    'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
    'penable': ([[0, 0], [1, 3]], [3, 1]),
})
```

### Register Handling

The `create_apb_slave` function handles the `registers` parameter in two ways:

1. If `registers` is None, an empty list is used
2. If `registers` is an integer, it's treated as the number of registers, initialized to zero

### Pattern Generation

Each sequence pattern in `create_apb_sequence` uses a dedicated generator function:

- Alternating: Creates write-read pairs for each register
- Burst: Creates all writes followed by all reads
- Strobe: Creates specialized strobe test patterns
- Stress: Creates a random mix of reads and writes

## Notes

- The factory functions automatically use the DUT's logger if none is provided
- The `create_apb_components` function creates a shared memory model for all components
- The command handler is only created if the DUT has the necessary signals
- All factory functions provide reasonable defaults for typical use cases

## See Also

- [APB Components](apb_components.md) - Core APB component implementations
- [APB Packet](apb_packet.md) - APB packet structure
- [APB Sequence](apb_sequence.md) - APB test sequence generation
- [Memory Model](../memory_model.md) - Used by APB slave for register storage

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
