# APB Components Usage Guide

This guide demonstrates how to use the APB components framework for hardware verification. It provides practical examples and common usage patterns.

## Basic Setup

### 1. Creating APB Components

The most common way to create APB components is using the factory functions from `apb_factories.py`:

```python
# Create APB master
apb_master = create_apb_master(
    dut,                   # Device under test
    "APB Master",          # Component title
    "s_apb",               # Signal prefix
    dut.pclk,              # Clock signal
    addr_width=32,         # Address width
    data_width=32,         # Data width
    randomizer=None,       # Optional randomizer
    log=log                # Logger
)

# Create APB slave
apb_slave = create_apb_slave(
    dut,                   # Device under test
    "APB Slave",           # Component title
    "s_apb",               # Signal prefix
    dut.pclk,              # Clock signal
    registers=[0] * 256,   # Initial register values
    addr_width=32,         # Address width
    data_width=32,         # Data width
    randomizer=None,       # Optional randomizer
    log=log                # Logger
)

# Create APB monitor
apb_monitor = create_apb_monitor(
    dut,                   # Device under test
    "APB Monitor",         # Component title
    "s_apb",               # Signal prefix
    dut.pclk,              # Clock signal
    addr_width=32,         # Address width
    data_width=32,         # Data width
    log=log                # Logger
)

# Create APB scoreboard
apb_scoreboard = create_apb_scoreboard(
    "APB Scoreboard",      # Scoreboard name
    addr_width=32,         # Address width
    data_width=32,         # Data width
    log=log                # Logger
)
```

### 2. Connecting Components

Connect monitors to scoreboards to verify transactions:

```python
# Add callback to monitor
apb_monitor.add_callback(apb_scoreboard.add_actual)
```

### 3. Creating a Memory Model

A memory model is used to store data for the APB components:

```python
# Create memory model
mem = MemoryModel(
    num_lines=1024,        # Number of lines in memory
    bytes_per_line=4,      # Bytes per line (data_width/8)
    log=log                # Logger
)
```

## Sending Transactions

### 1. Individual Transactions

To send a single APB transaction:

```python
# Create an APB packet
packet = APBPacket(
    count=0,               # Transaction count
    pwrite=1,              # Write (1) or Read (0)
    paddr=0x1000,          # Address
    pwdata=0x12345678,     # Write data (for writes)
    pstrb=0xF,             # Byte enable strobe
    pprot=0                # Protection attributes
)

# Send the transaction
await apb_master.send(packet)

# Wait for completion (optional)
await apb_master.wait_for_queue_empty()
```

### 2. Using Sequences

For more complex testing, use APB sequences:

```python
# Create a simple alternating read/write sequence
config = APBSequence(
    name="basic",
    pwrite_seq=[True, False, True, False],  # Write, Read, Write, Read
    addr_seq=[0x0, 0x0, 0x4, 0x4],          # Addresses
    data_seq=[0xABCD1234, 0x56789ABC],      # Write data
    strb_seq=[0xF, 0xF],                    # Byte enables
    inter_cycle_delays=[5, 5, 5]            # Delays between cycles
)

# Execute the sequence
for i in range(len(config.pwrite_seq)):
    # Get next transaction parameters
    is_write = config.next_pwrite()
    addr = config.next_addr()
    
    if is_write:
        # Get data and strobe for write
        data = config.next_data()
        strobe = config.next_strb()
        
        # Create and send write transaction
        write_packet = APBPacket(
            count=i,
            pwrite=1,
            paddr=addr,
            pwdata=data,
            pstrb=strobe,
            pprot=0
        )
        await apb_master.send(write_packet)
    else:
        # Create and send read transaction
        read_packet = APBPacket(
            count=i,
            pwrite=0,
            paddr=addr,
            pwdata=0,
            pstrb=0,
            pprot=0
        )
        await apb_master.send(read_packet)
    
    # Add delay between transactions
    delay = config.next_delay()
    if delay > 0:
        await cocotb.triggers.Timer(delay, units="ns")
```

### 3. Using Factory Sequence Patterns

The factory provides predefined sequence patterns:

```python
# Create a burst sequence (all writes followed by all reads)
config = create_apb_sequence(
    name="burst",
    num_regs=10,
    base_addr=0,
    pattern="burst",
    data_width=32,
    randomize_delays=True
)

# Create a stress test sequence
config = create_apb_sequence(
    name="stress",
    num_regs=64,
    base_addr=0,
    pattern="stress",
    data_width=32,
    randomize_delays=True
)
```

## Using Register Map

The RegisterMap class makes it easy to work with register definitions:

```python
# Create register map from a UVM file
reg_map = RegisterMap(
    filename="registers.py",
    apb_data_width=32,
    apb_addr_width=24,
    start_address=0x7F0000,
    log=log
)

# Write to a register field
reg_map.write("control", "enable", 1)
reg_map.write("status", "ready", 0)

# Generate APB cycles for all pending writes
apb_cycles = reg_map.generate_apb_cycles()

# Send the generated cycles
for cycle in apb_cycles:
    await apb_master.send(cycle)
```

## APB-GAXI Bridge Testing

When testing APB-GAXI bridges, use a more complex setup:

```python
# Create APB components
apb_monitor = create_apb_monitor(dut, "APB Monitor", "s_apb", dut.pclk)
apb_master = create_apb_master(dut, "APB Master", "s_apb", dut.pclk)

# Create GAXI components for command interface
cmd_monitor = create_gaxi_monitor(
    dut, "CMD Monitor", "", dut.pclk,
    field_config=cmd_field_config,
    is_slave=False,
    multi_sig=True,
    signal_map=cmd_signal_map,
    optional_signal_map=cmd_optional_signal_map
)

# Create APB-GAXI scoreboard
apb_gaxi_scoreboard = APBGAXIScoreboard("APB-GAXI Scoreboard", log=log)

# Connect monitors to scoreboard
apb_monitor.add_callback(apb_gaxi_scoreboard.add_apb_transaction)
cmd_monitor.add_callback(apb_gaxi_scoreboard.add_gaxi_transaction)

# Run tests and verify
await run_apb_test(config)
await verify_scoreboard()
```

## Reset and Initialization

Always reset components at the start of a test:

```python
# Reset DUT and components
async def reset_dut():
    # Reset DUT control signals
    dut.presetn.value = 0
    
    # Reset APB components
    await apb_master.reset_bus()
    await apb_slave.reset_bus()
    
    # Hold reset for multiple cycles
    await cocotb.triggers.Timer(50, units="ns")
    
    # Release reset
    dut.presetn.value = 1
    
    # Wait for stabilization
    await cocotb.triggers.Timer(100, units="ns")
```

## Command Handler

For more complex designs with a command/response interface:

```python
# Create command handler
cmd_handler = APBCommandHandler(dut, memory_model, log)

# Start the command handler
await cmd_handler.start()

# Run tests...

# Stop the command handler
await cmd_handler.stop()
```

## Verification

After running tests, verify the results:

```python
# Verify scoreboard for unmatched transactions
result = await apb_gaxi_scoreboard.check_scoreboard()

if result:
    log.info("Scoreboard verification passed - all transactions matched")
else:
    log.error("Scoreboard verification failed - unmatched transactions found")

# Get and log the report
report = apb_gaxi_scoreboard.report()
log.info(f"Scoreboard report:\n{report}")
```

## Complete Test Example

A complete test might look like:

```python
@cocotb.test()
async def apb_test(dut):
    # Create components
    apb_master = create_apb_master(dut, "APB Master", "s_apb", dut.pclk)
    apb_monitor = create_apb_monitor(dut, "APB Monitor", "s_apb", dut.pclk)
    apb_scoreboard = create_apb_scoreboard("APB Scoreboard")
    
    # Connect monitor to scoreboard
    apb_monitor.add_callback(apb_scoreboard.add_actual)
    
    # Reset DUT
    await reset_dut()
    
    # Create and run test sequence
    config = create_apb_sequence(name="basic", num_regs=10, pattern="alternating")
    await run_apb_test(config)
    
    # Verify results
    result = await apb_scoreboard.check()
    assert result, "Test failed - unmatched transactions found"
```

## Best Practices

1. Always reset components at the start of tests
2. Use factory functions for consistent setup
3. Connect monitors to scoreboards for verification
4. Use sequences for complex test patterns
5. Wait for transactions to complete before checking results
6. Use proper error handling and verification
7. Clean up resources (stop handlers, etc.) in finally blocks
