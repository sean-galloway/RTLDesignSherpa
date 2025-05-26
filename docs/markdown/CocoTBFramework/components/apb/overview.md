# APB Overview

## Introduction

The Advanced Peripheral Bus (APB) is a simple, low-bandwidth protocol designed for accessing peripheral registers. The CocoTBFramework provides a comprehensive set of components for simulating and testing APB interfaces in hardware designs.

## APB Protocol

APB is part of the AMBA (Advanced Microcontroller Bus Architecture) family of bus protocols. It features:

- Simple address/data phases
- No bursts or split transactions
- Low power footprint
- Common peripheral interface

The protocol uses the following signals:
- PSEL: Peripheral select
- PWRITE: Direction (0=Read, 1=Write)
- PENABLE: Enable signal
- PADDR: Address bus
- PWDATA: Write data bus
- PRDATA: Read data bus
- PREADY: Peripheral ready
- Optional: PPROT, PSLVERR, PSTRB

## Framework Components

The CocoTBFramework provides these APB-specific components:

### APB Master
- Drives APB transactions to peripherals
- Supports configurable timing randomization
- Handles read and write operations

### APB Slave
- Responds to APB transactions
- Features built-in memory model for registers
- Supports configurable timing and error injection

### APB Monitor
- Monitors APB bus transactions
- Captures and formats transaction details
- Used for scoreboarding and verification

### APB Packet
- Represents APB transactions
- Extends the base Packet class
- Provides protocol-specific formatting

### APB Sequence
- Generates test patterns for APB interfaces
- Supports various patterns (alternating, burst, strobes)
- Configurable randomization

### Factory Functions
- Simplifies component creation and configuration
- Provides common test patterns and sequences
- Enhanced functions for register testing

## Using APB Components

The typical usage flow is:

1. Create components using factory functions
2. Configure master, slave, and monitor
3. Generate test sequences
4. Connect to scoreboard for verification
5. Run test and analyze results

## Example

```python
# Create APB components
apb_master = create_apb_master(dut, "APB Master", "s_apb", dut.clk)
apb_slave = create_apb_slave(dut, "APB Slave", "m_apb", dut.clk, registers=1024)
apb_monitor = create_apb_monitor(dut, "APB Monitor", "s_apb", dut.clk)

# Create a scoreboard
scoreboard = create_apb_scoreboard("APB_Scoreboard")
apb_monitor.add_callback(scoreboard.monitor_callback)

# Create and run a test sequence
sequence = create_apb_sequence(name="test_sequence", pattern="alternating")
for _ in range(10):
    packet = sequence.next()
    await apb_master.send(packet)
```

## Navigation

[↑ APB Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
