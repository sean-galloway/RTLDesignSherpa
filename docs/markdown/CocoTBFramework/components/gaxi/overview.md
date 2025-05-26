# GAXI Verification Environment Overview

## Introduction

The GAXI (Generic AXI) verification environment provides a modular and extensible framework for testing and validating interfaces that use the valid/ready handshaking protocol. This framework implements a simplified AXI-style interface, focusing on the core handshaking mechanism while allowing for flexible data structures and configurations.

## What is GAXI?

GAXI is a generic implementation of the valid/ready handshaking protocol commonly used in modern interface designs. Key features include:

- Master initiates transfers by asserting a valid signal
- Slave controls flow by asserting a ready signal
- Data transfers occur when both valid and ready are asserted
- Support for different buffer implementations (skid buffers, FIFOs)
- Configurable data fields to match specific interface requirements
- Optional backpressure through randomized ready delays

The GAXI protocol is particularly useful for:
- Data path components like buffers and FIFOs
- Pipeline stages with flow control
- Clock domain crossing interfaces
- Simple memory-mapped interfaces
- Data collection and aggregation modules

## Architecture of the Verification Environment

The GAXI verification environment consists of the following major components:

1. **GAXI Master**: Controls the valid signal and drives data onto the bus
2. **GAXI Slave**: Controls the ready signal and receives data from the bus
3. **GAXI Monitor**: Passively observes GAXI transactions
4. **GAXI Command Handler**: Coordinates transactions between master and slave
5. **GAXI Packet**: Represents data transferred through the interface
6. **GAXI Sequence**: Generates test patterns for structured testing
7. **GAXI Memory Integration**: Connects GAXI operations to memory models
8. **GAXI Factories**: Simplifies component creation and configuration

## Component Hierarchy

The environment follows a layered architecture:

```
GAXI Test Sequences
    |
    v
GAXI Command Handler
    |
    +-----------------+
    |                 |
    v                 v
GAXI Master        GAXI Slave
    |                 |
    v                 v
GAXI Monitor       GAXI Monitor
    |                 |
    v                 v
RTL Interface      RTL Interface
```

At the highest level, sequences generate test scenarios, the command handler coordinates master-slave communication, and monitors observe both sides of the interface for verification.

## Signal Structure

The GAXI interface consists of the following key signals:

### Standard Mode (Single Data Bus)
- `m2s_valid`: Master to slave valid signal
- `s2m_ready`: Slave to master ready signal
- `m2s_pkt`: Master to slave packet data signal

### Multi-Signal Mode (Separate Signals per Field)
- `m2s_valid`: Master to slave valid signal
- `s2m_ready`: Slave to master ready signal
- `m2s_pkt_<field_name>`: Individual field signals (e.g., m2s_pkt_addr, m2s_pkt_data)

## Operating Modes

The framework supports multiple operating modes to accommodate different buffer implementations:

1. **skid**: Standard mode for skid buffers where data is available in the same cycle as valid/ready
   ```
   Clock       : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
   m2s_valid   : __|‾‾‾‾‾‾‾‾‾‾‾‾|_________
   s2m_ready   : ‾‾‾‾‾‾‾‾|‾‾‾‾‾‾‾‾|_______
   m2s_pkt     : --X Valid X-------X-----X-
   Transfer    :         ^         ^
   ```

2. **fifo_mux**: FIFO multiplexer mode for combinational FIFO outputs
   ```
   Clock       : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
   m2s_valid   : __|‾‾‾‾‾‾‾‾‾‾‾‾|_________
   s2m_ready   : ‾‾‾‾‾‾‾‾|‾‾‾‾‾‾‾‾|_______
   m2s_pkt     : --X V1 X---X V2 X---------
   Transfer    :         ^         ^
   ```

3. **fifo_flop**: FIFO flip-flop mode for registered FIFO outputs
   ```
   Clock       : __|‾‾|__|‾‾|__|‾‾|__|‾‾|__
   m2s_valid   : __|‾‾‾‾‾‾‾‾‾‾‾‾|_________
   s2m_ready   : ‾‾‾‾‾‾‾‾|‾‾‾‾‾‾‾‾|_______
   m2s_pkt     : -----X Valid X-----X-----X
   Transfer    :         ^         ^
   ```

## Key Verification Capabilities

The GAXI verification environment provides comprehensive testing capabilities:

### Transaction Types
- Single data transfers
- Burst sequences
- Random data patterns
- Specialized test patterns
- Dependency-tracked transactions

### Protocol Features
- Field-level masking and validation
- Timing randomization for realistic scenarios
- Memory model integration
- Transaction dependency tracking
- Custom callbacks for advanced verification

### Performance Testing
- Backpressure simulation
- High-throughput testing
- Latency measurement
- Throughput monitoring
- Queue depth analysis

### Memory Testing
- Enhanced memory integration
- Error detection and reporting
- Automatic read/write operations
- Boundary checking
- Data consistency verification

## Documentation Structure

The remainder of the GAXI documentation is organized into the following sections:

1. **GAXI Master**: Controls the valid signal and drives data
2. **GAXI Slave**: Controls the ready signal and receives data
3. **GAXI Monitor**: Passively observes transactions
4. **GAXI Packet**: Represents transaction data
5. **GAXI Sequence**: Test pattern generation
6. **GAXI Command Handler**: Transaction coordination
7. **GAXI Memory Integration**: Memory model connections
8. **GAXI Factories**: Component creation helpers
9. **GAXI Practical Examples**: End-to-end examples

## Getting Started

To start using the GAXI verification environment:

1. Create components using factory functions:
```python
components = create_gaxi_components(
    dut, dut.clk,
    title_prefix="Test_",
    field_config=field_config,
    mode='skid'
)
```

2. Access individual components:
```python
master = components['master']
slave = components['slave']
master_monitor = components['master_monitor']
slave_monitor = components['slave_monitor']
scoreboard = components['scoreboard']
```

3. Create a command handler:
```python
command_handler = GAXICommandHandler(
    components['master'],
    components['slave'],
    components['memory_model']
)
```

4. Start the command handler and process transactions:
```python
await command_handler.start()

# Create and send a sequence
sequence = GAXISequence("test_sequence", field_config)
sequence.add_data_incrementing(count=10, data_start=0, data_step=1)
sequence.add_walking_ones(data_width=32)

response_map = await command_handler.process_sequence(sequence)

# Stop the command handler
await command_handler.stop()
```

## Navigation

[↑ GAXI Index](index.md) | [↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
