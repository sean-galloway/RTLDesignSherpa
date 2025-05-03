# APB Components Overview

This document provides an overview of the Advanced Peripheral Bus (APB) components framework, which is part of the CocoTBFramework for hardware verification.

## Introduction

The APB (Advanced Peripheral Bus) is part of the AMBA (Advanced Microcontroller Bus Architecture) family of bus protocols developed by ARM. It's designed for low bandwidth control accesses, for example register interfaces on system peripherals. This APB framework provides a complete verification environment for APB interfaces in hardware designs.

## Core Components

The framework consists of the following key components:

### 1. APB Packet (`apb_packet.py`)

The `APBPacket` class is the fundamental data structure that represents individual APB transactions. It contains:
- Transaction direction (read/write)
- Address
- Data (read or write)
- Strobes for byte-enable during writes
- Protection attributes
- Error signaling
- Timing information

Additionally, the `APBTransaction` class adds randomization capabilities for generating test transactions.

### 2. APB Components (`apb_components.py`)

This file contains the core functional classes:

- **APBMonitor**: Observes APB bus activity and captures transactions
- **APBSlave**: Responds to APB transactions, includes a memory model
- **APBMaster**: Drives APB transactions onto the bus

These components handle the detailed protocol implementation, timing, and signal management required for APB verification.

### 3. APB Factories (`apb_factories.py`)

Factory functions that simplify the creation and configuration of APB components:
- Functions to create monitors, masters, slaves, scoreboards
- Utilities for creating test sequences with different patterns
- Convenience methods for common verification tasks

### 4. APB Sequence (`apb_sequence.py`)

The `APBSequence` class facilitates the creation of transaction sequences for testing:
- Supports different test patterns (alternating read/write, burst, strobe tests)
- Manages transaction timing, delays, and randomization
- Provides iteration and sequence management

### 5. Register Map (`register_map.py`)

The `RegisterMap` class handles register information from UVM files:
- Extracts register definitions
- Manages register state
- Provides register access methods
- Generates APB cycles for register access
- Compares expected vs. actual register values

### 6. Command Handler (`apb_command_handler.py`)

The `APBCommandHandler` processes commands on the command/response interface:
- Monitors the command interface
- Processes read/write commands using a memory model
- Drives the response interface with results

## Interrelationships

These components work together to create a complete verification environment:

1. **Test setup**: Factory functions create and configure the necessary components
2. **Test generation**: Sequences or transactions are generated
3. **Bus driving**: Masters drive transactions onto the bus
4. **Monitoring**: Monitors capture the activity
5. **Response**: Slaves respond to transactions
6. **Verification**: Scoreboards compare expected vs. actual results

## Integration with Other Components

The APB framework integrates with:
- **Memory Models**: For storing and retrieving data during simulation
- **Randomizers**: For constrained-random testing
- **Scoreboards**: For verification and checking
- **GAXI components**: For bridging between APB and other protocols
- **Command Handlers**: For more complex command-response interfaces

## Next Steps

For details on how to use these components, see the [APB Usage Guide](apb-usage). For deep dives into the implementation details, see the individual component deep dive documents.
