# AXI4 Components

## Overview

The AXI4 (Advanced eXtensible Interface 4) components provide a comprehensive implementation for building and testing AXI4-compliant interfaces within a verification environment. These components include masters, slaves, monitors, scoreboards, sequences, and factory functions to simplify complex test development.

## Key Features

- Complete AXI4 protocol implementation following AMBA specifications
- Flexible packet structure with field-based configuration
- Master and slave drivers with customizable timing behavior
- Memory model integration for data storage and checking
- Multiple transaction types including bursts, exclusive access, atomic operations
- Protocol extensions for advanced SoC verification
- Comprehensive test sequence generation and execution
- Scoreboarding and protocol checking

## Components

- [AXI4 Master](axi4_master.md) - Master driver for initiating AXI4 transactions
- [AXI4 Slave](axi4_slave.md) - Slave responder for AXI4 transactions
- [AXI4 Monitor](axi4_monitor.md) - Transaction monitoring and protocol checking
- [AXI4 Memory Model](axi4_memory_model.md) - Memory models for AXI4 verification
- [AXI4 Sequences](axi4_sequences.md) - Test sequence generation for AXI4 interfaces
- [AXI4 Scoreboard](axi4_scoreboard.md) - Transaction verification and checking
- [AXI4 Protocol Extensions](axi4_protocol_extensions.md) - Advanced protocol features
- [AXI4 Field Config](axi4_field_config.md) - Field configuration for AXI4 packets
- [AXI4 Implementation](axi4_implementation.md) - Implementation details

## Guides and Examples

- [Overview](overview.md) - Introduction to AXI4 components
- [Implementation Guide](axi4_implementation.md) - Implementation details and customization
- [Protocol Extensions Guide](axi4_protocol_extensions.md) - How to use protocol extensions
- [Memory Model Guide](axi4_memory_model.md) - Using memory models effectively

## Related Components

- [Packet](../packet.md) - Base packet class for protocol transactions
- [Field Config](../field_config.md) - Field configuration for packet structure
- [Memory Model](../memory_model.md) - Base memory model functionality
- [Constrained Random](../constrained_random.md) - Randomization framework

## Navigation

[↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
