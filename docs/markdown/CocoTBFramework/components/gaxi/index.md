# GAXI Components

## Overview

The GAXI (Generic AXI) components provide a flexible and extensible framework for building and testing valid/ready handshaking interfaces in verification environments. These components implement a simplified AXI-style interface that focuses on the handshaking protocol while maintaining flexibility for different data structures and use cases.

## Key Features

- Generic valid/ready handshaking protocol implementation
- Flexible packet structure with field-based configuration
- Master and slave drivers with customizable timing behavior
- Memory model integration with enhanced error handling
- Command handler for transaction coordination
- Comprehensive test sequence generation with dependency tracking
- Multiple operating modes for different buffer implementations
- Factory functions for simplified component creation

## Components

- [GAXI Master](gaxi_master.md) - Master driver for initiating GAXI transactions
- [GAXI Slave](gaxi_slave.md) - Slave responder for GAXI transactions
- [GAXI Monitor](gaxi_monitor.md) - Non-intrusive monitoring of GAXI interfaces
- [GAXI Packet](gaxi_packet.md) - Representation of GAXI transactions
- [GAXI Sequence](gaxi_sequence.md) - Sequence generation for testing GAXI interfaces
- [GAXI Command Handler](gaxi_command_handler.md) - Coordination of master-slave communication
- [GAXI Factories](gaxi_factories.md) - Factory functions for creating GAXI components
- [GAXI Memory Integration](gaxi_memory_integ.md) - Enhanced memory model integration
- [GAXI Practical Examples](gaxi_practical_examples.md) - Comprehensive implementation examples

## Guides and Examples

- [Overview](overview.md) - Introduction to GAXI components
- [Practical Examples](gaxi_practical_examples.md) - End-to-end usage examples
- Using GAXI for Component Verification
- Building Custom GAXI Test Sequences
- Integrating GAXI with Other Protocols

## Related Components

- [Packet](../packet.md) - Base packet class for protocol transactions
- [Field Config](../field_config.md) - Field configuration for packet structure
- [Memory Model](../memory_model.md) - Base memory model functionality
- [Flex Randomizer](../flex_randomizer.md) - Randomization for GAXI timing

## Navigation

[↑ Components Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
