# CocoTBFramework Components

This directory contains the core components of the CocoTBFramework verification environment. These components provide the building blocks for creating verification environments for digital designs using the [Cocotb](https://www.cocotb.org/) Python-based verification framework.

## Core Components

| Component | Description |
| --------- | ----------- |
| [ArbiterMonitor](arbiter_monitor.md) | Generic arbiter monitor for round-robin and weighted arbiters |
| [ConstrainedRandom](constrained_random.md) | Generates random values based on constraints and weights |
| [DebugObject](debug_object.md) | Utilities for debugging and inspecting objects |
| [FieldConfig](field_config.md) | Classes for defining field configurations for packets |
| [FlexRandomizer](flex_randomizer.md) | Flexible constrained randomization with sequence and function support |
| [MemoryModel](memory_model.md) | Generic memory model for verification environments |
| [Packet](packet.md) | Generic packet class for protocol testing with caching optimizations |
| [RandomizationConfig](randomization_config.md) | Configuration framework for controlling randomization behavior |

## Protocol-Specific Components

The framework also includes protocol-specific components in subdirectories:

- [**APB**](apb/index.md): Components for Advanced Peripheral Bus (APB) protocol testing
- [**AXI4**](axi4/index.md): Components for Advanced eXtensible Interface 4 (AXI4) protocol testing
- [**FIFO**](fifo/index.md): Components for FIFO interface testing
- [**GAXI**](gaxi/index.md): Components for Generic AXI interface testing

## Utility Components

- **WaveDrom Utils**: Utilities for generating WaveDrom timing diagrams

## Navigation

[↑ CocoTBFramework Index](../index.md)
