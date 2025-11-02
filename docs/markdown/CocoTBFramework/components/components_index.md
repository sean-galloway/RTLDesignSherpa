# Components Index

This directory contains the core verification components for the CocoTBFramework. These components provide protocol-specific implementations for masters, slaves, monitors, and supporting utilities across multiple bus protocols.

## Overview
- [**Overview**](overview.md) - Complete overview of the components directory and architecture

## Protocol Components

### Bus Protocols
- [**APB Components**](apb/components_apb_index.md) - Advanced Peripheral Bus protocol components with comprehensive transaction support
- [**AXI4 Components**](axi4/index.md) - Full AXI4 protocol components with burst transactions, outstanding operations, and compliance checking
- [**AXIL4 Components**](axil4/index.md) - AXI4-Lite protocol components optimized for register-oriented memory-mapped interfaces
- [**AXIS4 Components**](axis4/index.md) - AXI4-Stream protocol components for packet-based streaming data verification
- [**FIFO Components**](fifo/components_fifo_index.md) - First-In-First-Out protocol components for buffer and queue verification
- [**GAXI Components**](gaxi/components_gaxi_index.md) - Generic AXI-like protocol components with simplified interface

### Specialized Components
- [**Misc Components**](misc/components_misc_index.md) - Specialized monitoring and verification components for specific use cases

### Shared Infrastructure
- [**Shared Components**](shared/components_shared_index.md) - Core shared components used across all protocols including packet handling, randomization, statistics, and memory modeling

## Quick Start

### Basic Component Usage
```python
# Import protocol-specific components
from CocoTBFramework.components.apb import create_apb_master, create_apb_slave
from CocoTBFramework.components.gaxi import create_gaxi_master, create_gaxi_slave
from CocoTBFramework.components.fifo import create_fifo_master, create_fifo_slave

# Create components
apb_master = create_apb_master(dut, "APB_Master", "apb_", dut.clk)
gaxi_master = create_gaxi_master(dut, "GAXI_Master", "", dut.clk, field_config)
fifo_master = create_fifo_master(dut, "FIFO_Master", dut.clk)
```

### Shared Component Integration
```python
# Use shared components for configuration and utilities
from CocoTBFramework.components.shared import (
    FieldConfig, FieldDefinition, FlexRandomizer, MemoryModel
)

# Create field configuration
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))

# Create randomizer
randomizer = FlexRandomizer({
    'addr': ([(0x1000, 0x2000)], [1.0]),
    'data': ([(0, 0xFFFF)], [1.0])
})

# Create memory model
memory = MemoryModel(num_lines=256, bytes_per_line=4)
```

## Architecture Overview

### Component Hierarchy
```
┌─────────────────────────────────────────────────────────┐
│                 Protocol Components                    │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │     APB     │ │    AXI4     │ │   AXIL4     │     │
│   │ Components  │ │ Components  │ │ Components  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │   AXIS4     │ │    GAXI     │ │    FIFO     │     │
│   │ Components  │ │ Components  │ │ Components  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                 Specialized Components                 │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │    Misc     │ │   Future    │ │   Future    │     │
│   │ Components  │ │ Components  │ │ Components  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                  Shared Infrastructure                 │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│  │   Packet    │ │Randomization│ │ Statistics  │     │
│  │ Management  │ │  & Config   │ │& Monitoring │     │
│  └─────────────┘ └─────────────┘ └─────────────┘     │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│  │   Memory    │ │   Signal    │ │ Utilities & │     │
│  │   Model     │ │  Mapping    │ │   Debug     │     │
│  └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
```

## Key Features

### Protocol Coverage
- **APB**: Advanced Peripheral Bus with multi-slave support and register testing
- **AXI4**: Full AXI4 memory-mapped protocol with burst transactions and outstanding operations
- **AXIL4**: AXI4-Lite simplified protocol optimized for register access and configuration
- **AXIS4**: AXI4-Stream protocol for high-performance packet-based streaming data
- **GAXI**: Generic AXI-like interface with simplified handshaking
- **FIFO**: Buffer and queue protocols with flow control
- **Extensible**: Framework for adding new protocols

### Shared Infrastructure
- **Packet Management**: Protocol-agnostic packet handling with field configuration
- **Randomization**: Advanced constrained randomization with multiple modes
- **Statistics**: Comprehensive performance and error tracking
- **Memory Modeling**: High-performance memory simulation with access tracking
- **Signal Mapping**: Automatic signal discovery and manual override capabilities

### Component Types
- **Masters**: Transaction initiators with configurable timing and randomization
- **Slaves**: Transaction responders with memory backing and error injection
- **Monitors**: Passive observers for transaction logging and verification
- **Utilities**: Helper components for configuration, sequence generation, and debugging

## Integration Patterns

### Cross-Protocol Testing
```python
# Create components from different protocols
apb_master = create_apb_master(dut, "APB_Master", "apb_", dut.clk)
gaxi_slave = create_gaxi_slave(dut, "GAXI_Slave", "", dut.clk, field_config)

# Use shared memory model for cross-protocol verification
shared_memory = MemoryModel(num_lines=1024, bytes_per_line=4)
apb_master.set_memory_model(shared_memory)
gaxi_slave.set_memory_model(shared_memory)
```

### Factory Functions
All protocol components provide factory functions for easy creation:
- Sensible defaults for common use cases
- Automatic signal mapping and configuration
- Integration with shared components
- Consistent API across protocols

### Configuration Management
- Environment variable support for parameterization
- Field configuration system for packet structure definition
- Randomization profiles for different test scenarios
- Memory model integration for data tracking

## Performance Features

### Optimizations
- **Signal Caching**: Pre-resolved signal references for faster access
- **Thread-Safe Operations**: Parallel test execution support
- **Memory Efficiency**: NumPy-backed memory models for large data sets
- **Reduced Overhead**: Optimized data strategies and signal handling

### Scalability
- Support for large field configurations
- Efficient memory usage in long-running tests
- Parallel component operation
- Resource-conscious design

## Getting Started

1. **Choose Protocol**: Select appropriate protocol components (APB, GAXI, FIFO)
2. **Configure Fields**: Use FieldConfig for packet structure definition
3. **Create Components**: Use factory functions for quick setup
4. **Set Randomization**: Configure FlexRandomizer for test patterns
5. **Integrate Memory**: Add MemoryModel for data verification
6. **Run Tests**: Execute test sequences with monitoring and verification

Each component directory includes comprehensive documentation with examples, API references, and best practices for integration into verification environments.

## Navigation
- [**Back to CocoTBFramework**](../index.md) - Return to main framework index