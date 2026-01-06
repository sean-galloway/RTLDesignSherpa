<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# GAXI Components Index

This directory contains the GAXI (Generic AXI) protocol components for the CocoTBFramework. These components provide a simplified AXI-like interface for verification environments.

## Directory Structure

### Core Components
- [**gaxi_component_base.py**](components_gaxi_gaxi_component_base.md) - Unified base class for all GAXI components
- [**gaxi_master.py**](components_gaxi_gaxi_master.md) - GAXI Master with integrated structured pipeline
- [**gaxi_slave.py**](components_gaxi_gaxi_slave.md) - GAXI Slave with integrated structured pipeline
- [**gaxi_monitor.py**](components_gaxi_gaxi_monitor.md) - GAXI Monitor implementation
- [**gaxi_monitor_base.py**](components_gaxi_gaxi_monitor_base.md) - Base class for GAXI monitoring functionality

### Data and Protocol Support
- [**gaxi_packet.py**](components_gaxi_gaxi_packet.md) - GAXI Packet class with protocol-specific extensions
- [**gaxi_sequence.py**](components_gaxi_gaxi_sequence.md) - GAXI sequence generator for test patterns
- [**gaxi_command_handler.py**](components_gaxi_gaxi_command_handler.md) - Enhanced command handler for transactions

### Factory and Utilities
- [**gaxi_factories.py**](components_gaxi_gaxi_factories.md) - Factory functions for creating GAXI components

## Quick Start

### Basic Usage
```python
from CocoTBFramework.components.gaxi import create_gaxi_system

# Create complete GAXI system
system = create_gaxi_system(dut, clock)
master = system['master']
slave = system['slave']

# Send data
await master.send(master.create_packet(data=0xDEADBEEF))
```

### Advanced Usage
```python
from CocoTBFramework.components.gaxi import (
    GAXIMaster, GAXISlave, GAXIMonitor, GAXISequence
)

# Create individual components
master = GAXIMaster(dut, "TestMaster", "", clock, field_config)
slave = GAXISlave(dut, "TestSlave", "", clock, field_config)
monitor = GAXIMonitor(dut, "Monitor", "", clock, field_config)

# Create test sequence
sequence = GAXISequence("test_pattern", field_config)
sequence.add_burst(count=10, start_data=0x1000)
packets = sequence.generate_packets()
```

## Component Overview

### GAXIMaster
- Drives GAXI transactions with configurable timing
- Supports multi-signal and single-signal modes
- Integrated pipeline debugging and statistics
- Memory model integration for read/write operations

### GAXISlave  
- Receives GAXI transactions with configurable ready delays
- Supports different modes (skid, fifo_mux, fifo_flop)
- Automatic memory operations and response generation
- Pipeline debugging and error recovery

### GAXIMonitor
- Observes GAXI transactions on master or slave side
- Protocol violation detection
- Statistics collection and reporting
- Integration with scoreboards

### Supporting Classes
- **GAXIPacket**: Protocol-specific packet with field management
- **GAXISequence**: Test pattern generation with dependencies
- **GAXICommandHandler**: Transaction coordination and memory operations
- **GAXIComponentBase**: Common functionality for all components

## Features

### Signal Resolution
- Automatic signal discovery using pattern matching
- Manual signal mapping override capability
- Support for different signal naming conventions
- Multi-signal and single-signal field modes

### Performance Optimization
- Cached signal references for high-performance operation
- Thread-safe operation for parallel testing
- Optimized data collection and driving strategies
- Reduced signal lookup overhead

### Debugging Support
- Pipeline state tracking and transition logging
- Comprehensive statistics collection
- Protocol violation detection and reporting
- Memory operation tracking and validation

### Flexibility
- Configurable field definitions and packet structures
- Multiple randomization modes and constraints
- Dependency tracking in test sequences
- Memory model integration for transaction processing

## Integration

The GAXI components integrate seamlessly with:
- **Shared Components**: Field configuration, memory models, statistics
- **Scoreboards**: Automatic transaction recording and comparison
- **Randomization**: FlexRandomizer for timing and data generation
- **CocoTB**: Standard BusDriver/BusMonitor interfaces

## Navigation
- [**Overview**](components_gaxi_overview.md) - Detailed component overview and architecture
- [**Back to Components**](../components_index.md) - Return to components index
- [**Back to CocoTBFramework**](../components_index.md) - Return to main framework index