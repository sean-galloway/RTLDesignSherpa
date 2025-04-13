# GAXI Framework Overview

## Introduction

The GAXI (Generic AXI) framework is a modular and extensible verification environment designed for validating AXI-style interfaces and components that follow the valid/ready handshaking protocol. It provides a comprehensive suite of components for generating stimulus, observing responses, and verifying correctness of designs under test.

## Key Features

- **Flexible Component Architecture**: Master, slave, and monitor components that can be configured for different design requirements
- **Multi-Signal Support**: Works with both standard (single data bus) and multi-signal (individual signal per field) modes
- **Memory Integration**: Built-in memory model integration for automated data handling
- **Field Configuration**: Dynamic configuration of data fields with bit-width validation
- **Randomization**: Configurable timing randomization for realistic testing scenarios
- **Packet Generation**: Advanced packet generation with sequence capabilities
- **Enhanced Testing**: Support for various buffer types (FIFO, skid buffers) and test methodologies

## Core Components

The GAXI framework includes these primary components:

1. **GAXIMaster**: Controls the valid signal and drives data onto the bus
2. **GAXISlave**: Controls the ready signal and receives data from the bus
3. **GAXIMonitor**: Observes transactions without driving signals
4. **GAXIPacket**: Data structure for transactions with field masking
5. **GAXISequence**: Generates test sequences with dependency tracking
6. **FieldConfig**: Defines the structure and properties of data fields
7. **FlexRandomizer**: Provides configurable timing randomization
8. **GAXICommandHandler**: Coordinates transactions between components
9. **EnhancedMemoryIntegration**: Simplifies memory operations with improved error handling

## Framework Organization

The GAXI framework is organized into two main directories:

1. **components/gaxi**: Core component implementations
   - gaxi_master.py
   - gaxi_slave.py
   - gaxi_monitor.py
   - gaxi_packet.py
   - gaxi_sequence.py
   - gaxi_factories.py
   - gaxi_command_handler.py
   - gaxi_memory_integ.py

2. **tbclasses/gaxi**: Testbench implementations and examples
   - gaxi_buffer.py
   - gaxi_buffer_field.py
   - gaxi_buffer_multi.py
   - gaxi_buffer_seq.py
   - gaxi_buffer_configs.py
   - gaxi_data_collect_tb.py
   - gaxi_enhancements.py

This modular organization allows for easy reuse and extension of components for different verification needs.

## Common Use Cases

- Verification of valid/ready handshaking interfaces
- Testing of FIFOs, skid buffers, and other data path components
- Data collection and analysis from multiple sources
- Protocol conversion between different interface types
- Memory-mapped interface testing

## Getting Started

To use the GAXI framework, start by importing the necessary components:

```python
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.field_config import FieldConfig
```

Then create a field configuration that defines your data structure:

```python
field_config = FieldConfig()
field_config.add_field_dict('data', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 8,
    'active_bits': (31, 0),
    'description': 'Data value'
})
```

Next, instantiate the master, slave, and monitor components:

```python
master = GAXIMaster(dut, 'Master', '', clock, field_config=field_config)
slave = GAXISlave(dut, 'Slave', '', clock, field_config=field_config)
monitor = GAXIMonitor(dut, 'Monitor', '', clock, field_config=field_config)
```

Finally, create and send packets:

```python
packet = GAXIPacket(field_config)
packet.data = 0x12345678
await master.send(packet)
```

The following sections provide detailed documentation for each component of the GAXI framework.
