# AXIS4 Components

The AXIS4 (AXI4-Stream) components provide comprehensive verification capabilities for AXI4-Stream protocol implementations. Built on the robust GAXI infrastructure, these components offer high-performance stream protocol testing with advanced packet management, flow control, and protocol compliance verification.

## Component Overview

The AXIS4 component ecosystem includes specialized classes for comprehensive stream protocol verification:

### Core Components

- **[AXISMaster](axis_master.md)** - Stream data generation and transmission
- **[AXISSlave](axis_slave.md)** - Stream data reception and validation
- **[AXISMonitor](axis_monitor.md)** - Protocol compliance monitoring and analysis
- **[AXISPacket](axis_packet.md)** - Data structure management and field access

### Configuration System

- **[AXISFieldConfigs](axis_field_configs.md)** - Protocol adaptation and signal mapping

## Key Features

### Stream Protocol Specialization
- Single channel (T-channel) focus with TVALID/TREADY handshaking
- Native packet boundary management with TLAST signaling
- Advanced flow control and backpressure handling
- Complete sideband signal support (TID, TDEST, TUSER, TSTRB, TKEEP)

### GAXI Infrastructure Integration
- Unified field configuration system
- Memory model integration for data verification
- Comprehensive statistics and performance metrics
- Advanced debugging and transaction logging
- Automatic signal resolution across naming conventions

### Advanced Capabilities
- Multi-stream support with TID-based routing
- Real-time performance monitoring and analysis
- Protocol compliance verification
- Configurable timing randomization
- Memory-efficient streaming for large datasets

## Getting Started

```python
from cocotb_framework.components.axis4 import AXISMaster, AXISSlave, AXISMonitor

# Create AXIS components
master = AXISMaster(dut, "StreamSource", "m_axis_", clk)
slave = AXISSlave(dut, "StreamSink", "s_axis_", clk)
monitor = AXISMonitor(dut, "StreamMon", "s_axis_", clk)

# Configure stream properties
master.configure_stream(data_width=32, id_width=8, dest_width=4)

# Generate and send packets
packet = master.create_packet(data=0x12345678, last=True, id=5, dest=2)
await master.send_packet(packet)
```

## Documentation Structure

- **[Overview](components_axis4_overview.md)** - Comprehensive component architecture and capabilities
- **Component References** - Detailed documentation for each AXIS4 class
- **[Usage Examples](axis_examples.md)** - Practical implementation patterns and scenarios
- **[Configuration Guide](axis_configuration.md)** - Field configuration and customization options

The AXIS4 components provide a complete solution for AXI4-Stream protocol verification, combining the power and flexibility of the GAXI infrastructure with stream-specific optimizations and advanced features for comprehensive testing scenarios.