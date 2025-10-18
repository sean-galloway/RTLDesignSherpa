**[← Back to Components Index](../components_index.md)** | **[CocoTBFramework Index](../../index.md)** | **[Main Index](../../../index.md)**

# AXIL4 Components

The AXIL4 (AXI4-Lite) components provide comprehensive verification capabilities for AXI4-Lite protocol implementations. Built on the robust GAXI infrastructure, these components offer simplified memory-mapped transaction generation, protocol compliance checking, and comprehensive verification features optimized for lightweight AXI4-Lite implementations.

## Component Overview

The AXIL4 component ecosystem includes specialized interfaces for simplified AXI4-Lite protocol verification:

### Core Interface Components

- **[AXIL4MasterRead](axil4_master_read.md)** - Master read interface (AR/R channels)
- **[AXIL4MasterWrite](axil4_master_write.md)** - Master write interface (AW/W/B channels)
- **[AXIL4SlaveRead](axil4_slave_read.md)** - Slave read interface (AR/R channels)
- **[AXIL4SlaveWrite](axil4_slave_write.md)** - Slave write interface (AW/W/B channels)

### Data Structure and Configuration

- **[AXIL4Packet](axil4_packet.md)** - Transaction packet management
- **[AXIL4FieldConfigs](axil4_field_configs.md)** - Protocol field configuration system
- **[AXIL4PacketUtils](axil4_packet_utils.md)** - Packet manipulation utilities

### Advanced Features

- **[AXIL4ComplianceChecker](axil4_compliance_checker.md)** - Protocol compliance verification
- **[AXIL4Factories](axil4_factories.md)** - Component factory methods

## Key Features

### AXI4-Lite Protocol Support
- Simplified 5-channel implementation (AR, R, AW, W, B) without bursts
- Master and slave interface support
- Single outstanding transaction architecture
- Simplified signaling (no ID, USER, QOS, REGION signals)

### GAXI Infrastructure Integration
- Unified field configuration system
- Memory model integration for data verification
- Comprehensive statistics and performance metrics
- Advanced debugging and transaction logging
- Automatic signal resolution across naming conventions

### AXI4-Lite Specific Optimizations
- Single transaction focus (no burst support)
- Simplified address decode logic
- Register-oriented API methods
- Lightweight compliance checking

## Getting Started

```python
from cocotb_framework.components.axil4 import AXIL4MasterRead, AXIL4MasterWrite

# Create AXIL4 master interfaces
master_read = AXIL4MasterRead(
    dut=dut,
    clock=clk,
    prefix="m_axil_",
    data_width=32,
    addr_width=32
)

master_write = AXIL4MasterWrite(
    dut=dut,
    clock=clk,
    prefix="m_axil_",
    data_width=32,
    addr_width=32
)

# Perform register read
data = await master_read.read_register(address=0x1000)

# Perform register write
await master_write.write_register(address=0x1000, data=0x12345678)
```

## Protocol Architecture

AXI4-Lite implements a simplified 5-channel protocol without burst support:

```
┌─────────────────────────────────────────────────────────────────┐
│                   AXI4-Lite Protocol Channels                  │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ │
│  │  AR Channel │ │  R Channel  │ │ AW Channel  │ │  W Channel  │ │
│  │ (Addr Read) │ │ (Read Data) │ │(Addr Write) │ │(Write Data) │ │
│  │  No Bursts  │ │   Single    │ │  No Bursts  │ │   Single    │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘ │
│         │               │               │               │       │
│         └───────────────┼───────────────┼───────────────┘       │
│                         │               │                       │
│                  ┌─────────────┐ ┌─────────────┐               │
│                  │  B Channel  │ │Single Outst │               │
│                  │(Write Resp) │ │Transaction  │               │
│                  └─────────────┘ └─────────────┘               │
└─────────────────────────────────────────────────────────────────┘
```

## Key Differences from AXI4-Full

### Simplified Signaling
- **No Burst Support**: Fixed length of 1 transfer per transaction
- **No ID Signals**: Single outstanding transaction model
- **No User Signals**: Simplified sideband signaling
- **No QoS/Region**: Basic memory access only
- **Fixed Size**: Transfer size matches data width

### Register-Oriented Interface
```python
# AXI4-Lite is optimized for register access patterns
await master_write.write_register(0x100, 0x12345678)  # Control register
config_value = await master_read.read_register(0x104)  # Status register

# Byte-level register access with strobes
await master_write.write_register(0x108, 0xFF, strobe=0x1)  # Write byte 0 only
```

## Documentation Structure

- **[Overview](components_axil4_overview.md)** - Comprehensive component architecture and capabilities
- **Interface References** - Detailed documentation for each AXIL4 interface class
- **[Usage Examples](axil4_examples.md)** - Practical implementation patterns for register access
- **[Configuration Guide](axil4_configuration.md)** - Field configuration and customization options
- **[Compliance Guide](axil4_compliance.md)** - Protocol compliance checking and verification

## Common Use Cases

### Register Map Verification
```python
# Define register map
register_map = {
    0x000: "CONTROL",
    0x004: "STATUS",
    0x008: "DATA_IN",
    0x00C: "DATA_OUT",
    0x010: "INTERRUPT_ENABLE",
    0x014: "INTERRUPT_STATUS"
}

# Test register access
for addr, name in register_map.items():
    # Write test pattern
    test_value = 0xA5A5A5A5
    await master_write.write_register(addr, test_value)

    # Read back and verify
    read_value = await master_read.read_register(addr)
    assert read_value == test_value, f"Register {name} mismatch"
```

### Memory-Mapped Peripheral Testing
```python
# Configure AXIL4 slave for peripheral emulation
slave_read = AXIL4SlaveRead(dut, clk, "s_axil_")
slave_write = AXIL4SlaveWrite(dut, clk, "s_axil_")

# Connect to register model
register_model = create_register_model({
    0x00: RegisterDef("CTRL", 32, reset=0x00000000),
    0x04: RegisterDef("STAT", 32, reset=0x00000001, readonly=True),
    0x08: RegisterDef("DATA", 32, reset=0x00000000)
})

slave_read.connect_registers(register_model)
slave_write.connect_registers(register_model)
```

### Configuration Space Access
```python
# PCIe-style configuration space
config_space = AXIL4ConfigSpace(
    base_address=0x1000,
    size=4096,
    endianness='little'
)

# Standard configuration registers
await master_write.write_register(0x1004, 0x00000006)  # Command register
device_id = await master_read.read_register(0x1000)     # Device ID
```

## Performance Considerations

### Single Transaction Focus
- **Simplified State Machines**: No burst or outstanding transaction complexity
- **Lower Latency**: Reduced protocol overhead for single transfers
- **Register Access Optimized**: Optimized for control/status register patterns

### Memory Efficiency
- **Lightweight Structures**: Minimal memory overhead per transaction
- **Simple Queuing**: Single outstanding transaction simplifies queuing

The AXIL4 components provide a complete solution for AXI4-Lite protocol verification, offering simplified yet comprehensive functionality for memory-mapped register interface testing with the reliability and features of the GAXI infrastructure.