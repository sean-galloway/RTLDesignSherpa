**[← Back to Components Index](../components_index.md)** | **[CocoTBFramework Index](../../index.md)** | **[Main Index](../../../index.md)**

# AXI4 Components

The AXI4 (AXI4-Full) components provide comprehensive verification capabilities for AXI4 protocol implementations. Built on the robust GAXI infrastructure, these components offer advanced memory-mapped transaction generation, protocol compliance checking, and comprehensive verification features for full AXI4 implementations.

## Component Overview

The AXI4 component ecosystem includes specialized interfaces and utilities for comprehensive full AXI4 protocol verification:

### Core Interface Components

- **[AXI4MasterRead](axi4_master_read.md)** - Master read interface (AR/R channels)
- **[AXI4MasterWrite](axi4_master_write.md)** - Master write interface (AW/W/B channels)
- **[AXI4SlaveRead](axi4_slave_read.md)** - Slave read interface (AR/R channels)
- **[AXI4SlaveWrite](axi4_slave_write.md)** - Slave write interface (AW/W/B channels)

### Data Structure and Configuration

- **[AXI4Packet](axi4_packet.md)** - Transaction packet management
- **[AXI4FieldConfigs](axi4_field_configs.md)** - Protocol field configuration system
- **[AXI4Transaction](axi4_transaction.md)** - High-level transaction representation

### Advanced Features

- **[AXI4ComplianceChecker](axi4_compliance_checker.md)** - Protocol compliance verification
- **[AXI4Factories](axi4_factories.md)** - Component factory methods
- **[AXI4PacketUtils](axi4_packet_utils.md)** - Packet manipulation utilities
- **[AXI4RandomizationConfig](axi4_randomization_config.md)** - Randomization configuration
- **[AXI4TimingConfig](axi4_timing_config.md)** - Timing constraint configuration

## Key Features

### Full AXI4 Protocol Support
- Complete 5-channel implementation (AR, R, AW, W, B)
- Master and slave interface support
- Advanced features: Burst transactions, outstanding transactions, QoS
- Complete sideband signal support (ID, USER, CACHE, PROT, QOS, REGION)

### GAXI Infrastructure Integration
- Unified field configuration system
- Memory model integration for data verification
- Comprehensive statistics and performance metrics
- Advanced debugging and transaction logging
- Automatic signal resolution across naming conventions

### Advanced Verification Features
- Integrated protocol compliance checking
- Configurable timing randomization
- Outstanding transaction management
- Burst transaction support
- Error injection and recovery testing

## Getting Started

```python
from cocotb_framework.components.axi4 import AXI4MasterRead, AXI4MasterWrite

# Create AXI4 master read interface
master_read = AXI4MasterRead(
    dut=dut,
    clock=clk,
    prefix="m_axi_",
    data_width=32,
    id_width=8,
    addr_width=32,
    user_width=1
)

# Create AXI4 master write interface
master_write = AXI4MasterWrite(
    dut=dut,
    clock=clk,
    prefix="m_axi_",
    data_width=32,
    id_width=8,
    addr_width=32,
    user_width=1
)

# Perform read transaction
read_data = await master_read.read_transaction(
    address=0x1000,
    burst_len=4,
    id=1,
    burst_type=1  # INCR
)

# Perform write transaction
await master_write.write_transaction(
    address=0x2000,
    data=[0x12345678, 0x9ABCDEF0],
    id=2,
    burst_type=1  # INCR
)
```

## Protocol Architecture

AXI4 implements a full 5-channel protocol:

```
┌─────────────────────────────────────────────────────────────────┐
│                     AXI4 Protocol Channels                     │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ │
│  │  AR Channel │ │  R Channel  │ │ AW Channel  │ │  W Channel  │ │
│  │ (Addr Read) │ │ (Read Data) │ │(Addr Write) │ │(Write Data) │ │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘ │
│         │               │               │               │       │
│         └───────────────┼───────────────┼───────────────┘       │
│                         │               │                       │
│                  ┌─────────────┐ ┌─────────────┐               │
│                  │  B Channel  │ │   Master/   │               │
│                  │(Write Resp) │ │Slave Logic  │               │
│                  └─────────────┘ └─────────────┘               │
└─────────────────────────────────────────────────────────────────┘
```

## Documentation Structure

- **[Overview](components_axi4_overview.md)** - Comprehensive component architecture and capabilities
- **Interface References** - Detailed documentation for each AXI4 interface class
- **[Usage Examples](axi4_examples.md)** - Practical implementation patterns and scenarios
- **[Configuration Guide](axi4_configuration.md)** - Field configuration and customization options
- **[Compliance Guide](axi4_compliance.md)** - Protocol compliance checking and verification

## Advanced Use Cases

### Outstanding Transaction Management
```python
# Configure for multiple outstanding transactions
master_read.configure_outstanding(max_outstanding=8)

# Launch concurrent read transactions
tasks = []
for addr in [0x1000, 0x2000, 0x3000, 0x4000]:
    task = asyncio.create_task(master_read.read_transaction(addr, burst_len=4))
    tasks.append(task)

# Wait for all to complete
results = await asyncio.gather(*tasks)
```

### Protocol Compliance Verification
```python
# Enable compliance checking via environment variable
import os
os.environ['AXI4_COMPLIANCE_CHECK'] = '1'

# Compliance checker automatically integrated
master_read = AXI4MasterRead(dut, clk, "m_axi_")
# All transactions automatically monitored for compliance
```

### Memory Model Integration
```python
# Connect memory model for automatic verification
memory = create_memory_model(size=4096, data_width=32)
master_write.connect_memory(memory)
slave_read.connect_memory(memory)

# Data automatically verified between master writes and slave reads
```

The AXI4 components provide a complete solution for AXI4-Full protocol verification, combining the power and flexibility of the GAXI infrastructure with AXI4-specific optimizations and advanced features for comprehensive memory-mapped interface testing.