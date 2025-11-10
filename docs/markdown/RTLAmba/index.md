**[← Back to Main Index](../index.md)** | **[RTLAmba Overview](overview.md)**

# RTL AMBA Modules Index

This directory contains documentation for the AMBA (Advanced Microcontroller Bus Architecture) RTL library, providing comprehensive implementations of ARM AMBA bus protocols including APB, AXI4, AXI4-Lite, and AXI4-Stream.

## Overview

- **[Overview](overview.md)** - Complete overview of the RTL AMBA library architecture and protocol implementations

## AMBA Protocol Implementations

### APB (Advanced Peripheral Bus) - APB4/APB5

#### Core Components
- **[apb_master](apb/apb_master.md)** - APB master with command/response interfaces and FIFO buffering
- **[apb_master_cg](apb/apb_master_cg.md)** - Clock-gated APB master for power optimization
- **[apb_slave](apb/apb_slave.md)** - APB slave with configurable address decoding and response generation
- **[apb_slave_cg](apb/apb_slave_cg.md)** - Clock-gated APB slave for power optimization
- **[apb_monitor](apb/apb_monitor.md)** - APB protocol monitor for verification and debugging

#### Clock Domain Crossing
- **[apb_slave_cdc](apb/apb_slave_cdc.md)** - APB slave with clock domain crossing support
- **[apb_slave_cdc_cg](apb/apb_slave_cdc_cg.md)** - Clock-gated CDC APB slave

#### Test and Development
- **[apb_master_stub](apb/apb_master_stub.md)** - APB master stub for testing and simulation
- **[apb_slave_stub](apb/apb_slave_stub.md)** - APB slave stub for testing and simulation

### AXI4 (AXI4-Full) - Memory-Mapped Interface

#### Master Components
- **[axi4_master_rd](axi/axi4_master_rd.md)** - AXI4 read master with skid buffers and burst support
- **[axi4_master_rd_cg](axi/axi4_master_rd_cg.md)** - Clock-gated AXI4 read master
- **[axi4_master_wr](axi/axi4_master_wr.md)** - AXI4 write master with address/data coordination
- **[axi4_master_wr_cg](axi/axi4_master_wr_cg.md)** - Clock-gated AXI4 write master

#### Slave Components
- **[axi4_slave_rd](axi/axi4_slave_rd.md)** - AXI4 read slave with configurable response handling
- **[axi4_slave_rd_cg](axi/axi4_slave_rd_cg.md)** - Clock-gated AXI4 read slave
- **[axi4_slave_wr](axi/axi4_slave_wr.md)** - AXI4 write slave with write response generation
- **[axi4_slave_wr_cg](axi/axi4_slave_wr_cg.md)** - Clock-gated AXI4 write slave

#### Test Stubs
- **[axi4_master_stub](axi_stubs/axi4_master_stub.md)** - Complete AXI4 master stub
- **[axi4_master_rd_stub](axi_stubs/axi4_master_rd_stub.md)** - AXI4 read master stub
- **[axi4_master_wr_stub](axi_stubs/axi4_master_wr_stub.md)** - AXI4 write master stub
- **[axi4_slave_stub](axi_stubs/axi4_slave_stub.md)** - Complete AXI4 slave stub
- **[axi4_slave_rd_stub](axi_stubs/axi4_slave_rd_stub.md)** - AXI4 read slave stub
- **[axi4_slave_wr_stub](axi_stubs/axi4_slave_wr_stub.md)** - AXI4 write slave stub

### AXI4-Lite - Register Interface

#### Master Components
- **[axil4_master_rd](axil/axil4_master_rd.md)** - AXI4-Lite read master for register access
- **[axil4_master_rd_cg](axil/axil4_master_rd_cg.md)** - Clock-gated AXI4-Lite read master
- **[axil4_master_wr](axil/axil4_master_wr.md)** - AXI4-Lite write master for register access
- **[axil4_master_wr_cg](axil/axil4_master_wr_cg.md)** - Clock-gated AXI4-Lite write master

#### Slave Components
- **[axil4_slave_rd](axil/axil4_slave_rd.md)** - AXI4-Lite read slave with register interface
- **[axil4_slave_rd_cg](axil/axil4_slave_rd_cg.md)** - Clock-gated AXI4-Lite read slave
- **[axil4_slave_wr](axil/axil4_slave_wr.md)** - AXI4-Lite write slave with register interface
- **[axil4_slave_wr_cg](axil/axil4_slave_wr_cg.md)** - Clock-gated AXI4-Lite write slave

### AXI4-Stream - Streaming Interface

#### Stream Components
- **[axis_master](fabric/axis_master.md)** - AXI4-Stream master for data streaming
- **[axis_master_cg](fabric/axis_master_cg.md)** - Clock-gated AXI4-Stream master
- **[axis_slave](fabric/axis_slave.md)** - AXI4-Stream slave for data reception
- **[axis_slave_cg](fabric/axis_slave_cg.md)** - Clock-gated AXI4-Stream slave

### Shared Infrastructure and Utilities

#### Generic AXI (GAXI) Components
- **[gaxi_fifo_sync](fabric/gaxi_fifo_sync.md)** - Synchronous FIFO for GAXI interfaces
- **[gaxi_fifo_async](fabric/gaxi_fifo_async.md)** - Asynchronous FIFO for clock domain crossing
- **[gaxi_skid_buffer](fabric/gaxi_skid_buffer.md)** - Skid buffer for pipeline optimization
- **[gaxi_skid_buffer_async](fabric/gaxi_skid_buffer_async.md)** - Asynchronous skid buffer
- **[gaxi_skid_buffer_struct](fabric/gaxi_skid_buffer_struct.md)** - Structured skid buffer implementation

#### Arbitration and Control
- **[arbiter_monbus_common](utility/arbiter_monbus_common.md)** - Common arbitration logic for monitoring bus
- **[arbiter_rr_pwm_monbus](utility/arbiter_rr_pwm_monbus.md)** - Round-robin PWM arbiter for monbus
- **[arbiter_wrr_pwm_monbus](utility/arbiter_wrr_pwm_monbus.md)** - Weighted round-robin PWM arbiter
- **[monbus_arbiter](utility/monbus_arbiter.md)** - Monitoring bus arbiter

#### AXI Monitoring and Analysis
- **[axi_monitor_base](utility/axi_monitor_base.md)** - Base AXI protocol monitor
- **[axi_monitor_reporter](utility/axi_monitor_reporter.md)** - AXI transaction reporting
- **[axi_monitor_timeout](utility/axi_monitor_timeout.md)** - AXI timeout detection
- **[axi_monitor_timer](utility/axi_monitor_timer.md)** - AXI timing analysis
- **[axi_monitor_trans_mgr](utility/axi_monitor_trans_mgr.md)** - AXI transaction management

#### Address and Data Processing
- **[axi_gen_addr](utility/axi_gen_addr.md)** - AXI address generation utility
- **[axi_split_combi](utility/axi_split_combi.md)** - AXI combinational splitting logic
- **[axi_master_rd_splitter](utility/axi_master_rd_splitter.md)** - AXI read master splitter
- **[axi_master_wr_splitter](utility/axi_master_wr_splitter.md)** - AXI write master splitter

#### Clock and Reset Management
- **[amba_clock_gate_ctrl](utility/amba_clock_gate_ctrl.md)** - AMBA-specific clock gating controller
- **[cdc_handshake](utility/cdc_handshake.md)** - Clock domain crossing handshake

### Protocol Bridge and Shims

#### AXI4 to APB Conversion
- **[axi4_to_apb_convert](fabric/axi4_to_apb_convert.md)** - AXI4 to APB protocol converter
- **[axi4_to_apb_shim](fabric/axi4_to_apb_shim.md)** - Lightweight AXI4 to APB shim

### Package Definitions

#### Protocol Packages
- **[apb_pkg](includes/apb_pkg.md)** - APB protocol definitions and constants
- **[axi_pkg](includes/axi_pkg.md)** - AXI protocol definitions and constants
- **[monitor_pkg](includes/monitor_pkg.md)** - Monitoring infrastructure definitions
- **[monitor_network_pkg](includes/monitor_network_pkg.md)** - Network monitoring package definitions

## Quick Reference

### Module Count by Protocol
- **APB Components**: 7 modules (moved: apb_xbar, apb_xbar_thin to projects/components)
- **AXI4 Components**: 8 modules + 6 stubs
- **AXI4-Lite Components**: 8 modules
- **AXI4-Stream Components**: 4 modules
- **GAXI Infrastructure**: 5 modules
- **Shared Utilities**: 15 modules
- **Protocol Bridges**: 2 modules
- **Package Definitions**: 4 modules

**Note:** APB Crossbar has moved to production components. APB HPET is now part of the Retro Legacy Blocks collection. See [Component Projects](../projects/index.md) for complete documentation.

### Performance Characteristics

| Protocol | Typical Frequency | Throughput | Use Case |
|----------|------------------|------------|----------|
| APB | 100-200 MHz | 400 MB/s - 1.6 GB/s | Control registers, low-speed peripherals |
| AXI4-Lite | 200-400 MHz | 800 MB/s - 3.2 GB/s | Register access, configuration |
| AXI4-Full | 300-500 MHz | 9.6 GB/s - 32 GB/s | High-performance memory access |
| AXI4-Stream | 400-600 MHz | 12.8 GB/s - 76.8 GB/s | Data streaming, packet processing |

### Usage Guidelines

#### Protocol Selection
- **APB**: Simple register access, low area/power requirements
- **AXI4-Lite**: Standard register interface, moderate performance
- **AXI4-Full**: High-performance memory access, burst transactions
- **AXI4-Stream**: High-throughput data streaming, packet processing

#### Clock Gating Benefits
- **Power Reduction**: 20-40% dynamic power savings
- **Conditional Operation**: Clock gating when interfaces are idle
- **Fine-Grained Control**: Per-channel clock gating available

#### Design Integration
```systemverilog
// Example: Complete AXI4 system
axi4_master_rd #(.AXI_DATA_WIDTH(64)) u_rd_master (...);
axi4_master_wr #(.AXI_DATA_WIDTH(64)) u_wr_master (...);
axi4_slave_rd  #(.AXI_DATA_WIDTH(64)) u_rd_slave  (...);
axi4_slave_wr  #(.AXI_DATA_WIDTH(64)) u_wr_slave  (...);

// Protocol monitoring
axi_monitor_base #(.AXI_DATA_WIDTH(64)) u_monitor (...);
```

## Integration Patterns

### Multi-Protocol System
```systemverilog
// AXI4 to APB bridge for register access
axi4_to_apb_convert u_bridge (
    .axi_*    (cpu_axi_*),    // Connect to CPU AXI interface
    .apb_*    (periph_apb_*)  // Connect to peripheral APB bus
);

// APB crossbar for multiple peripherals
apb_xbar #(.NUM_SLAVES(4)) u_apb_xbar (
    .s_apb_*  (periph_apb_*),     // From bridge
    .m_apb_*  (slave_apb_*)       // To individual peripherals
);
```

### High-Performance Memory System
```systemverilog
// AXI4 read/write masters with monitoring
axi4_master_rd_cg u_rd_master (.cg_enable(rd_active), ...);
axi4_master_wr_cg u_wr_master (.cg_enable(wr_active), ...);
axi_monitor_base  u_monitor   (...);
```

### Streaming Data Path
```systemverilog
// AXI4-Stream processing chain
axis_master u_source (.m_axis_*(fifo_in));
gaxi_fifo_async u_cdc (.s_axis*(fifo_in), .m_axis*(fifo_out));
axis_slave u_sink (.s_axis_*(fifo_out));
```

## Verification and Debugging

### Monitoring Infrastructure
- Protocol compliance checking
- Transaction timing analysis
- Bandwidth utilization measurement
- Error detection and reporting

### Debug Features
- Transaction tracing
- Protocol state monitoring
- Performance counter integration
- Waveform annotation support

## Synthesis and Implementation

### Area Optimization
- Configurable buffer depths
- Optional clock gating
- Parameterizable data widths
- Shared resource options

### Timing Optimization
- Registered outputs
- Pipeline stages
- Skid buffer insertion
- Critical path balancing

### Power Optimization
- Clock gating controllers
- Power domain support
- Dynamic power scaling
- Low-power mode support

## Navigation
- **[Back to RTL Documentation](../index.md)** - Return to main RTL documentation index