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

**[Back to Main Index](../index.md)** | **[RTLAmba Overview](overview.md)**

# RTL AMBA Modules Index

This directory contains documentation for the AMBA (Advanced Microcontroller Bus Architecture) RTL library, providing comprehensive implementations of ARM AMBA bus protocols. The library supports both **AMBA 4** and **AMBA 5** specifications across APB, AXI, AXI-Lite, and AXI-Stream protocols.

## Overview

- **[Overview](overview.md)** - Complete overview of the RTL AMBA library architecture and protocol implementations

---

## AMBA 4 Protocol Implementations

AMBA 4 modules provide the foundation for high-performance SoC interconnect, widely deployed in production systems. These modules are mature, fully verified, and optimized for synthesis.

### APB4 (Advanced Peripheral Bus)

Simple, low-power peripheral bus for control registers and low-bandwidth devices.

**[APB4 Module Documentation](apb/README.md)**

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

---

### AXI4-Full (Memory-Mapped Interface)

High-performance memory-mapped interface supporting burst transactions and multiple outstanding operations.

**[AXI4 Module Documentation](axi4/README.md)**

#### Master Components
- **[axi4_master_rd](axi4/axi4_master_rd.md)** - AXI4 read master with skid buffers and burst support
- **[axi4_master_rd_cg](axi4/axi4_master_rd_cg.md)** - Clock-gated AXI4 read master
- **[axi4_master_wr](axi4/axi4_master_wr.md)** - AXI4 write master with address/data coordination
- **[axi4_master_wr_cg](axi4/axi4_master_wr_cg.md)** - Clock-gated AXI4 write master

#### Slave Components
- **[axi4_slave_rd](axi4/axi4_slave_rd.md)** - AXI4 read slave with configurable response handling
- **[axi4_slave_rd_cg](axi4/axi4_slave_rd_cg.md)** - Clock-gated AXI4 read slave
- **[axi4_slave_wr](axi4/axi4_slave_wr.md)** - AXI4 write slave with write response generation
- **[axi4_slave_wr_cg](axi4/axi4_slave_wr_cg.md)** - Clock-gated AXI4 write slave

#### Test Stubs
- **[axi4_master_stub](axi4/axi4_master_stub.md)** - Complete AXI4 master stub
- **[axi4_master_rd_stub](axi4/axi4_master_rd_stub.md)** - AXI4 read master stub
- **[axi4_master_wr_stub](axi4/axi4_master_wr_stub.md)** - AXI4 write master stub
- **[axi4_slave_stub](axi4/axi4_slave_stub.md)** - Complete AXI4 slave stub
- **[axi4_slave_rd_stub](axi4/axi4_slave_rd_stub.md)** - AXI4 read slave stub
- **[axi4_slave_wr_stub](axi4/axi4_slave_wr_stub.md)** - AXI4 write slave stub

---

### AXI4-Lite (Register Interface)

Simplified AXI4 for register access with single outstanding transaction support.

**[AXI4-Lite Module Documentation](axil4/README.md)**

#### Master Components
- **[axil4_master_rd](axil4/axil4_master_rd.md)** - AXI4-Lite read master for register access
- **[axil4_master_rd_cg](axil4/axil4_master_rd_cg.md)** - Clock-gated AXI4-Lite read master
- **[axil4_master_wr](axil4/axil4_master_wr.md)** - AXI4-Lite write master for register access
- **[axil4_master_wr_cg](axil4/axil4_master_wr_cg.md)** - Clock-gated AXI4-Lite write master

#### Slave Components
- **[axil4_slave_rd](axil4/axil4_slave_rd.md)** - AXI4-Lite read slave with register interface
- **[axil4_slave_rd_cg](axil4/axil4_slave_rd_cg.md)** - Clock-gated AXI4-Lite read slave
- **[axil4_slave_wr](axil4/axil4_slave_wr.md)** - AXI4-Lite write slave with register interface
- **[axil4_slave_wr_cg](axil4/axil4_slave_wr_cg.md)** - Clock-gated AXI4-Lite write slave

---

### AXI4-Stream (Streaming Interface)

High-throughput unidirectional streaming for data processing pipelines.

**[AXI4-Stream Module Documentation](axis4/README.md)**

#### Stream Components
- **[axis_master](axis4/axis_master.md)** - AXI4-Stream master for data streaming
- **[axis_master_cg](axis4/axis_master_cg.md)** - Clock-gated AXI4-Stream master
- **[axis_slave](axis4/axis_slave.md)** - AXI4-Stream slave for data reception
- **[axis_slave_cg](axis4/axis_slave_cg.md)** - Clock-gated AXI4-Stream slave

---

## AMBA 5 Protocol Implementations

AMBA 5 modules provide enhanced features for next-generation SoC designs, including atomic operations, extended QoS, memory tagging, and improved power management signaling.

### APB5 (Advanced Peripheral Bus - AMBA 5)

Enhanced APB with wake-up signaling, non-secure extension, and user signals.

**[APB5 Module Documentation](apb5/README.md)**

| Feature | APB4 | APB5 |
|---------|------|------|
| Protection | PPROT[2:0] | PPROT[2:0] + PNSE |
| Wake-up | Not supported | PWAKEUP signal |
| User Signals | Not supported | PAUSER, PWUSER, PRUSER, PBUSER |

#### Core Components
- **[apb5_master](apb5/apb5_master.md)** - APB5 master with command/response interface
- **[apb5_slave](apb5/apb5_slave.md)** - APB5 slave with buffered cmd/rsp interface
- **[apb5_slave_cdc](apb5/apb5_slave_cdc.md)** - APB5 slave with clock domain crossing
- **[apb5_monitor](apb5/apb5_monitor.md)** - APB5 transaction monitor

#### Clock-Gated Variants
- **[apb5_master_cg](apb5/apb5_master_cg.md)** - Clock-gated APB5 master
- **[apb5_slave_cg](apb5/apb5_slave_cg.md)** - Clock-gated APB5 slave
- **[apb5_slave_cdc_cg](apb5/apb5_slave_cdc_cg.md)** - Clock-gated CDC APB5 slave

#### Test Stubs
- **[apb5_master_stub](apb5/apb5_master_stub.md)** - APB5 master stub for testing
- **[apb5_slave_stub](apb5/apb5_slave_stub.md)** - APB5 slave stub for testing

---

### AXI5 (High-Performance Memory-Mapped - AMBA 5)

Enhanced AXI with atomic operations, memory tagging, and extended QoS.

**[AXI5 Module Documentation](axi5/README.md)**

| Feature | AXI4 | AXI5 |
|---------|------|------|
| Outstanding | Up to 16 | Up to 256 |
| Atomic Ops | Not supported | AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare |
| Memory Tagging | Not supported | AWMEMATTR, ARMEMATTR |
| Data Poisoning | Not supported | RPOISON, WPOISON |

#### Master Components
- **[axi5_master_rd](axi5/axi5_master_rd.md)** - AXI5 read master with skid buffers
- **[axi5_master_rd_cg](axi5/axi5_master_rd_cg.md)** - Clock-gated AXI5 read master
- **[axi5_master_wr](axi5/axi5_master_wr.md)** - AXI5 write master with address/data coordination
- **[axi5_master_wr_cg](axi5/axi5_master_wr_cg.md)** - Clock-gated AXI5 write master

#### Slave Components
- **[axi5_slave_rd](axi5/axi5_slave_rd.md)** - AXI5 read slave with configurable response
- **[axi5_slave_rd_cg](axi5/axi5_slave_rd_cg.md)** - Clock-gated AXI5 read slave
- **[axi5_slave_wr](axi5/axi5_slave_wr.md)** - AXI5 write slave with response generation
- **[axi5_slave_wr_cg](axi5/axi5_slave_wr_cg.md)** - Clock-gated AXI5 write slave

#### Integrated Monitor Modules
- **[axi5_master_rd_mon](axi5/axi5_master_rd_mon.md)** - Read master with integrated monitor
- **[axi5_master_rd_mon_cg](axi5/axi5_master_rd_mon_cg.md)** - Clock-gated read master with monitor
- **[axi5_master_wr_mon](axi5/axi5_master_wr_mon.md)** - Write master with integrated monitor
- **[axi5_master_wr_mon_cg](axi5/axi5_master_wr_mon_cg.md)** - Clock-gated write master with monitor
- **[axi5_slave_rd_mon](axi5/axi5_slave_rd_mon.md)** - Read slave with integrated monitor
- **[axi5_slave_rd_mon_cg](axi5/axi5_slave_rd_mon_cg.md)** - Clock-gated read slave with monitor
- **[axi5_slave_wr_mon](axi5/axi5_slave_wr_mon.md)** - Write slave with integrated monitor
- **[axi5_slave_wr_mon_cg](axi5/axi5_slave_wr_mon_cg.md)** - Clock-gated write slave with monitor

---

### AXI5-Stream (Streaming Interface - AMBA 5)

Enhanced streaming with wake-up signaling and data poisoning support.

**[AXI5-Stream Module Documentation](axis5/README.md)**

| Feature | AXI4-Stream | AXI5-Stream |
|---------|-------------|-------------|
| Wake-up | Not supported | TWAKEUP signal |
| Data Poisoning | Not supported | TPOISON |

#### Stream Components
- **[axis5_master](axis5/axis5_master.md)** - AXI5-Stream master for data streaming
- **[axis5_master_cg](axis5/axis5_master_cg.md)** - Clock-gated AXI5-Stream master
- **[axis5_slave](axis5/axis5_slave.md)** - AXI5-Stream slave for data reception
- **[axis5_slave_cg](axis5/axis5_slave_cg.md)** - Clock-gated AXI5-Stream slave

---

## Shared Infrastructure and Utilities

Infrastructure components used across all AMBA protocols.

### Generic AXI (GAXI) Components

**[GAXI Module Documentation](gaxi/README.md)**

- **[gaxi_fifo_sync](gaxi/gaxi_fifo_sync.md)** - Synchronous FIFO for GAXI interfaces
- **[gaxi_fifo_async](gaxi/gaxi_fifo_async.md)** - Asynchronous FIFO for clock domain crossing
- **[gaxi_skid_buffer](gaxi/gaxi_skid_buffer.md)** - Skid buffer for pipeline optimization
- **[gaxi_skid_buffer_async](gaxi/gaxi_skid_buffer_async.md)** - Asynchronous skid buffer
- **[gaxi_skid_buffer_struct](gaxi/gaxi_skid_buffer_struct.md)** - Structured skid buffer implementation

### Arbitration and Control

- **[arbiter_monbus_common](shared/arbiter_monbus_common.md)** - Common arbitration logic for monitoring bus
- **[arbiter_rr_pwm_monbus](shared/arbiter_rr_pwm_monbus.md)** - Round-robin PWM arbiter for monbus
- **[arbiter_wrr_pwm_monbus](shared/arbiter_wrr_pwm_monbus.md)** - Weighted round-robin PWM arbiter
- **[monbus_arbiter](shared/monbus_arbiter.md)** - Monitoring bus arbiter

### AXI Monitoring and Analysis

- **[axi_monitor_base](shared/axi_monitor_base.md)** - Base AXI protocol monitor
- **[axi_monitor_reporter](shared/axi_monitor_reporter.md)** - AXI transaction reporting
- **[axi_monitor_timeout](shared/axi_monitor_timeout.md)** - AXI timeout detection
- **[axi_monitor_timer](shared/axi_monitor_timer.md)** - AXI timing analysis
- **[axi_monitor_trans_mgr](shared/axi_monitor_trans_mgr.md)** - AXI transaction management

### Address and Data Processing

- **[axi_gen_addr](shared/axi_gen_addr.md)** - AXI address generation utility
- **[axi_split_combi](shared/axi_split_combi.md)** - AXI combinational splitting logic
- **[axi_master_rd_splitter](shared/axi_master_rd_splitter.md)** - AXI read master splitter
- **[axi_master_wr_splitter](shared/axi_master_wr_splitter.md)** - AXI write master splitter

### Clock and Reset Management

- **[amba_clock_gate_ctrl](shared/amba_clock_gate_ctrl.md)** - AMBA-specific clock gating controller
- **[cdc_handshake](shared/cdc_handshake.md)** - Clock domain crossing handshake

---

## Protocol Bridge and Shims

### AXI4 to APB Conversion
- **[axi4_to_apb_convert](shims/axi4_to_apb_convert.md)** - AXI4 to APB protocol converter
- **[axi4_to_apb_shim](shims/axi4_to_apb_shim.md)** - Lightweight AXI4 to APB shim

---

## Package Definitions

### Protocol Packages
- **[apb_pkg](includes/apb_pkg.md)** - APB protocol definitions and constants
- **[axi_pkg](includes/axi_pkg.md)** - AXI protocol definitions and constants
- **[monitor_pkg](includes/monitor_pkg.md)** - Monitoring infrastructure definitions
- **[monitor_network_pkg](includes/monitor_network_pkg.md)** - Network monitoring package definitions

---

## Quick Reference

### Module Count by Protocol

| Protocol | AMBA 4 | AMBA 5 | Total |
|----------|--------|--------|-------|
| APB | 9 modules | 9 modules | 18 |
| AXI (Full) | 14 modules | 16 modules | 30 |
| AXI-Lite | 8 modules | - | 8 |
| AXI-Stream | 4 modules | 4 modules | 8 |
| GAXI Infrastructure | 5 modules | - | 5 |
| Shared Utilities | 15 modules | - | 15 |
| Protocol Bridges | 2 modules | - | 2 |

**Total: 86 AMBA modules**

### Performance Characteristics

| Protocol | Typical Frequency | Throughput | Use Case |
|----------|------------------|------------|----------|
| APB4/APB5 | 100-200 MHz | 400 MB/s - 1.6 GB/s | Control registers, low-speed peripherals |
| AXI4-Lite | 200-400 MHz | 800 MB/s - 3.2 GB/s | Register access, configuration |
| AXI4/AXI5 | 300-500 MHz | 9.6 GB/s - 32 GB/s | High-performance memory access |
| AXI4/5-Stream | 400-600 MHz | 12.8 GB/s - 76.8 GB/s | Data streaming, packet processing |

### AMBA 4 vs AMBA 5 Selection Guide

| Requirement | Recommendation |
|-------------|----------------|
| Proven, mature design | AMBA 4 |
| Atomic operations needed | AMBA 5 (AXI5) |
| Memory tagging (MTE) | AMBA 5 (AXI5) |
| Power management wake-up | AMBA 5 (APB5, AXI5-Stream) |
| TrustZone integration | AMBA 5 (APB5 PNSE) |
| Maximum compatibility | AMBA 4 |
| Next-generation features | AMBA 5 |

---

## Usage Guidelines

### Protocol Selection
- **APB4/APB5**: Simple register access, low area/power requirements
- **AXI4-Lite**: Standard register interface, moderate performance
- **AXI4/AXI5**: High-performance memory access, burst transactions
- **AXI4/5-Stream**: High-throughput data streaming, packet processing

### Clock Gating Benefits
- **Power Reduction**: 20-40% dynamic power savings
- **Conditional Operation**: Clock gating when interfaces are idle
- **Fine-Grained Control**: Per-channel clock gating available

### Design Integration

```systemverilog
// Example: Complete AXI5 system with monitoring
axi5_master_rd_mon #(.AXI_DATA_WIDTH(64)) u_rd_master (...);
axi5_master_wr_mon #(.AXI_DATA_WIDTH(64)) u_wr_master (...);
axi5_slave_rd      #(.AXI_DATA_WIDTH(64)) u_rd_slave  (...);
axi5_slave_wr      #(.AXI_DATA_WIDTH(64)) u_wr_slave  (...);
```

---

## Navigation

- **[Back to RTL Documentation](../index.md)** - Return to main RTL documentation index
