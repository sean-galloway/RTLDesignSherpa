# AMBA (Advanced Microcontroller Bus Architecture) Index

Welcome to the RTLAmba documentation. This library provides SystemVerilog implementations of AMBA protocol interfaces and components for SoC designs. The library includes comprehensive implementations of various AMBA protocols with configurable parameters, optimizations for power efficiency, and utilities for robust system integration.

## Module Collections

### [APB (Advanced Peripheral Bus)](apb/apb_index.md)

The APB collection provides low-power, low-complexity interfaces for connecting peripheral devices to an SoC. These modules implement the AMBA APB protocol with features such as:

- Standard master and slave interfaces with command/response architecture
- Clock domain crossing (CDC) capabilities for multi-clock designs
- Power-optimized variants with clock gating support
- Stub implementations for simplified testing and verification

Perfect for connecting low-bandwidth peripherals such as configuration registers, timers, and simple I/O devices with minimal resource usage.

### [AXI (Advanced eXtensible Interface)](axi/axi_index.md)

The AXI collection implements the full-featured AMBA AXI4 protocol for high-performance, high-bandwidth connections between on-chip components. These modules offer:

- Complete implementation of all five AXI4 channels with proper handshaking
- Transaction splitting functionality for optimal memory access patterns
- Comprehensive error monitoring and timeout detection
- Power-optimized variants with intelligent clock gating
- Configurable buffering for improved timing closure and throughput

Ideal for high-performance memory interfaces, DMA controllers, and high-bandwidth IP blocks within complex SoC designs.

### [AXI-Lite (AXI4-Lite)](axil/axil_index.md)

The AXI-Lite collection provides simplified AXI interfaces for register access and control paths. These modules feature:

- Streamlined implementation of the AXI4-Lite protocol
- Reduced complexity compared to full AXI while maintaining compatibility
- Power-optimized variants with clock gating capability
- Comprehensive error detection and reporting
- Configurable buffering for timing optimization

Perfect for configuration and status registers, control interfaces, and other low-bandwidth control paths within an SoC.

### [AXI Stubs](axi_stubs/axi_stubs_index.md)

The AXI Stubs collection offers simplified interfaces for verification and testing of AXI components. These stub implementations provide:

- Packetized interfaces for clean test environment integration
- Support for all AXI4 features including bursts and quality of service
- Separate modules for read and write paths
- Configurable buffer depths for performance tuning
- Buffer count monitoring for flow control

Essential tools for efficient verification of AXI-based designs with reduced complexity in testbench development.

### [AMBA Fabric Components](fabric/amba_fabric_index.md)

The Fabric collection provides interconnect components that enable communication between multiple masters and slaves in a complex SoC design:

- APB crossbar implementations with configurable masters and slaves
- Protocol converters for bridging between AXI and APB domains
- Support for clock domain crossing in heterogeneous systems
- Weighted arbitration schemes for fair access to shared resources
- Configurable address mapping for flexible system architecture

These components form the backbone of SoC communication infrastructure, enabling efficient data transfer between various IP blocks.

### [AMBA Utilities](utility/utility_index.md)

The Utilities collection offers essential building blocks and helper modules for AMBA-based designs:

- Clock gating controllers for power optimization
- Error monitoring systems for protocol violation detection
- Address generation logic for transaction handling
- Clock domain crossing components for robust multi-clock designs
- Specialized FIFOs and buffers for improved performance and timing

These utilities provide the fundamental infrastructure needed for implementing robust and efficient AMBA interfaces.

## Getting Started

To integrate these modules into your design:

1. Choose the appropriate protocol (APB, AXI, AXI-Lite) based on your performance and complexity requirements
2. Select standard or power-optimized (_cg) variants based on your power constraints
3. Configure the module parameters (address width, data width, buffer depths, etc.) to match your system requirements
4. Connect the module interfaces to your design following the AMBA protocol specifications
5. Use the utility modules as needed for clock management, error monitoring, and clock domain crossing

For detailed information about each module, please refer to the corresponding documentation pages linked above.

---
[Back to Readme](../../../README.md)
---
