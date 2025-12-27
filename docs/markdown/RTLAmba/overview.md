**[Back to Main Index](../index.md)** | **[RTLAmba Index](index.md)**

# RTL AMBA Library Overview

The RTL AMBA library provides a comprehensive implementation of ARM's Advanced Microcontroller Bus Architecture (AMBA) specifications, offering high-performance, synthesizable RTL modules for both **AMBA 4** and **AMBA 5** protocols including APB, AXI4, AXI4-Lite, and AXI4-Stream with advanced features for modern SoC designs.

## Library Philosophy

### Design Principles

The RTL AMBA library is built on the following core principles:

**Standards Compliance**: Full adherence to ARM AMBA specifications (APB4/5, AXI4/5, AXI4-Lite, AXI4/5-Stream)
**Performance Optimization**: Designed for high-frequency operation with minimal latency
**Power Efficiency**: Comprehensive clock gating and power management features
**Scalability**: Parameterizable configurations for diverse system requirements
**Verification Ready**: Built-in monitoring and debug capabilities

### Quality Standards

- **AMBA Compliant**: Certified compliance with ARM AMBA specifications
- **Synthesis Proven**: Validated across multiple technology nodes and vendors
- **Performance Optimized**: Designed for maximum throughput and minimum latency
- **Power Efficient**: Advanced power management with clock gating options
- **Verification Complete**: Comprehensive testbenches and monitoring infrastructure

---

## Architecture Overview

### AMBA Protocol Family

```
AMBA Protocol Family
├── AMBA 4 (Established Standard)
│   ├── APB4 (Advanced Peripheral Bus)
│   │   ├── Simple register-oriented interface
│   │   ├── Low power, low area implementation
│   │   └── Suitable for control/status registers
│   ├── AXI4-Lite (Lightweight Memory-Mapped)
│   │   ├── Single outstanding transaction
│   │   ├── Register-oriented access patterns
│   │   └── Simplified AXI4 for configuration
│   ├── AXI4-Full (High-Performance Memory-Mapped)
│   │   ├── Multiple outstanding transactions (up to 16)
│   │   ├── Burst transaction support
│   │   └── High-throughput memory access
│   └── AXI4-Stream (High-Throughput Streaming)
│       ├── Unidirectional data streaming
│       ├── Back-pressure flow control
│       └── Packet-based data transfer
│
└── AMBA 5 (Next-Generation Features)
    ├── APB5 (Enhanced Peripheral Bus)
    │   ├── All APB4 features plus:
    │   ├── PWAKEUP for low-power wake-up
    │   ├── PNSE for TrustZone non-secure extension
    │   └── User signals (PAUSER, PWUSER, etc.)
    ├── AXI5 (Enhanced High-Performance)
    │   ├── All AXI4 features plus:
    │   ├── Atomic operations (AtomicStore, AtomicLoad, etc.)
    │   ├── Memory tagging (AWMEMATTR, ARMEMATTR)
    │   ├── Data poisoning (RPOISON, WPOISON)
    │   └── Up to 256 outstanding transactions
    └── AXI5-Stream (Enhanced Streaming)
        ├── All AXI4-Stream features plus:
        ├── TWAKEUP for low-power wake-up
        └── TPOISON for error propagation
```

### Implementation Architecture

```
RTL AMBA Library Architecture (86+ modules)
├── AMBA 4 Protocol Implementations (47 modules)
│   ├── APB4 (9 modules)
│   │   ├── Masters & Slaves
│   │   ├── Clock Gating Variants
│   │   ├── Clock Domain Crossing
│   │   └── Test Stubs
│   ├── AXI4 (14 modules)
│   │   ├── Read/Write Masters & Slaves
│   │   ├── Clock Gating Variants
│   │   └── Test Stubs
│   ├── AXI4-Lite (8 modules)
│   │   ├── Read/Write Masters & Slaves
│   │   └── Clock Gating Variants
│   └── AXI4-Stream (4 modules)
│       ├── Masters & Slaves
│       └── Clock Gating Variants
│
├── AMBA 5 Protocol Implementations (29 modules)
│   ├── APB5 (9 modules)
│   │   ├── Masters & Slaves
│   │   ├── Clock Gating Variants
│   │   ├── Clock Domain Crossing
│   │   └── Test Stubs
│   ├── AXI5 (16 modules)
│   │   ├── Read/Write Masters & Slaves
│   │   ├── Clock Gating Variants
│   │   └── Integrated Monitor Variants
│   └── AXI5-Stream (4 modules)
│       ├── Masters & Slaves
│       └── Clock Gating Variants
│
├── Shared Infrastructure (22 modules)
│   ├── GAXI Generic Components (5 modules)
│   ├── Monitoring & Debug (10 modules)
│   ├── Clock Domain Crossing (2 modules)
│   └── Arbitration Logic (5 modules)
│
└── Protocol Bridges (2 modules)
    └── AXI4 to APB Conversion
```

---

## AMBA 4 vs AMBA 5 Comparison

### Feature Comparison Matrix

| Feature | AMBA 4 | AMBA 5 |
|---------|--------|--------|
| **APB Protocol** | APB4 | APB5 |
| Protection Signals | PPROT[2:0] | PPROT[2:0] + PNSE |
| Wake-up Signaling | Not supported | PWAKEUP |
| User Signals | Not supported | PAUSER, PWUSER, PRUSER, PBUSER |
| **AXI Protocol** | AXI4 | AXI5 |
| Outstanding Transactions | Up to 16 | Up to 256 |
| Atomic Operations | Not supported | AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare |
| Memory Tagging | Not supported | AWMEMATTR, ARMEMATTR |
| Data Poisoning | Not supported | RPOISON, WPOISON |
| Chunking | Not supported | AWCHUNKEN |
| Loop Support | Not supported | AWLOOP, ARLOOP |
| **Stream Protocol** | AXI4-Stream | AXI5-Stream |
| Wake-up Signaling | Not supported | TWAKEUP |
| Data Poisoning | Not supported | TPOISON |

### When to Use Which Version

| Requirement | Recommendation |
|-------------|----------------|
| Proven, mature design | AMBA 4 |
| Maximum compatibility | AMBA 4 |
| Atomic operations needed | AMBA 5 (AXI5) |
| Memory tagging (MTE) for security | AMBA 5 (AXI5) |
| Power management wake-up | AMBA 5 (APB5, AXI5-Stream) |
| TrustZone non-secure extension | AMBA 5 (APB5 PNSE) |
| High outstanding count (>16) | AMBA 5 (AXI5) |
| Error propagation in pipelines | AMBA 5 (POISON signals) |
| Next-generation features | AMBA 5 |

---

## Protocol Implementations

### 1. APB (Advanced Peripheral Bus)

The APB implementation provides complete solutions for low-power peripheral access in both AMBA 4 and AMBA 5 variants.

#### Key Features
- **APB4/APB5 Compliance**: Full support for both specifications
- **Power Optimization**: Clock gating variants for all components
- **Flexible Configuration**: Parameterizable address and data widths
- **CDC Support**: Clock domain crossing for multi-clock systems

#### Performance Characteristics
- **Frequency**: Up to 200 MHz typical
- **Latency**: 2-3 clock cycles per transaction
- **Throughput**: Up to 1.6 GB/s at 200 MHz with 32-bit data
- **Power**: Ultra-low power with clock gating

#### APB4 Example

```systemverilog
// APB4 Master with command/response interface
apb_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .CMD_DEPTH(6),
    .RSP_DEPTH(6)
) u_apb_master (
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PPROT    (pprot),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr),
    .m_apb_PREADY   (pready),
    // Command/Response interfaces...
);
```

#### APB5 Example

```systemverilog
// APB5 Master with enhanced features
apb5_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_apb5_master (
    // Standard APB signals
    .m_apb_PSEL     (psel),
    .m_apb_PENABLE  (penable),
    .m_apb_PADDR    (paddr),
    .m_apb_PWRITE   (pwrite),
    .m_apb_PWDATA   (pwdata),
    .m_apb_PSTRB    (pstrb),
    .m_apb_PPROT    (pprot),
    .m_apb_PRDATA   (prdata),
    .m_apb_PSLVERR  (pslverr),
    .m_apb_PREADY   (pready),
    // APB5 enhanced signals
    .m_apb_PWAKEUP  (pwakeup),
    .m_apb_PNSE     (pnse),
    .m_apb_PAUSER   (pauser),
    .m_apb_PWUSER   (pwuser),
    // ...
);
```

---

### 2. AXI4/AXI5 (High-Performance Memory-Mapped)

The AXI implementation provides maximum performance for memory-intensive applications with full AMBA 4 and AMBA 5 support.

#### Key Features
- **AXI4/AXI5 Compliance**: Full implementation of both specifications
- **Outstanding Transactions**: Up to 16 (AXI4) or 256 (AXI5) concurrent
- **Burst Support**: INCR, FIXED, and WRAP burst types
- **Advanced Features**: QoS, caching, protection, atomic ops (AXI5)

#### Performance Characteristics
- **Frequency**: Up to 500 MHz typical
- **Latency**: 1-2 clock cycles for simple transactions
- **Throughput**: Up to 32 GB/s with 64-bit data at 500 MHz
- **Outstanding**: Up to 16 (AXI4) or 256 (AXI5) concurrent transactions

#### AXI4 Example

```systemverilog
// AXI4 Read Master with skid buffers
axi4_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_axi4_rd_master (
    .fub_axi_arid      (arid),
    .fub_axi_araddr    (araddr),
    .fub_axi_arlen     (arlen),
    .fub_axi_arsize    (arsize),
    .fub_axi_arburst   (arburst),
    // ...
);
```

#### AXI5 Example with Integrated Monitor

```systemverilog
// AXI5 Read Master with integrated monitoring
axi5_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128)
) u_axi5_rd_master_mon (
    .aclk               (clk),
    .aresetn            (resetn),
    // FUB and AXI interfaces
    .fub_axi_ar*        (...),
    .m_axi_ar*          (...),
    // Monitor bus output
    .mon_valid          (rd_mon_valid),
    .mon_ready          (rd_mon_ready),
    .mon_data           (rd_mon_data)
);
```

---

### 3. AXI4-Lite (Register-Oriented Interface)

The AXI4-Lite implementation provides simplified memory-mapped access optimized for registers.

#### Key Features
- **AXI4-Lite Compliance**: Simplified AXI4 for register access
- **Single Outstanding**: One transaction at a time for simplicity
- **Register Optimized**: Designed for configuration and status registers
- **Low Overhead**: Minimal logic for area-sensitive applications

#### Performance Characteristics
- **Frequency**: Up to 400 MHz typical
- **Latency**: 1-2 clock cycles per transaction
- **Throughput**: Up to 3.2 GB/s with 32-bit data at 400 MHz
- **Area**: Minimal logic overhead

#### Usage Pattern

```systemverilog
// AXI4-Lite Master for register access
axil4_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(2),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32)
) u_axil4_rd_master (
    // Simplified interface - no burst, ID, or advanced features
    .fub_axi_araddr    (araddr),
    .fub_axi_arprot    (arprot),
    .fub_axi_arvalid   (arvalid),
    .fub_axi_arready   (arready),
    .fub_axi_rdata     (rdata),
    .fub_axi_rresp     (rresp),
    .fub_axi_rvalid    (rvalid),
    .fub_axi_rready    (rready)
);
```

---

### 4. AXI4/5-Stream (High-Throughput Streaming)

The AXI-Stream implementation provides maximum throughput for streaming data applications in both AMBA 4 and AMBA 5 variants.

#### Key Features
- **AXI4/5-Stream Compliance**: Full streaming protocol implementation
- **Flow Control**: TVALID/TREADY handshaking with backpressure
- **Packet Support**: TLAST for packet boundary indication
- **Enhanced Features**: TWAKEUP, TPOISON (AXI5-Stream)

#### Performance Characteristics
- **Frequency**: Up to 600 MHz typical
- **Throughput**: Up to 76.8 GB/s with 128-bit data at 600 MHz
- **Latency**: 0-1 clock cycles (combinational or registered)
- **Backpressure**: Efficient flow control handling

#### Stream Processing Example

```systemverilog
// AXI5-Stream data processing pipeline
axis5_master #(
    .SKID_DEPTH_T(4),
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8)
) u_axis5_master (
    .m_axis_tdata    (tdata),
    .m_axis_tstrb    (tstrb),
    .m_axis_tkeep    (tkeep),
    .m_axis_tlast    (tlast),
    .m_axis_tid      (tid),
    .m_axis_tdest    (tdest),
    .m_axis_tuser    (tuser),
    .m_axis_twakeup  (twakeup),  // AXI5 feature
    .m_axis_tvalid   (tvalid),
    .m_axis_tready   (tready)
);

// Clock domain crossing FIFO
gaxi_fifo_async #(
    .DATA_WIDTH(64),
    .ADDR_WIDTH(4)
) u_cdc_fifo (
    .s_axis_*(src_axis_*),
    .m_axis_*(dst_axis_*)
);
```

---

## Advanced Features

### 1. Clock Gating and Power Management

Every major component has a clock-gated variant for power optimization.

#### Power Savings
- **Dynamic Power**: 20-40% reduction in switching power
- **Clock Tree Power**: Significant reduction in clock network power
- **Conditional Operation**: Modules powered down when idle

#### Implementation Example

```systemverilog
// Clock-gated APB5 master
apb5_master_cg #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_apb5_master_cg (
    .m_apb_*(apb_signals),
    .cg_enable      (apb_active),
    .cg_test_enable (scan_test_mode),
    .gated_clk      (apb_gated_clk)
);
```

### 2. Monitoring and Debug Infrastructure

Comprehensive monitoring infrastructure for protocol compliance and performance analysis.

#### Monitoring Features
- **Protocol Compliance**: Real-time AMBA specification checking
- **Performance Metrics**: Bandwidth, latency, and utilization measurement
- **Transaction Tracking**: Complete transaction lifecycle monitoring
- **Error Detection**: Protocol violation and timeout detection

#### Monitor Integration

```systemverilog
// AXI5 system with integrated monitoring
axi5_master_rd_mon u_master (...);  // Monitor built-in

// Or standalone monitor
axi_monitor_base #(
    .AXI_DATA_WIDTH(32),
    .AXI_ID_WIDTH(8)
) u_monitor (
    .axi_*(shared_axi_signals),
    .transaction_count   (trans_count),
    .bandwidth_utilization (bandwidth),
    .protocol_violations (violations),
    .timeout_events     (timeouts)
);
```

### 3. Generic AXI (GAXI) Infrastructure

Shared infrastructure components for all AMBA protocols.

#### GAXI Components
- **Skid Buffers**: Pipeline optimization and timing closure
- **FIFO Components**: Buffering and clock domain crossing
- **Flow Control**: Advanced handshaking and backpressure management

---

## System Integration Patterns

### 1. AMBA 4 to AMBA 5 Migration

```systemverilog
// Gradual migration - AMBA 5 core with AMBA 4 peripherals
module mixed_amba_system (
    input logic clk, rst_n
);

    // AMBA 5 high-performance core
    axi5_master_rd_mon u_cpu_rd_master (...);
    axi5_master_wr_mon u_cpu_wr_master (...);

    // Bridge to AMBA 4 subsystem
    axi4_to_apb_convert u_bridge (
        .s_axi  (cpu_axi),
        .m_apb  (periph_apb)
    );

    // Legacy AMBA 4 peripherals
    apb_slave u_legacy_periph (...);

endmodule
```

### 2. Multi-Clock Domain System

```systemverilog
// System with multiple clock domains
module multi_clock_system (
    input logic cpu_clk, ddr_clk, periph_clk,
    input logic rst_n
);

    // CPU domain (high frequency) - AXI5
    axi5_master_rd_cg u_cpu_master (
        .aclk(cpu_clk),
        .cg_enable(cpu_active),
        .*
    );

    // Clock domain crossing
    gaxi_fifo_async u_cpu_to_ddr_cdc (
        .s_clk(cpu_clk),
        .m_clk(ddr_clk),
        .*
    );

    // DDR domain
    axi5_slave_rd u_ddr_controller (
        .aclk(ddr_clk),
        .*
    );

    // Peripheral domain (low frequency) - APB5
    apb5_slave_cdc u_periph_cdc (
        .pclk(periph_clk),
        .aclk(cpu_clk),
        .*
    );

endmodule
```

### 3. Streaming Data Pipeline

```systemverilog
// High-throughput streaming processor with AXI5-Stream
module stream_processor (
    input logic clk, rst_n,
    axi5s_if.slave  s_axis,
    axi5s_if.master m_axis
);

    axi5s_if stage1_axis();
    axi5s_if stage2_axis();

    // Input buffering with clock gating
    axis5_master_cg u_input_stage (
        .cg_enable(input_active),
        .s_axis(s_axis),
        .m_axis(stage1_axis)
    );

    // Processing pipeline
    stream_processing_core u_processor (
        .s_axis(stage1_axis),
        .m_axis(stage2_axis)
    );

    // Output buffering
    axis5_slave u_output_stage (
        .s_axis(stage2_axis),
        .m_axis(m_axis)
    );

endmodule
```

---

## Synthesis and Implementation

### Technology Optimization

#### ASIC Optimization
- **Library Mapping**: Optimized for standard cell libraries
- **Clock Tree**: Efficient clock distribution
- **Power Domain**: Support for multiple power domains
- **DFT**: Design for test integration

#### FPGA Optimization
- **Resource Utilization**: Efficient use of FPGA resources
- **Clock Management**: Use of dedicated clock resources
- **DSP Integration**: Leveraging FPGA DSP blocks
- **Block RAM**: Efficient memory utilization

### Power Optimization

- **Clock Gating**: Fine-grained clock control
- **Power Islands**: Support for power domain isolation
- **Dynamic Scaling**: Frequency and voltage scaling support
- **Low-Power Modes**: Standby and sleep mode support
- **Wake-up Signaling**: AMBA 5 PWAKEUP/TWAKEUP support

---

## Documentation Structure

| Directory | Content |
|-----------|---------|
| `apb/` | APB4 module documentation |
| `apb5/` | APB5 module documentation |
| `axi4/` | AXI4 module documentation |
| `axi5/` | AXI5 module documentation |
| `axil4/` | AXI4-Lite module documentation |
| `axis4/` | AXI4-Stream module documentation |
| `axis5/` | AXI5-Stream module documentation |
| `gaxi/` | Generic AXI infrastructure |
| `shared/` | Shared utilities and monitors |
| `shims/` | Protocol converters |
| `includes/` | Package definitions |

---

The RTL AMBA library provides a complete, high-performance solution for AMBA-based system design, combining standards compliance with advanced optimization techniques for modern SoC implementations across both AMBA 4 and AMBA 5 specifications.
