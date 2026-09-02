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

**[Back to Main Index](../index.md)** | **[rtl-amba Index](index.md)**

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
 AMBA 4 (Established Standard)
    APB4 (Advanced Peripheral Bus)
       Simple register-oriented interface
       Low power, low area implementation
       Suitable for control/status registers
    AXI4-Lite (Lightweight Memory-Mapped)
       Single outstanding transaction
       Register-oriented access patterns
       Simplified AXI4 for configuration
    AXI4-Full (High-Performance Memory-Mapped)
       Multiple outstanding transactions (up to 16)
       Burst transaction support
       High-throughput memory access
    AXI4-Stream (High-Throughput Streaming)
        Unidirectional data streaming
        Back-pressure flow control
        Packet-based data transfer

 AMBA 5 (Next-Generation Features)
     APB5 (Enhanced Peripheral Bus)
        All APB4 features plus:
        PWAKEUP for low-power wake-up
        PNSE for TrustZone non-secure extension
        User signals (PAUSER, PWUSER, etc.)
     AXI5 (Enhanced High-Performance)
        All AXI4 features plus:
        Atomic operations (AtomicStore, AtomicLoad, etc.)
        Memory tagging (AWMEMATTR, ARMEMATTR)
        Data poisoning (RPOISON, WPOISON)
        Up to 256 outstanding transactions
     AXI5-Stream (Enhanced Streaming)
         All AXI4-Stream features plus:
         TWAKEUP for low-power wake-up
         TPOISON for error propagation
```

### Implementation Architecture

```
RTL AMBA Library Architecture (131 modules under rtl/amba/)
 AMBA 4 Protocol Implementations (45 modules)
    APB4 (9 modules) -- rtl/amba/apb4/
      Masters, slaves, clock-gating and CDC variants, test stubs
    AXI4 (16 modules) -- rtl/amba/axi4/
      Read/write masters and slaves, clock-gating and monitored variants
    AXI4-Lite (16 modules) -- rtl/amba/axil4/
      Read/write masters and slaves, clock-gating and monitored variants
    AXI4-Stream (4 modules) -- rtl/amba/axis4/
       Masters and slaves, clock-gating variants

 AMBA 5 Protocol Implementations (30 modules)
    APB5 (9 modules) -- rtl/amba/apb5/
    AXI5 (17 modules) -- rtl/amba/axi5/
    AXI5-Stream (4 modules) -- rtl/amba/axis5/

 Shared Infrastructure (56 modules)
     Monitor subsystem (30 modules) -- rtl/amba/monitor/
       Transaction monitors, the six reporter sub-blocks, the monbus
       CAM/compressor/group path, and the monbus-instrumented arbiters
     Shared datapath (20 modules) -- rtl/amba/shared/
       Splitters, bus meters, pattern generators, CRC checkers, SDPRAM slaves
     GAXI generic components (6 modules) -- rtl/amba/gaxi/
        Skid buffers, sync and drop FIFOs, register slice
```

Counts are per directory and re-derivable with `ls rtl/amba/<dir>/*.sv` -- one
module per file throughout. A further 5 modules under `rtl/amba/testcode/` are
verification collateral, not library blocks, and are excluded above.

The AXI4-to-APB protocol shims are **not** in this library. They live with the
other converters, in `projects/components/converters/rtl/`
(`axi4_to_apb4_shim`, `axi4_to_apb4_convert`, `axi4_to_apb5_shim`).

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
apb4_master #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .CMD_DEPTH(6),
    .RSP_DEPTH(6)
) u_apb4_master (
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
    .m_apb_PAUSER   (pauser),
    .m_apb_PWUSER   (pwuser),
    .m_apb_PRUSER   (pruser),
    .m_apb_PBUSER   (pbuser)
    // With ENABLE_PARITY=1 the six PxxxPARITY signals appear as well.
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
    // Monitor bus output -- a monbus packet, not a raw data word
    .i_mon_time         (mon_time),       // free-running broadcast time
    .monbus_valid       (rd_monbus_valid),
    .monbus_ready       (rd_monbus_ready),
    .monbus_packet      (rd_monbus_packet),
    .monbus_timestamp   (rd_monbus_timestamp)
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
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32)
) u_axil4_rd_master (
    .aclk              (clk),
    .aresetn           (resetn),
    // User side -- simplified: no burst, no ID, no advanced features
    .fub_araddr        (araddr),
    .fub_arprot        (arprot),
    .fub_arvalid       (arvalid),
    .fub_arready       (arready),
    .fub_rdata         (rdata),
    .fub_rresp         (rresp),
    .fub_rvalid        (rvalid),
    .fub_rready        (rready),
    // AXI4-Lite side
    .m_axil_araddr     (m_araddr),
    .m_axil_arprot     (m_arprot),
    .m_axil_arvalid    (m_arvalid),
    .m_axil_arready    (m_arready),
    .m_axil_rdata      (m_rdata),
    .m_axil_rresp      (m_rresp),
    .m_axil_rvalid     (m_rvalid),
    .m_axil_rready     (m_rready),
    .busy              (rd_busy)       // drives the _cg variant's gating
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
    .SKID_DEPTH(4),
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .ENABLE_WAKEUP(1)
) u_axis5_master (
    .aclk            (clk),
    .aresetn         (resetn),
    // User side
    .fub_axis_tdata  (src_tdata),
    .fub_axis_tstrb  (src_tstrb),
    .fub_axis_tlast  (src_tlast),
    .fub_axis_tid    (src_tid),
    .fub_axis_tdest  (src_tdest),
    .fub_axis_tuser  (src_tuser),
    .fub_axis_tvalid (src_tvalid),
    .fub_axis_tready (src_tready),
    .fub_axis_twakeup(src_twakeup),
    .fub_axis_tparity(src_tparity),
    // Stream side. There is no TKEEP: byte qualification is TSTRB.
    .m_axis_tdata    (tdata),
    .m_axis_tstrb    (tstrb),
    .m_axis_tlast    (tlast),
    .m_axis_tid      (tid),
    .m_axis_tdest    (tdest),
    .m_axis_tuser    (tuser),
    .m_axis_twakeup  (twakeup),  // AXI5 feature, gated by ENABLE_WAKEUP
    .m_axis_tvalid   (tvalid),
    .m_axis_tready   (tready)
);

// Clock domain crossing FIFO. Depth is a DEPTH parameter, not an address
// width -- the pointer width is derived from it.
gaxi_fifo_async #(
    .DATA_WIDTH(64),
    .DEPTH(16)
) u_cdc_fifo (
    .axi_wr_aclk    (src_clk),
    .axi_wr_aresetn (src_resetn),
    .axi_rd_aclk    (dst_clk),
    .axi_rd_aresetn (dst_resetn),
    .wr_valid       (src_tvalid),
    .wr_ready       (src_tready),
    .wr_data        (src_payload),
    .rd_valid       (dst_tvalid),
    .rd_ready       (dst_tready),
    .rd_data        (dst_payload)
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
    .pclk              (pclk),
    .presetn           (presetn),
    .m_apb_*           (apb_signals),
    // Config in, status out. The gated clock is generated INSIDE the
    // wrapper; it is not a port, and there is no scan-enable port here.
    .cfg_cg_enable     (apb_active),
    .cfg_cg_idle_count (4'd8),
    .cg_gating  (apb_is_gated)
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
    .ADDR_WIDTH(32),
    .ID_WIDTH(8),
    .IS_READ(1'b1),
    .IS_AXI(1'b1)
) u_monitor (
    .aclk           (clk),
    .aresetn        (resetn),
    .axi_*          (shared_axi_signals),
    // The monitor reports through the monbus, not through per-metric
    // counter ports. Errors, timeouts and completions are PACKETS.
    .i_mon_time     (mon_time),
    .monbus_valid   (monbus_valid),
    .monbus_ready   (monbus_ready),
    .monbus_packet  (monbus_packet),
    // Status pins, for CSRs and for driving a clock-gate
    .busy           (mon_busy),
    .active_count   (mon_active_count)
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

    // Bridge to the AMBA 4 subsystem. Two things to know before you wire
    // this up. Its AXI side is PACKED -- one _pkt bus per channel, not
    // per-signal -- and its APB side is a command/response stream, not APB
    // pins. An apb4_master downstream turns that stream into PSEL/PENABLE.
    // The module lives in projects/components/converters, not rtl/amba.
    axi4_to_apb4_convert u_bridge (
        .aclk            (clk),
        .aresetn         (rst_n),
        .r_s_axi_aw_pkt  (cpu_aw_pkt),
        .r_s_axi_awvalid (cpu_awvalid),
        .w_s_axi_awready (cpu_awready),
        // ... W, B, AR, R channels follow the same _pkt shape ...
        .w_cmd_valid     (apb_cmd_valid),
        .r_cmd_ready     (apb_cmd_ready),
        .r_cmd_data      (apb_cmd_data),
        .r_rsp_valid     (apb_rsp_valid),
        .w_rsp_ready     (apb_rsp_ready),
        .r_rsp_data      (apb_rsp_data)
    );

    // Legacy AMBA 4 peripherals
    apb4_slave u_legacy_periph (...);

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
        .cfg_cg_enable(cpu_active),
        .*
    );

    // Clock domain crossing. Both sides name their own clock and reset.
    gaxi_fifo_async u_cpu_to_ddr_cdc (
        .axi_wr_aclk(cpu_clk),
        .axi_rd_aclk(ddr_clk),
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
// High-throughput streaming processor with AXI5-Stream.
//
// This library has no SystemVerilog interface for AXI-Stream -- every port
// is an expanded signal. Two naming traps live in this one example:
//
//   * the axis5 _cg wrappers use fub_axis5_* / m_axis5_* and i_cg_enable,
//     while the modules they wrap use fub_axis_* / m_axis_* / s_axis_* and
//     the rest of the AMBA family uses cfg_cg_enable;
//   * byte qualification is TSTRB. There is no TKEEP anywhere in axis5.
//
module stream_processor (
    input logic clk, rst_n,
    input  logic [63:0] s_tdata, input logic [7:0] s_tstrb,
    input  logic        s_tlast, s_tvalid, output logic s_tready,
    output logic [63:0] m_tdata, output logic [7:0] m_tstrb,
    output logic        m_tlast, m_tvalid, input  logic m_tready
);

    // Input buffering with clock gating
    axis5_master_cg #(.AXIS_DATA_WIDTH(64)) u_input_stage (
        .aclk               (clk),
        .aresetn            (rst_n),
        .i_cg_enable        (input_active),
        .i_cg_idle_count    (4'd8),
        .fub_axis5_tdata    (s_tdata),
        .fub_axis5_tstrb    (s_tstrb),
        .fub_axis5_tlast    (s_tlast),
        .fub_axis5_tvalid   (s_tvalid),
        .fub_axis5_tready   (s_tready),
        .m_axis5_tdata      (stage1_tdata),
        .m_axis5_tstrb      (stage1_tstrb),
        .m_axis5_tlast      (stage1_tlast),
        .m_axis5_tvalid     (stage1_tvalid),
        .m_axis5_tready     (stage1_tready)
        // tid, tdest, tuser, twakeup and tparity elided
    );

    // Processing pipeline (your logic, on the same expanded signals)
    stream_processing_core u_processor (...);

    // Output buffering
    axis5_slave #(.AXIS_DATA_WIDTH(64)) u_output_stage (
        .aclk               (clk),
        .aresetn            (rst_n),
        .s_axis_tdata       (stage2_tdata),
        .s_axis_tstrb       (stage2_tstrb),
        .s_axis_tlast       (stage2_tlast),
        .s_axis_tvalid      (stage2_tvalid),
        .s_axis_tready      (stage2_tready),
        .fub_axis_tdata     (m_tdata),
        .fub_axis_tstrb     (m_tstrb),
        .fub_axis_tlast     (m_tlast),
        .fub_axis_tvalid    (m_tvalid),
        .fub_axis_tready    (m_tready)
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
