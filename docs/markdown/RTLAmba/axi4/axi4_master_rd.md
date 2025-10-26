# axi4_master_rd

An AXI4 read master module that provides high-performance read transaction processing with dual skid buffer architecture for optimal throughput and pipeline efficiency in AXI4 memory-mapped systems.

## Overview

The `axi4_master_rd` module implements a complete AXI4 read master interface with integrated address and data channel buffering using GAXI skid buffers. It acts as a bridge between upstream AXI4 read requestors and downstream AXI4 memory interfaces, providing transaction buffering, pipeline optimization, and flow control to maximize memory subsystem performance.

## Module Declaration

```systemverilog
module axi4_master_rd #(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Short and calculated params
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
) (
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (Input Side) - FUB
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_axi_arid,
    input  logic [AW-1:0]              fub_axi_araddr,
    input  logic [7:0]                 fub_axi_arlen,
    input  logic [2:0]                 fub_axi_arsize,
    input  logic [1:0]                 fub_axi_arburst,
    input  logic                       fub_axi_arlock,
    input  logic [3:0]                 fub_axi_arcache,
    input  logic [2:0]                 fub_axi_arprot,
    input  logic [3:0]                 fub_axi_arqos,
    input  logic [3:0]                 fub_axi_arregion,
    input  logic [UW-1:0]              fub_axi_aruser,
    input  logic                       fub_axi_arvalid,
    output logic                       fub_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_axi_rid,
    output logic [DW-1:0]              fub_axi_rdata,
    output logic [1:0]                 fub_axi_rresp,
    output logic                       fub_axi_rlast,
    output logic [UW-1:0]              fub_axi_ruser,
    output logic                       fub_axi_rvalid,
    input  logic                       fub_axi_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

    // Status outputs for clock gating
    output logic                       busy
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AR | int | 2 | Address channel skid buffer depth (2^N entries) |
| SKID_DEPTH_R | int | 4 | Read data channel skid buffer depth (2^N entries) |
| AXI_ID_WIDTH | int | 8 | AXI transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address bus width |
| AXI_DATA_WIDTH | int | 32 | AXI data bus width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| AXI_WSTRB_WIDTH | int | AXI_DATA_WIDTH/8 | AXI write strobe width (calculated) |

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock |
| aresetn | 1 | Input | AXI active-low reset |

### Slave AXI Interface (Input Side - FUB)

#### Read Address Channel (AR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_arid | AXI_ID_WIDTH | Input | Read address ID |
| fub_axi_araddr | AXI_ADDR_WIDTH | Input | Read address |
| fub_axi_arlen | 8 | Input | Burst length (0-255) |
| fub_axi_arsize | 3 | Input | Transfer size (bytes per beat) |
| fub_axi_arburst | 2 | Input | Burst type (FIXED, INCR, WRAP) |
| fub_axi_arlock | 1 | Input | Lock type (atomic access) |
| fub_axi_arcache | 4 | Input | Cache attributes |
| fub_axi_arprot | 3 | Input | Protection attributes |
| fub_axi_arqos | 4 | Input | Quality of Service |
| fub_axi_arregion | 4 | Input | Region identifier |
| fub_axi_aruser | AXI_USER_WIDTH | Input | User-defined signals |
| fub_axi_arvalid | 1 | Input | Read address valid |
| fub_axi_arready | 1 | Output | Read address ready |

#### Read Data Channel (R)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_rid | AXI_ID_WIDTH | Output | Read data ID |
| fub_axi_rdata | AXI_DATA_WIDTH | Output | Read data |
| fub_axi_rresp | 2 | Output | Read response (OKAY, EXOKAY, SLVERR, DECERR) |
| fub_axi_rlast | 1 | Output | Last read transfer in burst |
| fub_axi_ruser | AXI_USER_WIDTH | Output | User-defined signals |
| fub_axi_rvalid | 1 | Output | Read data valid |
| fub_axi_rready | 1 | Input | Read data ready |

### Master AXI Interface (Output Side)

#### Read Address Channel (AR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_arid | AXI_ID_WIDTH | Output | Read address ID |
| m_axi_araddr | AXI_ADDR_WIDTH | Output | Read address |
| m_axi_arlen | 8 | Output | Burst length (0-255) |
| m_axi_arsize | 3 | Output | Transfer size (bytes per beat) |
| m_axi_arburst | 2 | Output | Burst type (FIXED, INCR, WRAP) |
| m_axi_arlock | 1 | Output | Lock type (atomic access) |
| m_axi_arcache | 4 | Output | Cache attributes |
| m_axi_arprot | 3 | Output | Protection attributes |
| m_axi_arqos | 4 | Output | Quality of Service |
| m_axi_arregion | 4 | Output | Region identifier |
| m_axi_aruser | AXI_USER_WIDTH | Output | User-defined signals |
| m_axi_arvalid | 1 | Output | Read address valid |
| m_axi_arready | 1 | Input | Read address ready |

#### Read Data Channel (R)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_rid | AXI_ID_WIDTH | Input | Read data ID |
| m_axi_rdata | AXI_DATA_WIDTH | Input | Read data |
| m_axi_rresp | 2 | Input | Read response (OKAY, EXOKAY, SLVERR, DECERR) |
| m_axi_rlast | 1 | Input | Last read transfer in burst |
| m_axi_ruser | AXI_USER_WIDTH | Input | User-defined signals |
| m_axi_rvalid | 1 | Input | Read data valid |
| m_axi_rready | 1 | Output | Read data ready |

### Status Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module activity indicator for clock gating |

## Architecture

### Dual Buffer Design

The module employs a dual skid buffer architecture:

1. **AR Channel Buffer**: Buffers read address transactions
2. **R Channel Buffer**: Buffers read data responses

### Data Flow

```
FUB AXI → AR Skid Buffer → Master AXI → Memory/Slave
    ↑                                         ↓
FUB AXI ← R Skid Buffer ← Master AXI ← Memory/Slave
```

### Key Features

- **Pipeline Optimization**: Dual buffering eliminates pipeline stalls
- **AXI4 Compliance**: Full AXI4 protocol support including all signals
- **Flow Control**: Independent buffering for address and data channels
- **Clock Gating Support**: Busy signal for power optimization
- **Burst Support**: Full burst transaction handling (1-256 beats)
- **ID Preservation**: Transaction ID forwarding and matching
- **Error Handling**: Proper error response propagation

## Functionality

### Address Channel Processing

1. **Address Capture**: Incoming address transactions buffered in AR skid buffer
2. **Address Forward**: Buffered addresses forwarded to master interface
3. **Flow Control**: Ready/valid handshaking manages buffer flow

### Data Channel Processing

1. **Data Reception**: Read data from master interface buffered in R skid buffer
2. **Data Forward**: Buffered data forwarded to FUB interface
3. **Transaction Matching**: ID-based transaction correlation maintained

### Busy Signal Generation

The busy output indicates module activity:
```systemverilog
busy = (ar_buffer_count > 0) || (r_buffer_count > 0) ||
       fub_axi_arvalid || m_axi_rvalid;
```

## Timing Characteristics

### Buffer Latency

| Buffer | Default Depth | Latency | Description |
|--------|---------------|---------|-------------|
| AR Channel | 4 entries (DEPTH=2) | 1 cycle | Address buffering |
| R Channel | 16 entries (DEPTH=4) | 1 cycle | Data buffering |

### Performance Metrics

| Metric | Value | Conditions |
|--------|-------|------------|
| Maximum Frequency | 300-600 MHz | Technology dependent |
| Address Throughput | 1 transaction/cycle | When buffers not full |
| Data Throughput | 1 beat/cycle | When buffers not empty |
| Pipeline Efficiency | 95-99% | With appropriate buffer sizing |

### Transaction Latency

| Transaction Type | Latency | Description |
|------------------|---------|-------------|
| Single Read | 2-3 cycles | Address → Data (minimum) |
| Burst Read | 2+N cycles | Address + N data beats |
| Back-to-back | 1 cycle/txn | Sustained rate with buffering |

## Usage Examples

### Basic AXI4 Read Master Configuration

```systemverilog
axi4_master_rd #(
    .SKID_DEPTH_AR(2),        // 4-entry address buffer
    .SKID_DEPTH_R(4),         // 16-entry data buffer
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .AXI_USER_WIDTH(1)
) u_axi4_rd_master (
    .aclk            (axi_clk),
    .aresetn         (axi_resetn),

    // Slave interface (from CPU/DMA)
    .fub_axi_arid      (cpu_axi_arid),
    .fub_axi_araddr    (cpu_axi_araddr),
    .fub_axi_arlen     (cpu_axi_arlen),
    .fub_axi_arsize    (cpu_axi_arsize),
    .fub_axi_arburst   (cpu_axi_arburst),
    .fub_axi_arlock    (cpu_axi_arlock),
    .fub_axi_arcache   (cpu_axi_arcache),
    .fub_axi_arprot    (cpu_axi_arprot),
    .fub_axi_arqos     (cpu_axi_arqos),
    .fub_axi_arregion  (cpu_axi_arregion),
    .fub_axi_aruser    (cpu_axi_aruser),
    .fub_axi_arvalid   (cpu_axi_arvalid),
    .fub_axi_arready   (cpu_axi_arready),

    .fub_axi_rid       (cpu_axi_rid),
    .fub_axi_rdata     (cpu_axi_rdata),
    .fub_axi_rresp     (cpu_axi_rresp),
    .fub_axi_rlast     (cpu_axi_rlast),
    .fub_axi_ruser     (cpu_axi_ruser),
    .fub_axi_rvalid    (cpu_axi_rvalid),
    .fub_axi_rready    (cpu_axi_rready),

    // Master interface (to memory)
    .m_axi_arid        (mem_axi_arid),
    .m_axi_araddr      (mem_axi_araddr),
    .m_axi_arlen       (mem_axi_arlen),
    .m_axi_arsize      (mem_axi_arsize),
    .m_axi_arburst     (mem_axi_arburst),
    .m_axi_arlock      (mem_axi_arlock),
    .m_axi_arcache     (mem_axi_arcache),
    .m_axi_arprot      (mem_axi_arprot),
    .m_axi_arqos       (mem_axi_arqos),
    .m_axi_arregion    (mem_axi_arregion),
    .m_axi_aruser      (mem_axi_aruser),
    .m_axi_arvalid     (mem_axi_arvalid),
    .m_axi_arready     (mem_axi_arready),

    .m_axi_rid         (mem_axi_rid),
    .m_axi_rdata       (mem_axi_rdata),
    .m_axi_rresp       (mem_axi_rresp),
    .m_axi_rlast       (mem_axi_rlast),
    .m_axi_ruser       (mem_axi_ruser),
    .m_axi_rvalid      (mem_axi_rvalid),
    .m_axi_rready      (mem_axi_rready),

    // Status for clock gating
    .busy              (rd_master_busy)
);
```

### High-Performance Memory Interface

```systemverilog
// High-performance configuration for DDR interface
axi4_master_rd #(
    .SKID_DEPTH_AR(3),        // 8-entry address buffer
    .SKID_DEPTH_R(5),         // 32-entry data buffer
    .AXI_ID_WIDTH(4),         // Reduced ID width for efficiency
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(128),     // Wide data path
    .AXI_USER_WIDTH(1)
) u_ddr_rd_master (
    .aclk            (ddr_clk),
    .aresetn         (ddr_resetn),

    // Connect to multiple read requestors via AXI interconnect
    .fub_axi_*(cpu_cluster_axi_*),

    // Connect to DDR controller
    .m_axi_*(ddr_ctrl_axi_*),

    .busy            (ddr_rd_busy)
);
```

### Multi-Master System Integration

```systemverilog
module axi_memory_system (
    input logic axi_clk,
    input logic axi_resetn,

    // CPU interface
    axi4_if.slave   cpu_axi,
    // DMA interface
    axi4_if.slave   dma_axi,
    // Memory interface
    axi4_if.master  mem_axi
);

    // Read masters for independent buffering
    axi4_master_rd #(
        .SKID_DEPTH_AR(2),
        .SKID_DEPTH_R(3),
        .AXI_ID_WIDTH(4),
        .AXI_DATA_WIDTH(64)
    ) u_cpu_rd_master (
        .aclk(axi_clk),
        .aresetn(axi_resetn),
        .fub_axi_*(cpu_axi.*),
        .m_axi_*(cpu_rd_axi.*),
        .busy(cpu_rd_busy)
    );

    axi4_master_rd #(
        .SKID_DEPTH_AR(3),
        .SKID_DEPTH_R(4),
        .AXI_ID_WIDTH(4),
        .AXI_DATA_WIDTH(64)
    ) u_dma_rd_master (
        .aclk(axi_clk),
        .aresetn(axi_resetn),
        .fub_axi_*(dma_axi.*),
        .m_axi_*(dma_rd_axi.*),
        .busy(dma_rd_busy)
    );

    // AXI interconnect for arbitration
    axi4_interconnect #(
        .NUM_MASTERS(2),
        .NUM_SLAVES(1)
    ) u_interconnect (
        .aclk(axi_clk),
        .aresetn(axi_resetn),
        .s_axi({cpu_rd_axi, dma_rd_axi}),
        .m_axi(mem_axi)
    );

endmodule
```

### Clock Gating Integration

```systemverilog
// Clock gated version for power optimization
axi4_master_rd_cg #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_DATA_WIDTH(32)
) u_rd_master_cg (
    .aclk            (axi_clk),
    .aresetn         (axi_resetn),

    // Standard AXI interfaces
    .fub_axi_*(fub_axi_*),
    .m_axi_*(m_axi_*),

    // Clock gating control
    .cg_enable       (rd_enable),
    .cg_test_enable  (scan_mode),
    .busy            (rd_busy)
);

// Use busy signal for system-level power management
always_ff @(posedge axi_clk) begin
    rd_power_gate <= !rd_busy && idle_counter > IDLE_THRESHOLD;
end
```

## Performance Optimization

### Buffer Depth Selection

Choose buffer depths based on system characteristics:

| System Type | AR Depth | R Depth | Rationale |
|-------------|----------|---------|-----------|
| Low Latency CPU | 2 (4 entries) | 3 (8 entries) | Minimize latency |
| High Throughput DMA | 3 (8 entries) | 5 (32 entries) | Maximize bandwidth |
| DDR4 Interface | 4 (16 entries) | 6 (64 entries) | Handle refresh cycles |
| PCIe Interface | 3 (8 entries) | 4 (16 entries) | Variable latency tolerance |

### Burst Optimization

```systemverilog
// Optimize for burst efficiency
localparam BURST_LENGTH = 16; // Optimize for cache line size

// Generate efficient burst addresses
always_comb begin
    axi_araddr = base_addr & ~(BURST_LENGTH * DATA_BYTES - 1); // Align
    axi_arlen  = BURST_LENGTH - 1;                            // Length
    axi_arsize = $clog2(DATA_BYTES);                          // Size
    axi_arburst = 2'b01;                                      // INCR
end
```

### Quality of Service (QoS)

```systemverilog
// QoS-aware read master configuration
always_comb begin
    case (requestor_type)
        CPU_CRITICAL:  axi_arqos = 4'hF;    // Highest priority
        CPU_NORMAL:    axi_arqos = 4'h8;    // Medium priority
        DMA_BULK:      axi_arqos = 4'h4;    // Lower priority
        BACKGROUND:    axi_arqos = 4'h1;    // Lowest priority
        default:       axi_arqos = 4'h0;
    endcase
end
```

## Advanced Features

### Transaction Monitoring

```systemverilog
// Performance monitoring integration
logic [31:0] read_transaction_count;
logic [31:0] read_burst_total;
logic [31:0] read_latency_accumulator;

always_ff @(posedge axi_clk) begin
    // Count transactions
    if (fub_axi_arvalid && fub_axi_arready) begin
        read_transaction_count <= read_transaction_count + 1;
        read_burst_total <= read_burst_total + fub_axi_arlen + 1;
    end

    // Measure latency (simplified)
    if (fub_axi_rvalid && fub_axi_rready && fub_axi_rlast) begin
        read_latency_accumulator <= read_latency_accumulator + measured_latency;
    end
end

// Average burst length and latency calculations
assign avg_burst_length = read_burst_total / read_transaction_count;
assign avg_latency = read_latency_accumulator / read_transaction_count;
```

### Error Handling and Recovery

```systemverilog
// Enhanced error handling
logic error_detected;
logic [7:0] error_count;

always_ff @(posedge axi_clk) begin
    error_detected <= fub_axi_rvalid && fub_axi_rready &&
                     (fub_axi_rresp == 2'b10 || fub_axi_rresp == 2'b11);

    if (error_detected) begin
        error_count <= error_count + 1;
        // Log error details for debugging
        error_log <= {fub_axi_rid, fub_axi_rresp, timestamp};
    end
end
```

## Synthesis Considerations

### Area Optimization
- Reduce buffer depths for area-constrained designs
- Use smaller ID widths when possible
- Share buffers across multiple masters if timing allows

### Timing Optimization
- Register all interface signals for timing closure
- Use appropriate buffer depths to break critical paths
- Consider pipeline stages for very high-frequency operation

### Power Optimization
- Use clock gating variant (`axi4_master_rd_cg`) when available
- Implement QoS-based power scaling
- Size buffers appropriately to minimize switching activity

## Verification Notes

### Protocol Compliance
- Verify AXI4 handshaking on all channels
- Check burst handling and RLAST generation
- Validate ID preservation through the pipeline

### Buffer Verification
- Test buffer overflow/underflow protection
- Verify data integrity through buffers
- Check flow control under various load conditions

### Performance Verification
- Measure sustained throughput with various patterns
- Verify buffer efficiency and utilization
- Check latency under different loading conditions

## Related Modules

- **axi4_master_rd_cg**: Clock-gated version for power optimization
- **axi4_master_wr**: Complementary AXI4 write master
- **gaxi_skid_buffer**: Underlying buffer infrastructure
- **axi4_interconnect**: AXI4 interconnect for multi-master systems
- **axi_monitor_base**: AXI4 protocol monitoring and analysis

The `axi4_master_rd` module provides a complete, high-performance solution for AXI4 read master functionality with advanced buffering, full protocol compliance, and comprehensive system integration capabilities.

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**