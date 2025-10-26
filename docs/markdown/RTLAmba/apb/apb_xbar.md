# apb_xbar

An Advanced Peripheral Bus (APB) crossbar switch that provides full connectivity between multiple APB masters and slaves with weighted round-robin arbitration, programmable address decoding, and high-performance transaction routing.

## Overview

The `apb_xbar` module implements a complete APB crossbar interconnect supporting multiple masters accessing multiple slaves through intelligent arbitration and address-based routing. It features configurable address decoding, weighted round-robin arbitration for fairness control, and comprehensive buffering to optimize system throughput in complex multi-master, multi-slave APB environments.

## Module Declaration

```systemverilog
module apb_xbar #(
    // Number of APB masters (from the master)
    parameter int M = 3,
    // Number of APB slaves (to the dest)
    parameter int S = 6,
    // Address width
    parameter int ADDR_WIDTH = 32,
    // Data width
    parameter int DATA_WIDTH = 32,
    // Strobe width
    parameter int STRB_WIDTH = DATA_WIDTH/8,
    parameter int MAX_THRESH = 16,
    parameter int DEPTH = 4,
    // Local abbreviations
    parameter int DW     = DATA_WIDTH,
    parameter int AW     = ADDR_WIDTH,
    parameter int SW     = STRB_WIDTH,
    parameter int MID    = $clog2(M),
    parameter int SID    = $clog2(S),
    parameter int MTW    = $clog2(MAX_THRESH),
    parameter int MXMTW  = M * MTW,
    parameter int SXMTW  = S * MTW,
    parameter int SLVCPW = AW + DW + SW + 4,
    parameter int SLVRPW = DW + 1,
    parameter int MSTCPW = AW + DW + SW + 6,
    parameter int MSTRPW = DW + 3
) (
    input  logic                         pclk,
    input  logic                         presetn,

    // Slave enable for addr decoding
    input  logic [S-1:0]                 SLAVE_ENABLE,
    // Slave address base
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_BASE,
    // Slave address limit
    input  logic [S-1:0][ADDR_WIDTH-1:0] SLAVE_ADDR_LIMIT,
    // Thresholds for the Weighted Round Robin Arbiters
    input  logic [MXMTW-1:0]             MST_THRESHOLDS,
    input  logic [SXMTW-1:0]             SLV_THRESHOLDS,

    // Master interfaces - These are from the APB master
    input  logic [M-1:0]                 m_apb_psel,
    input  logic [M-1:0]                 m_apb_penable,
    input  logic [M-1:0]                 m_apb_pwrite,
    input  logic [M-1:0][2:0]            m_apb_pprot,
    input  logic [M-1:0][ADDR_WIDTH-1:0] m_apb_paddr,
    input  logic [M-1:0][DATA_WIDTH-1:0] m_apb_pwdata,
    input  logic [M-1:0][STRB_WIDTH-1:0] m_apb_pstrb,
    output logic [M-1:0]                 m_apb_pready,
    output logic [M-1:0][DATA_WIDTH-1:0] m_apb_prdata,
    output logic [M-1:0]                 m_apb_pslverr,

    // Slave interfaces - these are to the APB destinations
    output logic [S-1:0]                 s_apb_psel,
    output logic [S-1:0]                 s_apb_penable,
    output logic [S-1:0]                 s_apb_pwrite,
    output logic [S-1:0][2:0]            s_apb_pprot,
    output logic [S-1:0][ADDR_WIDTH-1:0] s_apb_paddr,
    output logic [S-1:0][DATA_WIDTH-1:0] s_apb_pwdata,
    output logic [S-1:0][STRB_WIDTH-1:0] s_apb_pstrb,
    input  logic [S-1:0]                 s_apb_pready,
    input  logic [S-1:0][DATA_WIDTH-1:0] s_apb_prdata,
    input  logic [S-1:0]                 s_apb_pslverr
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| M | int | 3 | Number of APB masters (input side) |
| S | int | 6 | Number of APB slaves (output side) |
| ADDR_WIDTH | int | 32 | APB address bus width |
| DATA_WIDTH | int | 32 | APB data bus width |
| STRB_WIDTH | int | DATA_WIDTH/8 | APB write strobe width |
| MAX_THRESH | int | 16 | Maximum arbitration threshold |
| DEPTH | int | 4 | Internal buffer depth (2^DEPTH entries) |

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| pclk | 1 | Input | APB clock |
| presetn | 1 | Input | APB active-low reset |

### Configuration Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| SLAVE_ENABLE | S | Input | Per-slave enable bits |
| SLAVE_ADDR_BASE | S × ADDR_WIDTH | Input | Base address for each slave |
| SLAVE_ADDR_LIMIT | S × ADDR_WIDTH | Input | Limit address for each slave |
| MST_THRESHOLDS | M × MTW | Input | Master arbitration thresholds |
| SLV_THRESHOLDS | S × MTW | Input | Slave arbitration thresholds |

### Master Interfaces (Input Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_apb_psel | M | Input | Master select signals |
| m_apb_penable | M | Input | Master enable signals |
| m_apb_pwrite | M | Input | Master write/read indicators |
| m_apb_pprot | M × 3 | Input | Master protection attributes |
| m_apb_paddr | M × ADDR_WIDTH | Input | Master addresses |
| m_apb_pwdata | M × DATA_WIDTH | Input | Master write data |
| m_apb_pstrb | M × STRB_WIDTH | Input | Master write strobes |
| m_apb_pready | M | Output | Master ready signals |
| m_apb_prdata | M × DATA_WIDTH | Output | Master read data |
| m_apb_pslverr | M | Output | Master error signals |

### Slave Interfaces (Output Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_apb_psel | S | Output | Slave select signals |
| s_apb_penable | S | Output | Slave enable signals |
| s_apb_pwrite | S | Output | Slave write/read indicators |
| s_apb_pprot | S × 3 | Output | Slave protection attributes |
| s_apb_paddr | S × ADDR_WIDTH | Output | Slave addresses |
| s_apb_pwdata | S × DATA_WIDTH | Output | Slave write data |
| s_apb_pstrb | S × STRB_WIDTH | Output | Slave write strobes |
| s_apb_pready | S | Input | Slave ready signals |
| s_apb_prdata | S × DATA_WIDTH | Input | Slave read data |
| s_apb_pslverr | S | Input | Slave error signals |

## Architecture

### Crossbar Topology

The crossbar provides full connectivity between all masters and slaves:

```
Master 0 ──┐
Master 1 ──┼── Crossbar ──┬── Slave 0
Master 2 ──┘    Switch    ├── Slave 1
   ...                    ├── Slave 2
                          └── ...
```

### Key Components

1. **APB Slave Stubs**: Convert APB protocol to command/response interface (master side)
2. **APB Master Stubs**: Convert command/response interface to APB protocol (slave side)
3. **Address Decoders**: Route transactions based on configurable address ranges
4. **Round-Robin Arbiters**: Uses proven `arbiter_round_robin` module with ACK-based transaction locking
5. **Side Queues**: Buffer master IDs for response routing
6. **Multiplexers/Demultiplexers**: Route commands and responses

**Note:** Generated crossbars (1to1, 2to1, 1to4, 2to4) use the proven `arbiter_round_robin` module from `rtl/common/` with WAIT_GNT_ACK=1 mode for reliable arbitration.

### Data Flow

```
APB Masters → Slave Stubs → Command Queues → Address Decode → Arbitration →
Master Stubs → APB Slaves

APB Slaves → Master Stubs → Response Queues → ID Matching → Arbitration →
Slave Stubs → APB Masters
```

## Functionality

### Address Decoding

Each slave is assigned an address range defined by:
- **SLAVE_ADDR_BASE[i]**: Starting address for slave i
- **SLAVE_ADDR_LIMIT[i]**: Ending address for slave i
- **SLAVE_ENABLE[i]**: Enable bit for slave i

Address matching logic:
```systemverilog
if (SLAVE_ENABLE[s] &&
    (addr >= SLAVE_ADDR_BASE[s]) &&
    (addr <= SLAVE_ADDR_LIMIT[s])) begin
    // Route to slave s
end
```

### Round-Robin Arbitration with ACK Mode

Generated crossbars use the `arbiter_round_robin` module from `rtl/common/`:
- **WAIT_GNT_ACK=1**: Grant locks until transaction completes
- **Grant ACK**: `grant && rsp_valid && rsp_ready` signals transaction completion
- **Request Vector**: Built from `cmd_valid` and address match (for multi-slave)
- **Fair Rotation**: Priority rotates after each transaction

**Note:** The full `apb_xbar` module with weighted thresholds is separate from the generated crossbars. Generated crossbars (1to1, 2to1, 1to4, 2to4) use standard round-robin for simplicity and reliability.

### Transaction Buffering

Internal queues provide:
1. **Command Buffering**: Stores pending transactions
2. **Response Buffering**: Stores completed transactions
3. **ID Tracking**: Maintains master-slave associations

## Timing Characteristics

### Latency Components

| Component | Latency | Description |
|-----------|---------|-------------|
| Stub Conversion | 1 cycle | APB to command/response |
| Address Decode | 0 cycles | Combinatorial logic |
| Arbitration | 1 cycle | Grant generation |
| Buffer Transit | 1 cycle | Queue traversal |
| **Total Minimum** | **3 cycles** | Best case path |

### Throughput Metrics

| Metric | Value | Conditions |
|--------|-------|------------|
| Maximum Frequency | 200-400 MHz | Technology dependent |
| Peak Throughput | 1 transaction/cycle/path | No conflicts |
| Sustained Throughput | 85-95% of peak | With typical arbitration |
| Concurrent Transactions | Up to M×S | All paths active |

## Usage Examples

### Basic Multi-Core System

```systemverilog
apb_xbar #(
    .M(4),                    // 4 CPU cores
    .S(8),                    // 8 peripheral slaves
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .DEPTH(3)                 // 8-entry buffers
) u_system_xbar (
    .pclk            (apb_clk),
    .presetn         (apb_resetn),

    // Address map configuration
    .SLAVE_ENABLE    (slave_enable),
    .SLAVE_ADDR_BASE ({
        32'h4000_7000,  // Slave 7: High-speed UART
        32'h4000_6000,  // Slave 6: SPI controller
        32'h4000_5000,  // Slave 5: I2C controller
        32'h4000_4000,  // Slave 4: GPIO controller
        32'h4000_3000,  // Slave 3: Timer 3
        32'h4000_2000,  // Slave 2: Timer 2
        32'h4000_1000,  // Slave 1: Timer 1
        32'h4000_0000   // Slave 0: System controller
    }),
    .SLAVE_ADDR_LIMIT ({
        32'h4000_7FFF,  // Slave 7: 4KB space
        32'h4000_6FFF,  // Slave 6: 4KB space
        32'h4000_5FFF,  // Slave 5: 4KB space
        32'h4000_4FFF,  // Slave 4: 4KB space
        32'h4000_3FFF,  // Slave 3: 4KB space
        32'h4000_2FFF,  // Slave 2: 4KB space
        32'h4000_1FFF,  // Slave 1: 4KB space
        32'h4000_0FFF   // Slave 0: 4KB space
    }),

    // Equal priority arbitration
    .MST_THRESHOLDS  ({4{4'h4}}),  // Equal priority for all masters
    .SLV_THRESHOLDS  ({8{4'h4}}),  // Equal priority for all slaves

    // Master interfaces (from CPUs)
    .m_apb_psel      (cpu_apb_psel),
    .m_apb_penable   (cpu_apb_penable),
    .m_apb_pwrite    (cpu_apb_pwrite),
    .m_apb_pprot     (cpu_apb_pprot),
    .m_apb_paddr     (cpu_apb_paddr),
    .m_apb_pwdata    (cpu_apb_pwdata),
    .m_apb_pstrb     (cpu_apb_pstrb),
    .m_apb_pready    (cpu_apb_pready),
    .m_apb_prdata    (cpu_apb_prdata),
    .m_apb_pslverr   (cpu_apb_pslverr),

    // Slave interfaces (to peripherals)
    .s_apb_psel      (periph_apb_psel),
    .s_apb_penable   (periph_apb_penable),
    .s_apb_pwrite    (periph_apb_pwrite),
    .s_apb_pprot     (periph_apb_pprot),
    .s_apb_paddr     (periph_apb_paddr),
    .s_apb_pwdata    (periph_apb_pwdata),
    .s_apb_pstrb     (periph_apb_pstrb),
    .s_apb_pready    (periph_apb_pready),
    .s_apb_prdata    (periph_apb_prdata),
    .s_apb_pslverr   (periph_apb_pslverr)
);
```

### High-Performance Computing System

```systemverilog
// HPC system with priority-based arbitration
apb_xbar #(
    .M(6),                    // Multiple masters with different priorities
    .S(12),                   // Large number of slaves
    .ADDR_WIDTH(32),
    .DATA_WIDTH(64),          // Wide data path
    .DEPTH(4),                // Large buffers for latency tolerance
    .MAX_THRESH(32)           // High threshold range
) u_hpc_xbar (
    .pclk            (hpc_clk),
    .presetn         (hpc_resetn),

    // Hierarchical address map
    .SLAVE_ENABLE    (12'h00F),       // Enable first 12 slaves
    .SLAVE_ADDR_BASE ({
        32'h5000_B000,  // Slave 11: Debug interface
        32'h5000_A000,  // Slave 10: Performance counters
        32'h5000_9000,  // Slave 9:  DMA controller 3
        32'h5000_8000,  // Slave 8:  DMA controller 2
        32'h5000_7000,  // Slave 7:  DMA controller 1
        32'h5000_6000,  // Slave 6:  Memory controller
        32'h5000_5000,  // Slave 5:  Network interface
        32'h5000_4000,  // Slave 4:  Accelerator 3
        32'h5000_3000,  // Slave 3:  Accelerator 2
        32'h5000_2000,  // Slave 2:  Accelerator 1
        32'h5000_1000,  // Slave 1:  Cache controller
        32'h5000_0000   // Slave 0:  System control
    }),
    .SLAVE_ADDR_LIMIT ({
        32'h5000_BFFF,  // 4KB each
        32'h5000_AFFF,
        32'h5000_9FFF,
        32'h5000_8FFF,
        32'h5000_7FFF,
        32'h5000_6FFF,
        32'h5000_5FFF,
        32'h5000_4FFF,
        32'h5000_3FFF,
        32'h5000_2FFF,
        32'h5000_1FFF,
        32'h5000_0FFF
    }),

    // Priority-based arbitration
    .MST_THRESHOLDS  ({
        4'hF,  // Master 5: Highest priority (system)
        4'hC,  // Master 4: High priority (real-time)
        4'h8,  // Master 3: Medium priority (compute)
        4'h8,  // Master 2: Medium priority (compute)
        4'h4,  // Master 1: Low priority (background)
        4'h2   // Master 0: Lowest priority (debug)
    }),
    .SLV_THRESHOLDS  ({12{4'h8}}),   // Equal slave priority

    // Connect interfaces
    .m_apb_*(master_apb_*),
    .s_apb_*(slave_apb_*)
);
```

### Mixed Latency System

```systemverilog
// System with mix of low-latency and high-throughput requirements
module mixed_latency_system (
    input logic apb_clk,
    input logic apb_resetn,

    // Real-time masters (low latency)
    axi_apb_if.slave  rt_masters [2],
    // Bulk transfer masters (high throughput)
    axi_apb_if.slave  bulk_masters [2],

    // Critical slaves (low latency)
    axi_apb_if.master critical_slaves [4],
    // Memory slaves (high throughput)
    axi_apb_if.master memory_slaves [4]
);

    apb_xbar #(
        .M(4),          // 2 RT + 2 bulk
        .S(8),          // 4 critical + 4 memory
        .DEPTH(2)       // Small buffers for low latency
    ) u_mixed_xbar (
        .pclk(apb_clk),
        .presetn(apb_resetn),

        // Time-sensitive address ranges
        .SLAVE_ADDR_BASE ({
            32'h6000_7000,  // Memory 3
            32'h6000_6000,  // Memory 2
            32'h6000_5000,  // Memory 1
            32'h6000_4000,  // Memory 0
            32'h6000_3000,  // Critical 3: Interrupt controller
            32'h6000_2000,  // Critical 2: Timer
            32'h6000_1000,  // Critical 1: Real-time IO
            32'h6000_0000   // Critical 0: System control
        }),

        // Latency-optimized arbitration
        .MST_THRESHOLDS ({
            4'h2,   // Master 3: Bulk (low priority)
            4'h2,   // Master 2: Bulk (low priority)
            4'hF,   // Master 1: RT (highest priority)
            4'hF    // Master 0: RT (highest priority)
        }),
        .SLV_THRESHOLDS ({
            4'h4, 4'h4, 4'h4, 4'h4,  // Memory slaves: medium
            4'hF, 4'hF, 4'hF, 4'hF   // Critical slaves: highest
        }),

        // Interface connections
        .m_apb_*(concat({rt_masters, bulk_masters})),
        .s_apb_*(concat({critical_slaves, memory_slaves}))
    );

endmodule
```

## Advanced Configuration

### Dynamic Address Mapping

```systemverilog
// Reconfigurable address decoder
logic [7:0][31:0] dynamic_addr_base;
logic [7:0][31:0] dynamic_addr_limit;
logic [7:0]       dynamic_enable;

always_ff @(posedge apb_clk) begin
    if (config_write && config_addr[15:12] == 4'h1) begin
        case (config_addr[11:0])
            12'h000: dynamic_addr_base[0]  <= config_wdata;
            12'h004: dynamic_addr_limit[0] <= config_wdata;
            12'h008: dynamic_enable[0]     <= config_wdata[0];
            // ... additional configuration registers
        endcase
    end
end

apb_xbar #(.M(3), .S(8))
u_dynamic_xbar (
    // ...
    .SLAVE_ADDR_BASE (dynamic_addr_base),
    .SLAVE_ADDR_LIMIT(dynamic_addr_limit),
    .SLAVE_ENABLE    (dynamic_enable),
    // ...
);
```

### Performance Monitoring

```systemverilog
// Transaction performance monitoring
logic [31:0] transaction_counts [M][S];
logic [31:0] arbitration_cycles [M];
logic [31:0] total_transactions;

always_ff @(posedge apb_clk) begin
    for (int m = 0; m < M; m++) begin
        for (int s = 0; s < S; s++) begin
            if (transaction_complete[m][s]) begin
                transaction_counts[m][s] <= transaction_counts[m][s] + 1;
                total_transactions <= total_transactions + 1;
            end
        end

        if (arbitration_active[m] && !arbitration_grant[m]) begin
            arbitration_cycles[m] <= arbitration_cycles[m] + 1;
        end
    end
end

// Performance metrics
assign avg_arbitration_delay = arbitration_cycles / total_transactions;
assign master_utilization = transaction_counts / total_cycles;
```

### Quality of Service (QoS)

```systemverilog
// QoS-aware threshold management
logic [3:0] qos_thresholds [M];
logic [3:0] dynamic_mst_thresh [M];

always_comb begin
    for (int m = 0; m < M; m++) begin
        case (master_qos[m])
            2'b11: dynamic_mst_thresh[m] = 4'hF;  // Critical
            2'b10: dynamic_mst_thresh[m] = 4'hC;  // High
            2'b01: dynamic_mst_thresh[m] = 4'h8;  // Medium
            2'b00: dynamic_mst_thresh[m] = 4'h4;  // Low
        endcase
    end
end

apb_xbar u_qos_xbar (
    // ...
    .MST_THRESHOLDS({dynamic_mst_thresh[3], dynamic_mst_thresh[2],
                     dynamic_mst_thresh[1], dynamic_mst_thresh[0]}),
    // ...
);
```

## Performance Optimization

### Buffer Sizing Guidelines

| System Type | Recommended DEPTH | Buffer Size | Benefit |
|-------------|-------------------|-------------|---------|
| Low Latency | 2 | 4 entries | Minimal delay |
| Balanced | 3-4 | 8-16 entries | Good throughput/latency |
| High Throughput | 4-5 | 16-32 entries | Maximum bandwidth |
| Variable Latency | 5-6 | 32-64 entries | Latency tolerance |

### Arbitration Tuning

```systemverilog
// Example threshold configurations
localparam [3:0] CRITICAL_THRESH = 4'hF;  // 15/16 cycles
localparam [3:0] HIGH_THRESH     = 4'hC;  // 12/16 cycles
localparam [3:0] NORMAL_THRESH   = 4'h8;  // 8/16 cycles
localparam [3:0] LOW_THRESH      = 4'h4;  // 4/16 cycles
localparam [3:0] BACKGROUND_THRESH = 4'h2;  // 2/16 cycles
```

### Address Map Optimization

```systemverilog
// Optimize for cache line alignment
localparam [31:0] SLAVE_BASES [8] = '{
    32'h4000_0000,  // Align to 64KB boundaries
    32'h4001_0000,  // for optimal cache behavior
    32'h4002_0000,
    32'h4003_0000,
    32'h4004_0000,
    32'h4005_0000,
    32'h4006_0000,
    32'h4007_0000
};
```

## Synthesis Considerations

### Area Optimization
- Reduce M and S parameters to minimum required
- Use smaller DEPTH values for area-constrained designs
- Share arbiters when timing allows

### Timing Optimization
- Register all crossbar outputs
- Use pipeline stages for critical paths
- Balance buffer depths with frequency requirements

### Power Optimization
- Use clock gating on unused master/slave ports
- Implement threshold-based power scaling
- Gate clocks during idle periods

## Verification Notes

### Connectivity Verification
- Verify all M×S path combinations
- Check address decoding for all ranges
- Validate arbitration fairness

### Protocol Compliance
- Check APB protocol adherence on all ports
- Verify proper PREADY handling
- Validate error propagation

### Performance Verification
- Measure throughput under various loads
- Check arbitration latency and fairness
- Verify buffer efficiency

## Related Modules

- **apb_xbar_thin**: Lightweight crossbar for simple configurations
- **apb_master**: APB master for crossbar output side (cmd/rsp to APB)
- **apb_slave**: APB slave for crossbar input side (APB to cmd/rsp)
- **arbiter_round_robin**: Proven round-robin arbiter used in generated crossbars
- **arbiter_priority_encoder**: Dependency of arbiter_round_robin
- **encoder**: Used for address decoding in multi-slave crossbars
- **apb_monitor**: APB protocol monitoring and debugging

**Generated Crossbar Dependencies:**
- `rtl/amba/gaxi/gaxi_fifo_sync.sv` (used by apb_slave/apb_master)
- `rtl/amba/gaxi/gaxi_skid_buffer.sv` (used by apb_slave/apb_master)
- `rtl/common/arbiter_round_robin.sv` (arbitration)
- `rtl/common/arbiter_priority_encoder.sv` (arbiter dependency)
- `rtl/common/encoder.sv` (multi-slave address decode)

The `apb_xbar` module provides a complete, high-performance solution for multi-master, multi-slave APB systems with advanced arbitration, flexible address decoding, and comprehensive system integration capabilities.

---

## Navigation

- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**