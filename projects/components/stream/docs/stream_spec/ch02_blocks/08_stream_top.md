# STREAM Top-Level Integration Specification

**Module:** `stream_top.sv`
**Location:** `rtl/stream_macro/`
**Status:** To be created

---

## Overview

The STREAM Top-Level module integrates all STREAM components into a complete scatter-gather DMA engine. It provides the external interfaces for APB configuration, AXI memory access, and MonBus monitoring.

### Key Features

- **8 independent channels** with shared resource arbitration
- **APB slave** for configuration
- **AXI masters** for descriptor fetch, data read, data write
- **AXIL interfaces** for MonBus error/logging
- **MonBus output** for monitoring and debugging
- **Parameterizable** performance modes for AXI engines

---

## Block Diagram

```
                           |-------------------------------------|
                           |         STREAM Top                 |
                           |                                     |
APB Config ----------------| APB Config                         |
                           |   |                                 |
                           | |----------------------------|     |
                           | |  8  Scheduler + Desc Eng   |     |
                           | |  (one per channel)         |     |
                           | `---|--------------------|---|     |
                           |     |                    |         |
                           |     |                    |         |
                           | |---------|        |---------|    |
Descriptor Fetch ----------| | Arbiter |        | Arbiter |    |
(AXI Master)               | `----|----|        `----|----|    |
                           |      |                  |         |
Data Read -----------------|  AXI Read          AXI Write      |
(AXI Master)               |  Engine            Engine          |
                           |      |                  |         |
Data Write ----------------|      |                  |         |
(AXI Master)               |  |-----------------------|        |
                           |  |     Simple SRAM       |        |
                           |  `-----------------------|        |
                           |                                     |
                           | |----------------------|           |
MonBus --------------------| |  MonBus AXIL Group   |           |
AXIL Slave ----------------| |  - Error FIFO        |           |
AXIL Master ---------------| |  - Logging           |           |
IRQ -----------------------| |  - Interrupt         |           |
                           | `----------------------|           |
                           `-------------------------------------|
```

---

## Interface

### Parameters

```systemverilog
parameter int NUM_CHANNELS = 8;              // Fixed at 8
parameter int ADDR_WIDTH = 64;               // Address bus width
parameter int DATA_WIDTH = 512;              // Data bus width
parameter int APB_ADDR_WIDTH = 32;           // APB address width
parameter int APB_DATA_WIDTH = 32;           // APB data width
parameter int AXIL_ADDR_WIDTH = 32;          // AXIL address width
parameter int AXIL_DATA_WIDTH = 32;          // AXIL data width
parameter int SRAM_DEPTH = 1024;             // SRAM depth

// Performance modes for AXI engines
parameter string RD_PERFORMANCE = "LOW";     // "LOW", "MEDIUM", "HIGH"
parameter string WR_PERFORMANCE = "LOW";     // "LOW", "MEDIUM", "HIGH"
parameter int    RD_MAX_BURST_LEN = 8;       // Read engine max burst
parameter int    WR_MAX_BURST_LEN = 16;      // Write engine max burst
```

### Ports

**Clock and Reset:**
```systemverilog
input  logic                        aclk;
input  logic                        aresetn;
```

**APB Configuration Interface:**
```systemverilog
input  logic [APB_ADDR_WIDTH-1:0]   s_apb_paddr;
input  logic                        s_apb_psel;
input  logic                        s_apb_penable;
input  logic                        s_apb_pwrite;
input  logic [APB_DATA_WIDTH-1:0]   s_apb_pwdata;
input  logic [3:0]                  s_apb_pstrb;
output logic                        s_apb_pready;
output logic [APB_DATA_WIDTH-1:0]   s_apb_prdata;
output logic                        s_apb_pslverr;
```

**AXI Master - Descriptor Fetch (256-bit):**
```systemverilog
// AR channel
output logic [ADDR_WIDTH-1:0]       m_axi_desc_araddr;
output logic [7:0]                  m_axi_desc_arlen;
output logic [2:0]                  m_axi_desc_arsize;
output logic [1:0]                  m_axi_desc_arburst;
output logic                        m_axi_desc_arvalid;
input  logic                        m_axi_desc_arready;

// R channel
input  logic [255:0]                m_axi_desc_rdata;
input  logic [1:0]                  m_axi_desc_rresp;
input  logic                        m_axi_desc_rlast;
input  logic                        m_axi_desc_rvalid;
output logic                        m_axi_desc_rready;
```

**AXI Master - Data Read (parameterizable width):**
```systemverilog
// AR channel
output logic [ADDR_WIDTH-1:0]       m_axi_rd_araddr;
output logic [7:0]                  m_axi_rd_arlen;
output logic [2:0]                  m_axi_rd_arsize;
output logic [1:0]                  m_axi_rd_arburst;
output logic                        m_axi_rd_arvalid;
input  logic                        m_axi_rd_arready;

// R channel
input  logic [DATA_WIDTH-1:0]       m_axi_rd_rdata;
input  logic [1:0]                  m_axi_rd_rresp;
input  logic                        m_axi_rd_rlast;
input  logic                        m_axi_rd_rvalid;
output logic                        m_axi_rd_rready;
```

**AXI Master - Data Write (parameterizable width):**
```systemverilog
// AW channel
output logic [ADDR_WIDTH-1:0]       m_axi_wr_awaddr;
output logic [7:0]                  m_axi_wr_awlen;
output logic [2:0]                  m_axi_wr_awsize;
output logic [1:0]                  m_axi_wr_awburst;
output logic                        m_axi_wr_awvalid;
input  logic                        m_axi_wr_awready;

// W channel
output logic [DATA_WIDTH-1:0]       m_axi_wr_wdata;
output logic [DATA_WIDTH/8-1:0]     m_axi_wr_wstrb;
output logic                        m_axi_wr_wlast;
output logic                        m_axi_wr_wvalid;
input  logic                        m_axi_wr_wready;

// B channel
input  logic [1:0]                  m_axi_wr_bresp;
input  logic                        m_axi_wr_bvalid;
output logic                        m_axi_wr_bready;
```

**AXIL Slave (MonBus Error/Interrupt Access):**
```systemverilog
// AR channel
input  logic [AXIL_ADDR_WIDTH-1:0]  s_axil_araddr;
input  logic                        s_axil_arvalid;
output logic                        s_axil_arready;

// R channel
output logic [AXIL_DATA_WIDTH-1:0]  s_axil_rdata;
output logic [1:0]                  s_axil_rresp;
output logic                        s_axil_rvalid;
input  logic                        s_axil_rready;
```

**AXIL Master (MonBus Packet Logging to Memory):**
```systemverilog
// AW channel
output logic [AXIL_ADDR_WIDTH-1:0]  m_axil_awaddr;
output logic                        m_axil_awvalid;
input  logic                        m_axil_awready;

// W channel
output logic [AXIL_DATA_WIDTH-1:0]  m_axil_wdata;
output logic [3:0]                  m_axil_wstrb;
output logic                        m_axil_wvalid;
input  logic                        m_axil_wready;

// B channel
input  logic [1:0]                  m_axil_bresp;
input  logic                        m_axil_bvalid;
output logic                        m_axil_bready;
```

**MonBus Output:**
```systemverilog
output logic                        monbus_valid;
input  logic                        monbus_ready;
output logic [63:0]                 monbus_packet;
```

**Interrupt:**
```systemverilog
output logic                        irq_out;
```

---

## Internal Instances

### Per-Channel Blocks (8 instances)

```systemverilog
// Channel 0-7: Scheduler + Descriptor Engine
for (genvar ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_channels

    // Descriptor Engine
    descriptor_engine #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(256)
    ) u_desc_engine (
        .aclk(aclk),
        .aresetn(aresetn),
        .desc_req_valid(ch_desc_req[ch]),
        .desc_req_ready(ch_desc_req_ready[ch]),
        .desc_req_addr(ch_desc_addr[ch]),
        .desc_valid(ch_desc_valid[ch]),
        .desc_ready(ch_desc_ready[ch]),
        .desc_packet(ch_desc_packet[ch]),
        // ... AXI and MonBus
    );

    // Scheduler
    scheduler #(
        .CHANNEL_ID(ch),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_scheduler (
        .aclk(aclk),
        .aresetn(aresetn),
        .cfg_enable(ch_enable[ch]),
        .desc_valid(ch_desc_valid[ch]),
        .desc_ready(ch_desc_ready[ch]),
        .desc_packet(ch_desc_packet[ch]),
        .datard_valid(ch_datard_valid[ch]),
        .datard_ready(ch_datard_ready[ch]),
        // ... more signals
    );

end
```

### Shared Resources

```systemverilog
// Channel Arbiter
channel_arbiter #(
    .NUM_CHANNELS(NUM_CHANNELS)
) u_arbiter (
    .aclk(aclk),
    .aresetn(aresetn),
    .desc_req(ch_desc_req),
    .desc_priority(ch_desc_priority),
    .desc_grant(ch_desc_grant),
    .datard_req(ch_datard_valid),
    .datard_grant(ch_datard_ready),
    .datawr_req(ch_datawr_valid),
    .datawr_grant(ch_datawr_ready)
);

// AXI Read Engine
axi_read_engine #(
    .PERFORMANCE(RD_PERFORMANCE),
    .MAX_BURST_LEN(RD_MAX_BURST_LEN),
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH)
) u_rd_engine (
    .aclk(aclk),
    .aresetn(aresetn),
    .datard_valid(datard_valid_mux),  // From arbiter mux
    .datard_ready(datard_ready_mux),
    .datard_addr(datard_addr_mux),
    .m_axi_araddr(m_axi_rd_araddr),
    // ... more signals
);

// AXI Write Engine
axi_write_engine #(
    .PERFORMANCE(WR_PERFORMANCE),
    .MAX_BURST_LEN(WR_MAX_BURST_LEN),
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH)
) u_wr_engine (
    .aclk(aclk),
    .aresetn(aresetn),
    .datawr_valid(datawr_valid_mux),  // From arbiter mux
    .datawr_ready(datawr_ready_mux),
    .datawr_addr(datawr_addr_mux),
    .m_axi_awaddr(m_axi_wr_awaddr),
    // ... more signals
);

// Simple SRAM
simple_sram #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH($clog2(SRAM_DEPTH))
) u_sram (
    .aclk(aclk),
    .aresetn(aresetn),
    .wr_en(sram_wr_en),
    .wr_addr(sram_wr_addr),
    .wr_data(sram_wr_data),
    .rd_en(sram_rd_en),
    .rd_addr(sram_rd_addr),
    .rd_data(sram_rd_data)
);

// MonBus AXIL Group
monbus_axil_group #(
    .NUM_CHANNELS(NUM_CHANNELS)
) u_monbus (
    .aclk(aclk),
    .aresetn(aresetn),
    .ch_monbus_valid(ch_monbus_valid),
    .ch_monbus_ready(ch_monbus_ready),
    .ch_monbus_packet(ch_monbus_packet),
    .s_axil_araddr(s_axil_araddr),
    .m_axil_awaddr(m_axil_awaddr),
    .irq_out(irq_out),
    // ... more signals
);

// APB Config
apb_config #(
    .NUM_CHANNELS(NUM_CHANNELS)
) u_config (
    .pclk(aclk),
    .presetn(aresetn),
    .paddr(s_apb_paddr),
    .psel(s_apb_psel),
    .ch_enable(ch_enable),
    .ch_desc_addr(ch_desc_addr),
    .ch_read_burst_len(ch_read_burst_len),
    .ch_write_burst_len(ch_write_burst_len),
    // ... more signals
);
```

---

## Resource Multiplexing

### Descriptor Fetch Arbiter

```systemverilog
// Multiplex descriptor requests to single AXI master
always_comb begin
    case (desc_grant_id)
        3'd0: m_axi_desc_araddr = ch0_desc_araddr;
        3'd1: m_axi_desc_araddr = ch1_desc_araddr;
        // ... all 8 channels
    endcase
end

// Demultiplex descriptor responses
assign ch0_desc_rvalid = m_axi_desc_rvalid && (desc_grant_id == 3'd0);
assign ch1_desc_rvalid = m_axi_desc_rvalid && (desc_grant_id == 3'd1);
// ... all 8 channels
```

### Data Read/Write Arbiters

Similar multiplexing for `datard_*` and `datawr_*` interfaces.

---

## Configuration Example

**Software initialization:**

```c
// 1. Configure global settings
write_apb(ADDR_GLOBAL_CTRL, GLOBAL_ENABLE);

// 2. Configure channel 0
write_apb(ADDR_CH0_RD_BURST, 8);   // 8-beat read bursts
write_apb(ADDR_CH0_WR_BURST, 16);  // 16-beat write bursts

// 3. Kick off transfer (write descriptor address)
write_apb(ADDR_CH0_CTRL, 0x1000_0000);

// 4. (Optional) Configure multiple channels
write_apb(ADDR_CH1_CTRL, 0x2000_0000);
write_apb(ADDR_CH2_CTRL, 0x3000_0000);
```

---

## Performance Modes

**Example configurations:**

### Tutorial Mode (Low Performance)
```systemverilog
stream_top #(
    .RD_PERFORMANCE("LOW"),
    .WR_PERFORMANCE("LOW"),
    .RD_MAX_BURST_LEN(8),
    .WR_MAX_BURST_LEN(16)
) u_stream (...);
```
**Characteristics:** Simple, clear, educational

### Production Mode (High Performance)
```systemverilog
stream_top #(
    .RD_PERFORMANCE("HIGH"),
    .WR_PERFORMANCE("HIGH"),
    .RD_MAX_BURST_LEN(256),
    .WR_MAX_BURST_LEN(256)
) u_stream (...);
```
**Characteristics:** Maximum throughput, pipelined

---

## Testing

**Test Location:** `projects/components/stream/dv/tests/integration_tests/`

**Test Scenarios:**
1. Single channel transfer (end-to-end)
2. Multi-channel concurrent transfers
3. Chained descriptors
4. Error handling and recovery
5. Performance validation (different modes)
6. MonBus packet generation
7. Interrupt handling

---

## Area Estimates

| Component | Instances | Area/Instance | Total |
|-----------|-----------|---------------|-------|
| Descriptor Engine | 8 | ~300 LUTs | ~2400 LUTs |
| Scheduler | 8 | ~400 LUTs | ~3200 LUTs |
| AXI Read Engine (Low) | 1 | ~250 LUTs | ~250 LUTs |
| AXI Write Engine (Low) | 1 | ~250 LUTs | ~250 LUTs |
| Simple SRAM | 1 | 1024 64B | 64 KB |
| Channel Arbiter | 3 | ~150 LUTs | ~450 LUTs |
| APB Config | 1 | ~350 LUTs | ~350 LUTs |
| MonBus AXIL Group | 1 | ~1000 LUTs | ~1000 LUTs |
| **Total (Low Perf)** | - | - | **~7900 LUTs + 64KB SRAM** |

**High Performance:** ~12000 LUTs + 64KB SRAM (due to AXI engine pipelining)

---

## Related Documentation

- **All Components:** `00_index.md` - Specification index
- **RAPIDS Comparison:** `../../ARCHITECTURAL_NOTES.md`
- **Source:** `rtl/stream_macro/stream_top.sv` (to be created)

---

**Last Updated:** 2025-10-17
