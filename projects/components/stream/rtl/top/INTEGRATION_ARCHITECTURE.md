# STREAM Top-Level Integration Architecture

## Overview

This document describes how the STREAM top-level wrappers integrate:
- PeakRDL-generated register block
- APB-to-descriptor kick-off router (`apbtodescr.sv`)
- Configuration block (`stream_config_block.sv`)
- Core datapath (`stream_core.sv` or `stream_core_notie.sv`)
- Monitor infrastructure (`monbus_axil_group.sv`)

## Address Map

```
0x0000_0000 - 0x0000_001C : Channel kick-off registers (CHx_CTRL)
0x0000_0100 - 0x0000_03FF : Configuration and status registers
```

### Channel Kick-Off Registers (0x00-0x1C)

```
Offset  Register        Description
------  --------------  -----------------------------------------------------
0x00    CH0_CTRL        Channel 0 descriptor address (write triggers DMA)
0x04    CH1_CTRL        Channel 1 descriptor address
0x08    CH2_CTRL        Channel 2 descriptor address
0x0C    CH3_CTRL        Channel 3 descriptor address
0x10    CH4_CTRL        Channel 4 descriptor address
0x14    CH5_CTRL        Channel 5 descriptor address
0x18    CH6_CTRL        Channel 6 descriptor address
0x1C    CH7_CTRL        Channel 7 descriptor address
```

### Configuration Registers (0x100-0x3FF)

See `stream_regs_v2.rdl` for complete register map.

## Block Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│ stream_top_ch8 (top-level wrapper)                                  │
│                                                                      │
│  ┌─────────────┐                                                    │
│  │ APB Slave   │                                                    │
│  │ (External)  │                                                    │
│  └──────┬──────┘                                                    │
│         │ APB4                                                      │
│         ↓                                                           │
│  ┌─────────────────────┐                                           │
│  │ apb_slave_cdc       │ ← Clock domain crossing (if needed)       │
│  │ (rtl/amba/apb/)     │                                            │
│  └─────────┬───────────┘                                           │
│            │ APB4                                                   │
│            ↓                                                        │
│  ┌─────────────────────────────────────────────────────────────┐  │
│  │ APB-to-CMD/RSP Converter                                     │  │
│  │ (peakrdl_to_cmdrsp.sv from converters/)                      │  │
│  └─────────┬────────────────────────────────────────────────────┘  │
│            │ CMD/RSP Interface                                     │
│            ↓                                                        │
│  ┌─────────────────────────────────────────────────────────────┐  │
│  │ Address Demux Logic (based on addr[11:8])                    │  │
│  │   - If addr[11:8] == 4'h0: Route to apbtodescr (0x00-0xFF)   │  │
│  │   - If addr[11:8] >= 4'h1: Route to registers (0x100-0xFFF)  │  │
│  └───────┬─────────────────────────────────┬───────────────────┘  │
│          │                                 │                       │
│          ↓ CMD/RSP (0x00-0x1C)             ↓ CMD/RSP (0x100-0x3FF)│
│  ┌──────────────────┐            ┌─────────────────────────────┐  │
│  │ apbtodescr.sv    │            │ stream_regs_v2 (PeakRDL)    │  │
│  │ (fub/)           │            │ (generated/)                │  │
│  │                  │            │                             │  │
│  │ Output:          │            │ Output:                     │  │
│  │  desc_apb_valid  │            │  Register fields            │  │
│  │  desc_apb_addr   │            │   (GLOBAL_CTRL_*, etc.)     │  │
│  └────────┬─────────┘            └─────────┬───────────────────┘  │
│           │                                │                       │
│           │ (kick-off)                     ↓                       │
│           │                      ┌──────────────────────────────┐  │
│           │                      │ stream_config_block.sv       │  │
│           │                      │ (top/, to be created)        │  │
│           │                      │                              │  │
│           │                      │ Maps PeakRDL register        │  │
│           │                      │ outputs to stream_core       │  │
│           │                      │ configuration inputs         │  │
│           │                      └─────────┬────────────────────┘  │
│           │                                │ (configs)             │
│           │                                ↓                       │
│           │                      ┌──────────────────────────────┐  │
│           └─────────────────────>│ stream_core.sv               │  │
│                                  │ (macro/)                     │  │
│                                  │                              │  │
│                                  │  8-channel DMA engine        │  │
│                                  │  with AXI masters            │  │
│                                  └──────┬───────────────────────┘  │
│                                         │ MonBus                   │
│                                         ↓                          │
│                                  ┌──────────────────────────────┐  │
│                                  │ monbus_axil_group.sv         │  │
│                                  │ (macro/)                     │  │
│                                  │                              │  │
│                                  │ Converts MonBus → AXI-Lite   │  │
│                                  │ for integration             │  │
│                                  └──────────────────────────────┘  │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

## CMD/RSP Interface Protocol

The CMD/RSP interface is a simplified transaction protocol used between:
1. APB-to-CMD/RSP converter
2. PeakRDL register block
3. `apbtodescr` module

### Command Channel (cmd_*)

```systemverilog
input  logic                    cmd_valid,      // Command valid
output logic                    cmd_ready,      // Command accepted
input  logic                    cmd_pwrite,     // 1=write, 0=read
input  logic [ADDR_WIDTH-1:0]   cmd_paddr,      // Byte address
input  logic [DATA_WIDTH-1:0]   cmd_pwdata,     // Write data
input  logic [DATA_WIDTH/8-1:0] cmd_pstrb,      // Byte strobes
```

### Response Channel (rsp_*)

```systemverilog
output logic                    rsp_valid,      // Response valid
input  logic                    rsp_ready,      // Response accepted
output logic [DATA_WIDTH-1:0]   rsp_prdata,     // Read data
output logic                    rsp_pslverr,    // Error flag
```

### Transaction Flow

```
1. Command Phase:
   - Master asserts cmd_valid with address and control
   - Slave asserts cmd_ready when it can accept
   - Handshake: cmd_valid && cmd_ready

2. Response Phase:
   - Slave asserts rsp_valid with data and/or error
   - Master asserts rsp_ready when ready to accept
   - Handshake: rsp_valid && rsp_ready

3. Independent Channels:
   - Command and response are decoupled
   - Multiple commands can be in flight (pipelined)
```

## Integration Components

### 1. apb_slave_cdc (Optional)

**Location:** `rtl/amba/apb/apb_slave_cdc.sv`

**Purpose:** Clock domain crossing from external APB clock to internal STREAM clock

**When to use:**
- APB interface runs at different clock than STREAM core
- Common: APB @ 100 MHz, STREAM @ 250 MHz

**Configuration:**
```systemverilog
apb_slave_cdc #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32)
) u_apb_cdc (
    // External APB clock domain
    .pclk       (apb_clk),
    .presetn    (apb_rst_n),
    .paddr_in   (s_apb_paddr),
    .psel_in    (s_apb_psel),
    // ... external APB signals

    // Internal STREAM clock domain
    .aclk       (aclk),
    .aresetn    (aresetn),
    .paddr_out  (int_paddr),
    .psel_out   (int_psel),
    // ... internal APB signals
);
```

### 2. peakrdl_to_cmdrsp

**Location:** `projects/components/converters/rtl/peakrdl_to_cmdrsp.sv`

**Purpose:** Converts APB4 protocol to CMD/RSP interface

**Configuration:**
```systemverilog
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),   // 4KB address space (0x000-0xFFF)
    .DATA_WIDTH(32)
) u_apb_to_cmdrsp (
    .aclk       (aclk),
    .aresetn    (aresetn),

    // From APB interface
    .cmd_valid  (apb_cmd_valid),
    .cmd_ready  (apb_cmd_ready),
    .cmd_pwrite (apb_pwrite),
    .cmd_paddr  (apb_paddr[11:0]),  // Only lower 12 bits
    .cmd_pwdata (apb_pwdata),
    .cmd_pstrb  (apb_pstrb),

    .rsp_valid  (apb_rsp_valid),
    .rsp_ready  (apb_rsp_ready),
    .rsp_prdata (apb_rsp_prdata),
    .rsp_pslverr(apb_rsp_pslverr),

    // To PeakRDL register block (passthrough interface)
    .regblk_req         (...),
    .regblk_req_is_wr   (...),
    // ... PeakRDL passthrough signals
);
```

### 3. Address Demux Logic

**Created in top-level wrapper**

**Purpose:** Route CMD/RSP transactions to either `apbtodescr` or PeakRDL registers

**Logic:**
```systemverilog
// Decode based on address bits [11:5]
// 0x000-0x01F (32 bytes): Kick-off registers → apbtodescr
// 0x100-0x3FF (768 bytes): Config registers → PeakRDL

logic cmd_to_kickoff;
logic cmd_to_regs;

assign cmd_to_kickoff = (cmd_paddr[11:5] == 7'h00);  // 0x00-0x1F
assign cmd_to_regs    = (cmd_paddr[11:8] >= 4'h1);   // 0x100+

// Route command
assign kickoff_cmd_valid = apb_cmd_valid && cmd_to_kickoff;
assign regs_cmd_valid    = apb_cmd_valid && cmd_to_regs;

// Mux response
always_comb begin
    if (r_last_access_kickoff) begin
        apb_rsp_valid  = kickoff_rsp_valid;
        apb_rsp_prdata = kickoff_rsp_prdata;
        apb_rsp_pslverr = kickoff_rsp_pslverr;
    end else begin
        apb_rsp_valid  = regs_rsp_valid;
        apb_rsp_prdata = regs_rsp_prdata;
        apb_rsp_pslverr = regs_rsp_pslverr;
    end
end

// Track which path was used for response routing
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        r_last_access_kickoff <= 1'b0;
    end else if (apb_cmd_valid && apb_cmd_ready) begin
        r_last_access_kickoff <= cmd_to_kickoff;
    end
end
```

### 4. stream_config_block (To Be Created)

**Purpose:** Map PeakRDL register outputs to `stream_core` configuration inputs

**Key Mappings:**

```systemverilog
module stream_config_block #(
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64
) (
    input  logic clk,
    input  logic rst_n,

    // From PeakRDL register block
    input  logic        reg_global_enable,
    input  logic [7:0]  reg_channel_enable,
    input  logic [7:0]  reg_channel_reset,
    input  logic [15:0] reg_sched_timeout_cycles,
    input  logic        reg_sched_timeout_enable,
    // ... (all other register fields)

    // To stream_core
    output logic [NUM_CHANNELS-1:0] cfg_channel_enable,
    output logic [NUM_CHANNELS-1:0] cfg_channel_reset,
    output logic [15:0]             cfg_sched_timeout_cycles,
    output logic                    cfg_sched_timeout_enable,
    // ... (all other config signals)

    // Monitor configuration expansion
    output logic                    cfg_desc_mon_enable,
    output logic                    cfg_desc_mon_err_enable,
    output logic                    cfg_desc_mon_perf_enable,
    output logic                    cfg_desc_mon_timeout_enable,
    output logic [31:0]             cfg_desc_mon_timeout_cycles,
    output logic [31:0]             cfg_desc_mon_latency_thresh,
    output logic [15:0]             cfg_desc_mon_pkt_mask,
    output logic [3:0]              cfg_desc_mon_err_select,
    output logic [7:0]              cfg_desc_mon_err_mask,
    output logic [7:0]              cfg_desc_mon_timeout_mask,
    output logic [7:0]              cfg_desc_mon_compl_mask,
    output logic [7:0]              cfg_desc_mon_thresh_mask,
    output logic [7:0]              cfg_desc_mon_perf_mask,
    output logic [7:0]              cfg_desc_mon_addr_mask,
    output logic [7:0]              cfg_desc_mon_debug_mask,
    // ... (repeat for read/write engine monitors)
);

// Simple assignment mapping
assign cfg_channel_enable = reg_channel_enable;
assign cfg_channel_reset = reg_channel_reset;
// ... etc.

// Monitor config field extraction from packed registers
assign cfg_desc_mon_enable        = reg_daxmon_enable[0];
assign cfg_desc_mon_err_enable    = reg_daxmon_enable[1];
assign cfg_desc_mon_perf_enable   = reg_daxmon_enable[4];
assign cfg_desc_mon_timeout_cycles= reg_daxmon_timeout;
// ... etc.

endmodule
```

### 5. stream_core_notie (Variant)

**Purpose:** Wrapper around `stream_core.sv` with monitors disabled

**Approach:** Tie off all monitor configuration inputs internally

```systemverilog
module stream_core_notie #(
    // Same parameters as stream_core
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    // ...
) (
    // Clock and reset
    input  logic clk,
    input  logic rst_n,

    // Configuration (NO monitor configs exposed)
    input  logic [NUM_CHANNELS-1:0] cfg_channel_enable,
    input  logic [NUM_CHANNELS-1:0] cfg_channel_reset,
    input  logic [15:0]             cfg_sched_timeout_cycles,
    // ... (only non-monitor configs)

    // AXI interfaces (same as stream_core)
    // ...

    // NO MonBus output (monitors disabled)
);

// Instantiate stream_core with monitors tied off
stream_core #(
    .NUM_CHANNELS(NUM_CHANNELS),
    .DATA_WIDTH(DATA_WIDTH),
    // ...
) u_core (
    .clk(clk),
    .rst_n(rst_n),

    // Pass through configs
    .cfg_channel_enable(cfg_channel_enable),
    // ...

    // Tie off all monitor configs
    .cfg_desc_mon_enable(1'b0),
    .cfg_desc_mon_err_enable(1'b0),
    .cfg_desc_mon_perf_enable(1'b0),
    .cfg_desc_mon_timeout_enable(1'b0),
    .cfg_desc_mon_timeout_cycles(32'h0),
    .cfg_desc_mon_latency_thresh(32'h0),
    .cfg_desc_mon_pkt_mask(16'h0),
    .cfg_desc_mon_err_select(4'h0),
    .cfg_desc_mon_err_mask(8'h0),
    .cfg_desc_mon_timeout_mask(8'h0),
    .cfg_desc_mon_compl_mask(8'h0),
    .cfg_desc_mon_thresh_mask(8'h0),
    .cfg_desc_mon_perf_mask(8'h0),
    .cfg_desc_mon_addr_mask(8'h0),
    .cfg_desc_mon_debug_mask(8'h0),

    // Repeat for read/write engine monitors
    .cfg_rdeng_mon_enable(1'b0),
    // ...
    .cfg_wreng_mon_enable(1'b0),
    // ...

    // AXI interfaces pass through
    // ...

    // MonBus tied off (not connected)
    .mon_valid(),  // Unconnected
    .mon_ready(1'b1),  // Always ready
    .mon_packet()  // Unconnected
);

endmodule
```

## Top-Level Wrapper Variants

### stream_top_ch8.sv (No Monitors)

**Features:**
- Full APB configuration interface
- Channel kick-off via `apbtodescr`
- Uses `stream_core_notie` (monitors disabled)
- No MonBus output

**Parameters:**
```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int DATA_WIDTH = 512;
parameter int SRAM_DEPTH = 4096;
```

### stream_top_mon_ch8.sv (Monitors Enabled)

**Features:**
- Full APB configuration interface (including monitor configs)
- Channel kick-off via `apbtodescr`
- Uses `stream_core` (monitors enabled)
- MonBus output exposed via `monbus_axil_group`
- AXI-Lite interface for monitor packet streaming

**Parameters:**
```systemverilog
parameter int NUM_CHANNELS = 8;
parameter int DATA_WIDTH = 512;
parameter int SRAM_DEPTH = 4096;
parameter int MONBUS_FIFO_DEPTH = 256;  // MonBus packet FIFO
```

### Reduced Channel Variants

Similar structure, just parameterized for 1, 2, or 4 channels:
- `stream_top_ch1.sv` / `stream_top_mon_ch1.sv`
- `stream_top_ch2.sv` / `stream_top_mon_ch2.sv`
- `stream_top_ch4.sv` / `stream_top_mon_ch4.sv`

## Integration Checklist

When integrating a STREAM top-level wrapper:

- [ ] Choose variant:
  - [ ] Number of channels (1, 2, 4, or 8)
  - [ ] Monitors enabled? (top vs top_mon)
- [ ] Connect APB interface (clock, reset, address, data, control)
- [ ] If CDC needed, use `apb_slave_cdc`
- [ ] Connect AXI master interfaces:
  - [ ] Descriptor fetch (256-bit)
  - [ ] Data read (parameterizable width)
  - [ ] Data write (parameterizable width)
- [ ] If monitors enabled:
  - [ ] Connect MonBus AXI-Lite interface
  - [ ] Configure monitor packet destinations
- [ ] Write descriptor addresses to CHx_CTRL registers to trigger DMA
- [ ] Configure via APB registers (0x100-0x3FF range)

## Next Steps

1. Install PeakRDL: `pip install peakrdl peakrdl-regblock`
2. Generate register block RTL from `stream_regs_v2.rdl`
3. Create `stream_config_block.sv`
4. Create `stream_core_notie.sv`
5. Create all top-level wrapper variants
6. Create integration tests

## References

- PeakRDL generation: `PEAKRDL_GENERATION.md`
- Register map: `stream_regs_v2.rdl`
- Core datapath: `../macro/stream_core.sv`
- Kick-off router: `../fub/apbtodescr.sv`
- CMD/RSP converter: `../../../converters/rtl/peakrdl_to_cmdrsp.sv`
- APB CDC: `../../../../rtl/amba/apb/apb_slave_cdc.sv`
