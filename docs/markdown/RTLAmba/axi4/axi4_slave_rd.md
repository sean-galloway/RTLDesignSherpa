# AXI4 Slave Read

**Module:** `axi4_slave_rd.sv`
**Location:** `rtl/amba/axi4/`
**Status:** ✅ Production Ready

---

## Overview

The AXI4 Slave Read module provides a buffered AXI4 slave read interface with configurable depth skid buffers on the AR and R channels. This module serves as an elastic buffer between an AXI4 interconnect and a memory or backend processing element, decoupling timing and providing backpressure handling.

### Key Features

- ✅ **Full AXI4 Read Support:** Complete AR and R channel implementation
- ✅ **Independent Channel Buffering:** Separate configurable depth buffers for each channel
- ✅ **Elastic Buffering:** Decouples interconnect and backend timing domains
- ✅ **Burst Support:** Full burst transaction handling with RLAST tracking
- ✅ **User Signal Support:** Carries ARUSER and RUSER signals
- ✅ **Clock Gating Support:** Busy signal for dynamic power management

---

## Module Interface

```systemverilog
module axi4_slave_rd #(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1
) (
    // Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (s_axi_*)
    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]   s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]   s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0] s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // Backend Interface (fub_axi_* - to memory/backend)
    // Read address channel (AR)
    output logic [AXI_ID_WIDTH-1:0]   fub_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] fub_axi_araddr,
    output logic [7:0]                 fub_axi_arlen,
    output logic [2:0]                 fub_axi_arsize,
    output logic [1:0]                 fub_axi_arburst,
    output logic                       fub_axi_arlock,
    output logic [3:0]                 fub_axi_arcache,
    output logic [2:0]                 fub_axi_arprot,
    output logic [3:0]                 fub_axi_arqos,
    output logic [3:0]                 fub_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0] fub_axi_aruser,
    output logic                       fub_axi_arvalid,
    input  logic                       fub_axi_arready,

    // Read data channel (R)
    input  logic [AXI_ID_WIDTH-1:0]   fub_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] fub_axi_rdata,
    input  logic [1:0]                 fub_axi_rresp,
    input  logic                       fub_axi_rlast,
    input  logic [AXI_USER_WIDTH-1:0] fub_axi_ruser,
    input  logic                       fub_axi_rvalid,
    output logic                       fub_axi_rready,

    // Status
    output logic                       busy
);
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `SKID_DEPTH_AR` | int | 2 | Depth of read address (AR) channel skid buffer |
| `SKID_DEPTH_R` | int | 4 | Depth of read data (R) channel skid buffer |
| `AXI_ID_WIDTH` | int | 8 | Width of transaction ID signals (ARID, RID) |
| `AXI_ADDR_WIDTH` | int | 32 | Width of address bus (ARADDR) |
| `AXI_DATA_WIDTH` | int | 32 | Width of data bus (RDATA), must be 8, 16, 32, 64, 128, 256, 512, or 1024 |
| `AXI_USER_WIDTH` | int | 1 | Width of user-defined signals (ARUSER, RUSER) |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | Input | 1 | AXI clock - all signals sampled on rising edge |
| `aresetn` | Input | 1 | Active-low asynchronous reset |

### Slave AXI Interface (s_axi_*)

**Read Address Channel (AR)**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_arid` | Input | `AXI_ID_WIDTH` | Read transaction ID |
| `s_axi_araddr` | Input | `AXI_ADDR_WIDTH` | Read address |
| `s_axi_arlen` | Input | 8 | Burst length (0-255 beats) |
| `s_axi_arsize` | Input | 3 | Burst size (bytes per beat) |
| `s_axi_arburst` | Input | 2 | Burst type (FIXED, INCR, WRAP) |
| `s_axi_arlock` | Input | 1 | Lock type (atomic access support) |
| `s_axi_arcache` | Input | 4 | Cache attributes |
| `s_axi_arprot` | Input | 3 | Protection attributes |
| `s_axi_arqos` | Input | 4 | Quality of Service identifier |
| `s_axi_arregion` | Input | 4 | Region identifier |
| `s_axi_aruser` | Input | `AXI_USER_WIDTH` | User-defined signal |
| `s_axi_arvalid` | Input | 1 | Read address valid |
| `s_axi_arready` | Output | 1 | Read address ready |

**Read Data Channel (R)**

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_rid` | Output | `AXI_ID_WIDTH` | Read transaction ID |
| `s_axi_rdata` | Output | `AXI_DATA_WIDTH` | Read data |
| `s_axi_rresp` | Output | 2 | Read response (OKAY, EXOKAY, SLVERR, DECERR) |
| `s_axi_rlast` | Output | 1 | Last beat of burst indicator |
| `s_axi_ruser` | Output | `AXI_USER_WIDTH` | User-defined signal |
| `s_axi_rvalid` | Output | 1 | Read data valid |
| `s_axi_rready` | Input | 1 | Read data ready |

### Backend Interface (fub_axi_*)

Mirrors the slave interface but in the opposite direction (output on AR, input on R).

### Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Indicates active transactions in buffers (for clock gating) |

---

## Functional Description

### Architecture

The AXI4 Slave Read module uses two independent `gaxi_skid_buffer` instances to provide elastic buffering on each read channel:

```
Slave (s_axi_*)           Skid Buffers          Backend (fub_axi_*)

   arvalid ──────────►┌─────────────┐──────────► arvalid
   arready ◄──────────┤  AR Buffer  │◄────────── arready
   araddr  ──────────►│  (depth=2)  │──────────► araddr
   ar*     ──────────►│             │──────────► ar*
                      └─────────────┘

   rvalid  ◄──────────┌─────────────┐◄────────── rvalid
   rready  ──────────►│  R Buffer   │──────────► rready
   rdata   ◄──────────│  (depth=4)  │◄────────── rdata
   r*      ◄──────────│             │◄────────── r*
                      └─────────────┘
```

### Channel Operations

#### Read Address (AR) Channel
1. Master presents read address and attributes via interconnect
2. AR skid buffer accepts when space available (`s_axi_arready` high)
3. Buffered address presented to backend when ready
4. Configurable depth (`SKID_DEPTH_AR`) smooths timing variations

#### Read Data (R) Channel
1. Backend returns read data with transaction ID
2. R skid buffer provides deeper buffering (default depth=4)
3. RLAST signal preserved to indicate burst boundaries
4. Data forwarded to master when ready to accept

### Busy Signal

The `busy` output indicates active transactions:
```systemverilog
busy = (ar_count > 0) || (r_count > 0) ||
       s_axi_arvalid || fub_axi_rvalid
```

Use cases:
- **Clock gating:** Disable clock when `busy` is low
- **Power management:** Enter low-power mode when idle
- **Synchronization:** Wait for idle before configuration changes

---

## Configuration Guidelines

### Buffer Depth Selection

**Read Address (SKID_DEPTH_AR):**
- Default: 2 (sufficient for most cases)
- Increase if:
  - High-latency backend address processing
  - Frequent address channel backpressure
  - Multiple outstanding bursts needed

**Read Data (SKID_DEPTH_R):**
- Default: 4 (deeper than AR for burst data)
- Increase if:
  - Large burst sizes (ARLEN > 4)
  - High-bandwidth streaming reads
  - Variable backend read latency

### Recommended Configurations

**Low-Latency Memory (single outstanding read):**
```systemverilog
axi4_slave_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(2)
) u_slave_rd ( ... );
```

**High-Throughput Streaming (burst reads):**
```systemverilog
axi4_slave_rd #(
    .SKID_DEPTH_AR(4),
    .SKID_DEPTH_R(16)    // Deep for burst data
) u_slave_rd ( ... );
```

**Variable Latency Backend:**
```systemverilog
axi4_slave_rd #(
    .SKID_DEPTH_AR(8),
    .SKID_DEPTH_R(16)
) u_slave_rd ( ... );
```

---

## Usage Example

### Basic Integration with Memory

```systemverilog
// Instantiate AXI4 slave read buffer
axi4_slave_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .AXI_USER_WIDTH(1)
) u_axi_slave_rd (
    .aclk               (axi_aclk),
    .aresetn            (axi_aresetn),

    // Slave interface (from AXI interconnect)
    .s_axi_arid         (s_axi_arid),
    .s_axi_araddr       (s_axi_araddr),
    .s_axi_arlen        (s_axi_arlen),
    .s_axi_arsize       (s_axi_arsize),
    .s_axi_arburst      (s_axi_arburst),
    .s_axi_arlock       (s_axi_arlock),
    .s_axi_arcache      (s_axi_arcache),
    .s_axi_arprot       (s_axi_arprot),
    .s_axi_arqos        (s_axi_arqos),
    .s_axi_arregion     (s_axi_arregion),
    .s_axi_aruser       (s_axi_aruser),
    .s_axi_arvalid      (s_axi_arvalid),
    .s_axi_arready      (s_axi_arready),

    .s_axi_rid          (s_axi_rid),
    .s_axi_rdata        (s_axi_rdata),
    .s_axi_rresp        (s_axi_rresp),
    .s_axi_rlast        (s_axi_rlast),
    .s_axi_ruser        (s_axi_ruser),
    .s_axi_rvalid       (s_axi_rvalid),
    .s_axi_rready       (s_axi_rready),

    // Backend interface (to memory controller)
    .fub_axi_arid       (mem_arid),
    .fub_axi_araddr     (mem_araddr),
    .fub_axi_arlen      (mem_arlen),
    .fub_axi_arsize     (mem_arsize),
    .fub_axi_arburst    (mem_arburst),
    .fub_axi_arlock     (mem_arlock),
    .fub_axi_arcache    (mem_arcache),
    .fub_axi_arprot     (mem_arprot),
    .fub_axi_arqos      (mem_arqos),
    .fub_axi_arregion   (mem_arregion),
    .fub_axi_aruser     (mem_aruser),
    .fub_axi_arvalid    (mem_arvalid),
    .fub_axi_arready    (mem_arready),

    .fub_axi_rid        (mem_rid),
    .fub_axi_rdata      (mem_rdata),
    .fub_axi_rresp      (mem_rresp),
    .fub_axi_rlast      (mem_rlast),
    .fub_axi_ruser      (mem_ruser),
    .fub_axi_rvalid     (mem_rvalid),
    .fub_axi_rready     (mem_rready),

    // Status
    .busy               (rd_slave_busy)
);

// Memory controller backend
memory_controller u_mem_ctrl (
    .axi_aclk       (axi_aclk),
    .axi_aresetn    (axi_aresetn),
    // Connect to fub_axi_* signals
    .axi_arid       (mem_arid),
    .axi_araddr     (mem_araddr),
    // ... rest of signals
);
```

### Clock Gating Example

```systemverilog
// Use busy signal for clock gating
logic axi_clk_gated;

clock_gate_ctrl u_cg (
    .i_clk          (axi_clk),
    .i_enable       (rd_slave_busy),
    .o_clk_gated    (axi_clk_gated)
);

// Connect module to gated clock
axi4_slave_rd #( ... ) u_slave_rd (
    .aclk (axi_clk_gated),
    ...
);
```

---

## Design Notes

### Buffer Independence

The two skid buffers operate independently:
- AR channel can accept new addresses while R channel returns data
- Burst reads can pipeline - next burst starts before previous completes
- Backend can have variable read latency without stalling interconnect

### Packet Preservation

All signal groups packed and unpacked atomically:
- AR channel: `{arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser}`
- R channel: `{rid, rdata, rresp, rlast, ruser}`

### Backpressure Handling

Ready signals propagate backpressure:
- Interconnect sees `arready` low when AR buffer full
- Backend sees `rready` low when R buffer full
- Prevents data loss while decoupling timing

### ID and Burst Handling

This module is a pass-through buffer:
- Does NOT track transaction IDs
- Does NOT enforce burst ordering
- Relies on backend to:
  - Match RID to ARID
  - Return correct number of beats (ARLEN+1)
  - Assert RLAST on final beat

### Reset Behavior

On `aresetn` assertion (active-low):
- All skid buffers flush
- Valid signals deasserted
- Busy signal goes low
- No data retained across reset

---

## Related Modules

### Companion Modules
- **axi4_slave_wr** - AXI4 slave write with buffering
- **axi4_slave_rd_cg** - Clock-gated variant with additional CG logic
- **axi4_slave_rd_mon** - Read transaction monitor for verification

### Used Components
- **[gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md)** - Elastic buffer with valid/ready handshake
- **[clock_gate_ctrl](../../RTLCommon/clock_gate_ctrl.md)** - Clock gating control (example)

### Related Infrastructure
- **[axi4_master_rd](axi4_master_rd.md)** - Corresponding AXI4 read master module
- **axi4_interconnect** - Multi-master/multi-slave crossbar

---

## References

### Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification (AXI4)

### Source Code
- RTL: `rtl/amba/axi4/axi4_slave_rd.sv`
- Tests: `val/amba/test_axi4_slave_rd.py`
- Framework: `bin/CocoTBFramework/components/axi4/`

### Documentation
- Architecture: [RTLAmba Overview](../overview.md)
- AXI4 Index: [axi4/README.md](README.md)
- GAXI Buffers: [gaxi/README.md](../gaxi/README.md)

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
