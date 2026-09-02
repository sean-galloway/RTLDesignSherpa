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

# AXI4 Slave Write

**Module:** `axi4_slave_wr.sv`
**Location:** `rtl/amba/axi4/`
**Status:** Production Ready

---

## Overview

The AXI4 Slave Write module is a buffered AXI4 slave write interface with configurable-depth skid buffers on all three write channels (AW, W, B). Think of it as an elastic buffer sitting between the AXI4 interconnect and your memory or backend processing element: it decouples the timing on the two sides and absorbs backpressure, so a sluggish backend doesn't stall the interconnect and an eager master doesn't overrun the backend.

### Key Features

- **Full AXI4 Write Support:** Complete AW, W, and B channel implementation
- **Independent Channel Buffering:** Separate configurable depth buffers for each channel
- **Elastic Buffering:** Decouples interconnect and backend timing domains
- **Burst Support:** Full burst transaction handling with WLAST tracking
- **User Signal Support:** Carries AWUSER, WUSER, and BUSER signals
- **Clock Gating Support:** Busy signal for dynamic power management

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `SKID_DEPTH_AW` | int | 2 | Depth of write address (AW) channel skid buffer |
| `SKID_DEPTH_W` | int | 4 | Depth of write data (W) channel skid buffer |
| `SKID_DEPTH_B` | int | 2 | Depth of write response (B) channel skid buffer |
| `AXI_ID_WIDTH` | int | 8 | Width of transaction ID signals (AWID, BID) |
| `AXI_ADDR_WIDTH` | int | 32 | Width of address bus (AWADDR) |
| `AXI_DATA_WIDTH` | int | 32 | Width of data bus (WDATA), must be 8, 16, 32, 64, 128, 256, 512, or 1024 |
| `AXI_WSTRB_WIDTH` | int | AXI_DATA_WIDTH/8 | Write strobe width |
| `AXI_USER_WIDTH` | int | 1 | Width of user-defined signals (AWUSER, WUSER, BUSER) |

---

## Ports

Here's the full module declaration -- the tables below it break the ports down by group.

```systemverilog
module axi4_slave_wr #(
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    // Derived shorthands -- override the eight above, not these
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+SW+1+UW,
    parameter int BSize    = IW+2+UW
) (
    // Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI Interface (s_axi_*)
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]   s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [SW-1:0]               s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]   s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0] s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    // Backend Interface (fub_axi_* - to memory/backend)
    // Write address channel (AW)
    output logic [AXI_ID_WIDTH-1:0]   fub_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0] fub_axi_awaddr,
    output logic [7:0]                 fub_axi_awlen,
    output logic [2:0]                 fub_axi_awsize,
    output logic [1:0]                 fub_axi_awburst,
    output logic                       fub_axi_awlock,
    output logic [3:0]                 fub_axi_awcache,
    output logic [2:0]                 fub_axi_awprot,
    output logic [3:0]                 fub_axi_awqos,
    output logic [3:0]                 fub_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0] fub_axi_awuser,
    output logic                       fub_axi_awvalid,
    input  logic                       fub_axi_awready,

    // Write data channel (W)
    output logic [AXI_DATA_WIDTH-1:0] fub_axi_wdata,
    output logic [SW-1:0]               fub_axi_wstrb,
    output logic                       fub_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0] fub_axi_wuser,
    output logic                       fub_axi_wvalid,
    input  logic                       fub_axi_wready,

    // Write response channel (B)
    input  logic [AXI_ID_WIDTH-1:0]   fub_axi_bid,
    input  logic [1:0]                 fub_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0] fub_axi_buser,
    input  logic                       fub_axi_bvalid,
    output logic                       fub_axi_bready,

    // Status
    output logic                       busy
);
```

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `aclk` | Input | 1 | AXI clock - all signals sampled on rising edge |
| `aresetn` | Input | 1 | Active-low asynchronous reset |

### Slave AXI Interface (s_axi_*)

#### Write Address Channel (AW)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_awid` | Input | `AXI_ID_WIDTH` | Write transaction ID |
| `s_axi_awaddr` | Input | `AXI_ADDR_WIDTH` | Write address |
| `s_axi_awlen` | Input | 8 | Burst length, AXI-encoded: beats - 1 (`0x00` = 1 beat, `0xFF` = 256) |
| `s_axi_awsize` | Input | 3 | Burst size (bytes per beat) |
| `s_axi_awburst` | Input | 2 | Burst type (FIXED, INCR, WRAP) |
| `s_axi_awlock` | Input | 1 | Lock type (atomic access support) |
| `s_axi_awcache` | Input | 4 | Cache attributes |
| `s_axi_awprot` | Input | 3 | Protection attributes |
| `s_axi_awqos` | Input | 4 | Quality of Service identifier |
| `s_axi_awregion` | Input | 4 | Region identifier |
| `s_axi_awuser` | Input | `AXI_USER_WIDTH` | User-defined signal |
| `s_axi_awvalid` | Input | 1 | Write address valid |
| `s_axi_awready` | Output | 1 | Write address ready |

#### Write Data Channel (W)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_wdata` | Input | `AXI_DATA_WIDTH` | Write data |
| `s_axi_wstrb` | Input | `AXI_DATA_WIDTH/8` | Write strobes (byte enables) |
| `s_axi_wlast` | Input | 1 | Last beat of burst indicator |
| `s_axi_wuser` | Input | `AXI_USER_WIDTH` | User-defined signal |
| `s_axi_wvalid` | Input | 1 | Write data valid |
| `s_axi_wready` | Output | 1 | Write data ready |

#### Write Response Channel (B)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axi_bid` | Output | `AXI_ID_WIDTH` | Response transaction ID |
| `s_axi_bresp` | Output | 2 | Write response (OKAY, EXOKAY, SLVERR, DECERR) |
| `s_axi_buser` | Output | `AXI_USER_WIDTH` | User-defined signal |
| `s_axi_bvalid` | Output | 1 | Write response valid |
| `s_axi_bready` | Input | 1 | Write response ready |

### Backend Interface (fub_axi_*)

Mirrors the slave interface but in the opposite direction (output on AW/W, input on B).

### Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Indicates active transactions in buffers (for clock gating) |

---

## Functional Description

### Architecture

Three independent `gaxi_skid_buffer` instances do the heavy lifting, one per write channel:

```mermaid
flowchart LR
    subgraph SL["Slave<br/>(s_axi_*)"]
        saw["aw*"]
        sw["w*"]
        sb["b*"]
    end

    subgraph BUF["Skid Buffers"]
        awb["AW Buffer<br/>(depth=2)"]
        wb["W Buffer<br/>(depth=4)"]
        bb["B Buffer<br/>(depth=2)"]
    end

    subgraph BE["Backend<br/>(fub_axi_*)"]
        baw["aw*"]
        bw["w*"]
        bb2["b*"]
    end

    saw --> awb --> baw
    sw --> wb --> bw
    bb2 --> bb --> sb
```

### Channel Operations

#### Write Address (AW) Channel
1. Master presents write address and attributes via interconnect
2. AW skid buffer accepts when space available (`s_axi_awready` high)
3. Buffered address presented to backend when ready
4. Configurable depth (`SKID_DEPTH_AW`) smooths timing variations

#### Write Data (W) Channel
1. Master presents write data with strobes via interconnect
2. W skid buffer provides deeper buffering (default depth=4)
3. WLAST signal preserved to indicate burst boundaries
4. Independent from AW channel (AXI4 allows W before AW)

#### Write Response (B) Channel
1. Backend returns write response with transaction ID
2. B skid buffer captures response when master busy
3. Master receives response via interconnect when ready to accept
4. ID matching handled by AXI interconnect (not this module)

### Busy Signal

The `busy` output indicates active transactions:
```systemverilog
assign busy = (int_aw_count > 0) || (int_w_count > 0) || (int_b_count > 0) ||
                s_axi_awvalid || s_axi_wvalid || fub_axi_bvalid;
```

Use cases:
- **Clock gating:** Disable clock when `busy` is low
- **Power management:** Enter low-power mode when idle
- **Synchronization:** Wait for idle before configuration changes

---

## Timing Characteristics

| Skid parameter | Default depth |
|---|---|
| `SKID_DEPTH_AW` | 2 entries |
| `SKID_DEPTH_W` | 4 entries |
| `SKID_DEPTH_B` | 2 entries |

Each channel traverses one `gaxi_skid_buffer`, which registers both `rd_valid`
and its storage. The **1-cycle input-to-output latency therefore applies on
every transfer, including the unstalled case** -- there is no combinational
bypass. Depth buys backpressure absorption, not throughput; full rate is
sustained once the pipeline is primed. Legal range is 2..8 inclusive, odd
values included.

Clocking: `aclk`, reset `aresetn` (active-low asynchronous).

No synthesis numbers are quoted here. Frequency and area depend on the target
device and the parameters you elaborate with; run your own build.

---

## Usage Examples


Every parameter and port below is read from the module declaration.

```systemverilog
axi4_slave_wr #(
    .SKID_DEPTH_AW         (2),
    .SKID_DEPTH_W          (4),
    .SKID_DEPTH_B          (2),
    .AXI_ID_WIDTH          (8),
    .AXI_ADDR_WIDTH        (32),
    .AXI_DATA_WIDTH        (32),
    .AXI_USER_WIDTH        (1)
) u_axi4_slave_wr (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .s_axi_awid            (s_axi_awid),
    .s_axi_awaddr          (s_axi_awaddr),
    .s_axi_awlen           (s_axi_awlen),
    .s_axi_awsize          (s_axi_awsize),
    .s_axi_awburst         (s_axi_awburst),
    .s_axi_awlock          (s_axi_awlock),
    .s_axi_awcache         (s_axi_awcache),
    .s_axi_awprot          (s_axi_awprot),
    .s_axi_awqos           (s_axi_awqos),
    .s_axi_awregion        (s_axi_awregion),
    .s_axi_awuser          (s_axi_awuser),
    .s_axi_awvalid         (s_axi_awvalid),
    .s_axi_awready         (s_axi_awready),
    .s_axi_wdata           (s_axi_wdata),
    .s_axi_wstrb           (s_axi_wstrb),
    .s_axi_wlast           (s_axi_wlast),
    .s_axi_wuser           (s_axi_wuser),
    .s_axi_wvalid          (s_axi_wvalid),
    .s_axi_wready          (s_axi_wready),
    .s_axi_bid             (s_axi_bid),
    .s_axi_bresp           (s_axi_bresp),
    .s_axi_buser           (s_axi_buser),
    .s_axi_bvalid          (s_axi_bvalid),
    .s_axi_bready          (s_axi_bready),
    .fub_axi_awid          (fub_axi_awid),
    .fub_axi_awaddr        (fub_axi_awaddr),
    .fub_axi_awlen         (fub_axi_awlen),
    .fub_axi_awsize        (fub_axi_awsize),
    .fub_axi_awburst       (fub_axi_awburst),
    .fub_axi_awlock        (fub_axi_awlock),
    .fub_axi_awcache       (fub_axi_awcache),
    .fub_axi_awprot        (fub_axi_awprot),
    .fub_axi_awqos         (fub_axi_awqos),
    .fub_axi_awregion      (fub_axi_awregion),
    .fub_axi_awuser        (fub_axi_awuser),
    .fub_axi_awvalid       (fub_axi_awvalid),
    .fub_axi_awready       (fub_axi_awready),
    .fub_axi_wdata         (fub_axi_wdata),
    .fub_axi_wstrb         (fub_axi_wstrb),
    .fub_axi_wlast         (fub_axi_wlast),
    .fub_axi_wuser         (fub_axi_wuser),
    .fub_axi_wvalid        (fub_axi_wvalid),
    .fub_axi_wready        (fub_axi_wready),
    .fub_axi_bid           (fub_axi_bid),
    .fub_axi_bresp         (fub_axi_bresp),
    .fub_axi_buser         (fub_axi_buser),
    .fub_axi_bvalid        (fub_axi_bvalid),
    .fub_axi_bready        (fub_axi_bready),
    .busy                  (busy)
);
```

## Design Notes

### Buffer Depth Selection

`SKID_DEPTH_*` is an entry count, not a log2 exponent. The underlying
`gaxi_skid_buffer` allocates one register slot per entry and tracks occupancy
with a 4-bit counter, so legal values are 2..8 inclusive (any integer). Values greater than 8
overflow the occupancy counter and are not supported.

**Write Address (SKID_DEPTH_AW):**
- Default: 2 (sufficient for most cases)
- Increase if:
  - High-latency backend address decode
  - Frequent address channel backpressure
  - Multiple outstanding bursts needed

**Write Data (SKID_DEPTH_W):**
- Default: 4 (deeper than AW for burst data)
- Increase if:
  - Large burst sizes (AWLEN > 4)
  - High-bandwidth streaming writes
  - Variable backend write latency

**Write Response (SKID_DEPTH_B):**
- Default: 2 (responses are typically single-beat)
- Increase if:
  - Master slow to accept responses
  - Many concurrent outstanding writes
  - Response channel backpressure observed

### Recommended Configurations

**Low-Latency Memory (single outstanding write):**
```systemverilog
axi4_slave_wr #(
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(2),
    .SKID_DEPTH_B(2)
) u_slave_wr ( ... );
```

**High-Throughput Streaming (burst writes):**
```systemverilog
axi4_slave_wr #(
    .SKID_DEPTH_AW(4),
    .SKID_DEPTH_W(8),    // Deep for burst data
    .SKID_DEPTH_B(4)
) u_slave_wr ( ... );
```

**Multiple Outstanding Writes:**
```systemverilog
axi4_slave_wr #(
    .SKID_DEPTH_AW(8),
    .SKID_DEPTH_W(8),
    .SKID_DEPTH_B(8)
) u_slave_wr ( ... );
```

### Buffer Independence

The three skid buffers operate independently:
- AW and W channels can progress at different rates
- AXI4 allows W data before AW address
- B responses return asynchronously based on backend timing

### Packet Preservation

All signal groups packed and unpacked atomically:
- AW channel: `{awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser}`
- W channel: `{wdata, wstrb, wlast, wuser}`
- B channel: `{bid, bresp, buser}`

### Backpressure Handling

Ready signals propagate backpressure:
- Interconnect sees `awready/wready` low when buffers full
- Backend backpressure captured in buffers
- Prevents data loss while decoupling timing

### ID and Burst Handling

This module is a pass-through buffer, and it's honest about it:
- Does NOT track transaction IDs
- Does NOT enforce burst ordering
- Relies on backend to:
  - Match BID to AWID
  - Generate appropriate BRESP

### Reset Behavior

On `aresetn` assertion (active-low):
- All skid buffers flush
- Valid signals deasserted
- Busy signal goes low
- No data retained across reset

---

## Related Modules

### Companion Modules
- **[axi4_slave_rd](axi4_slave_rd.md)** - AXI4 slave read with buffering
- **axi4_slave_wr_cg** - Clock-gated variant with additional CG logic
- **axi4_slave_wr_mon** - Write transaction monitor for verification

### Used Components
- **[gaxi_skid_buffer](../gaxi/gaxi_skid_buffer.md)** - Elastic buffer with valid/ready handshake
- **[clock_gate_ctrl](../../rtl-common/clock_gate_ctrl.md)** - Clock gating control (example)

### Related Infrastructure
- **[axi4_master_wr](axi4_master_wr.md)** - Corresponding AXI4 write master module
- **axi4_interconnect** - Multi-master/multi-slave crossbar

---

## Testing

The unit testbench lives at `val/amba/test_axi4_slave_wr.py`, built on the shared AXI4 test framework in `bin/TBClasses/components/axi4/`.

---

## References

### Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification (AXI4)

### Source Code
- RTL: `rtl/amba/axi4/axi4_slave_wr.sv`

### Documentation
- Architecture: [rtl-amba Overview](../overview.md)
- AXI4 Index: [axi4/README.md](README.md)
- GAXI Buffers: [gaxi/README.md](../gaxi/README.md)

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[<- Back to AXI4 Index](README.md)**
- **[<- Back to rtl-amba Index](../index.md)**
- **[<- Back to Main Documentation Index](../../index.md)**
