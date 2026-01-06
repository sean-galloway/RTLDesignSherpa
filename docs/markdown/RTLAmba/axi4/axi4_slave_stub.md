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

# AXI4 Slave Stub

**Module:** `axi4_slave_stub.sv`
**Location:** `rtl/amba/axi4/stubs/`
**Status:** Production Ready

---

## Overview

The AXI4 Slave Stub provides a simplified packed-data interface for receiving both AXI4 read and write transactions from a master. It combines the read and write slave stub functionalities into a single module, internally instantiating `axi4_slave_rd_stub` and `axi4_slave_wr_stub`. This provides a complete AXI4 slave interface with simplified packet-based control, ideal for testbenches and integration scenarios.

### Key Features

- Combined read and write channel support
- Packed packet interfaces for all channels (AW, W, B, AR, R)
- Configurable skid buffer depths per channel
- Full AXI4 protocol support (bursts, IDs, user signals)
- Simplified testbench integration
- Parameterized data widths

---

## Module Architecture

```mermaid
flowchart LR
    subgraph AXI4["AXI4 Slave Interface"]
        s_aw["AW Channel"]
        s_w["W Channel"]
        s_b["B Channel"]
        s_ar["AR Channel"]
        s_r["R Channel"]
    end

    subgraph STUB["AXI4 Slave Stub"]
        wr_stub["axi4_slave_wr_stub<br/>(Write Channels)"]
        rd_stub["axi4_slave_rd_stub<br/>(Read Channels)"]
    end

    subgraph PACKED["Packed Interfaces"]
        direction TB
        aw_pkt["AW Packet"]
        w_pkt["W Packet"]
        b_pkt["B Packet"]
        ar_pkt["AR Packet"]
        r_pkt["R Packet"]
    end

    s_aw --> wr_stub
    s_w --> wr_stub
    wr_stub --> s_b

    s_ar --> rd_stub
    rd_stub --> s_r

    wr_stub --> aw_pkt
    wr_stub --> w_pkt
    b_pkt --> wr_stub

    rd_stub --> ar_pkt
    r_pkt --> rd_stub
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AW | int | 2 | AW channel skid buffer depth (log2) |
| SKID_DEPTH_W | int | 4 | W channel skid buffer depth (log2) |
| SKID_DEPTH_B | int | 2 | B channel skid buffer depth (log2) |
| SKID_DEPTH_AR | int | 2 | AR channel skid buffer depth (log2) |
| SKID_DEPTH_R | int | 4 | R channel skid buffer depth (log2) |
| AXI_ID_WIDTH | int | 8 | AXI transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address bus width |
| AXI_DATA_WIDTH | int | 32 | AXI data bus width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| AXI_WSTRB_WIDTH | int | AXI_DATA_WIDTH/8 | Write strobe width |
| AW | int | AXI_ADDR_WIDTH | Short alias for address width |
| DW | int | AXI_DATA_WIDTH | Short alias for data width |
| IW | int | AXI_ID_WIDTH | Short alias for ID width |
| SW | int | AXI_WSTRB_WIDTH | Short alias for strobe width |
| UW | int | AXI_USER_WIDTH | Short alias for user width |
| AWSize | int | IW+AW+8+3+2+1+4+3+4+4+UW | AW packet size (calculated) |
| WSize | int | DW+SW+1+UW | W packet size (calculated) |
| BSize | int | IW+2+UW | B packet size (calculated) |
| ARSize | int | IW+AW+8+3+2+1+4+3+4+4+UW | AR packet size (calculated) |
| RSize | int | IW+DW+2+1+UW | R packet size (calculated) |

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock |
| aresetn | 1 | Input | AXI reset (active low) |

### AXI4 Write Channels

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axi_awid | AXI_ID_WIDTH | Input | Write address ID |
| s_axi_awaddr | AXI_ADDR_WIDTH | Input | Write address |
| s_axi_awlen | 8 | Input | Burst length |
| s_axi_awsize | 3 | Input | Burst size |
| s_axi_awburst | 2 | Input | Burst type |
| s_axi_awlock | 1 | Input | Lock type |
| s_axi_awcache | 4 | Input | Cache type |
| s_axi_awprot | 3 | Input | Protection type |
| s_axi_awqos | 4 | Input | Quality of service |
| s_axi_awregion | 4 | Input | Region identifier |
| s_axi_awuser | AXI_USER_WIDTH | Input | User signal |
| s_axi_awvalid | 1 | Input | Write address valid |
| s_axi_awready | 1 | Output | Write address ready |
| s_axi_wdata | AXI_DATA_WIDTH | Input | Write data |
| s_axi_wstrb | AXI_WSTRB_WIDTH | Input | Write strobes |
| s_axi_wlast | 1 | Input | Write last |
| s_axi_wuser | AXI_USER_WIDTH | Input | User signal |
| s_axi_wvalid | 1 | Input | Write data valid |
| s_axi_wready | 1 | Output | Write data ready |
| s_axi_bid | AXI_ID_WIDTH | Output | Response ID |
| s_axi_bresp | 2 | Output | Write response |
| s_axi_buser | AXI_USER_WIDTH | Output | User signal |
| s_axi_bvalid | 1 | Output | Write response valid |
| s_axi_bready | 1 | Input | Write response ready |

### AXI4 Read Channels

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axi_arid | AXI_ID_WIDTH | Input | Read address ID |
| s_axi_araddr | AXI_ADDR_WIDTH | Input | Read address |
| s_axi_arlen | 8 | Input | Burst length |
| s_axi_arsize | 3 | Input | Burst size |
| s_axi_arburst | 2 | Input | Burst type |
| s_axi_arlock | 1 | Input | Lock type |
| s_axi_arcache | 4 | Input | Cache type |
| s_axi_arprot | 3 | Input | Protection type |
| s_axi_arqos | 4 | Input | Quality of service |
| s_axi_arregion | 4 | Input | Region identifier |
| s_axi_aruser | AXI_USER_WIDTH | Input | User signal |
| s_axi_arvalid | 1 | Input | Read address valid |
| s_axi_arready | 1 | Output | Read address ready |
| s_axi_rid | AXI_ID_WIDTH | Output | Read data ID |
| s_axi_rdata | AXI_DATA_WIDTH | Output | Read data |
| s_axi_rresp | 2 | Output | Read response |
| s_axi_rlast | 1 | Output | Read last |
| s_axi_ruser | AXI_USER_WIDTH | Output | User signal |
| s_axi_rvalid | 1 | Output | Read data valid |
| s_axi_rready | 1 | Input | Read data ready |

### Write Packet Interfaces

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_awvalid | 1 | Output | AW packet valid |
| fub_axi_awready | 1 | Input | Ready to accept AW packet |
| fub_axi_aw_count | 4 | Output | AW buffer occupancy |
| fub_axi_aw_pkt | AWSize | Output | Packed AW packet data |
| fub_axi_wvalid | 1 | Output | W packet valid |
| fub_axi_wready | 1 | Input | Ready to accept W packet |
| fub_axi_w_pkt | WSize | Output | Packed W packet data |
| fub_axi_bvalid | 1 | Input | B packet valid |
| fub_axi_bready | 1 | Output | Ready to accept B packet |
| fub_axi_b_pkt | BSize | Input | Packed B packet data |

### Read Packet Interfaces

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_arvalid | 1 | Output | AR packet valid |
| fub_axi_arready | 1 | Input | Ready to accept AR packet |
| fub_axi_ar_count | 4 | Output | AR buffer occupancy |
| fub_axi_ar_pkt | ARSize | Output | Packed AR packet data |
| fub_axi_rvalid | 1 | Input | R packet valid |
| fub_axi_rready | 1 | Output | Ready to accept R packet |
| fub_axi_r_pkt | RSize | Input | Packed R packet data |

---

## Packet Formats

### Write Channel Packets

**AW Packet (Write Address):**
```
fub_axi_aw_pkt = {awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser}
Width = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW
```

**W Packet (Write Data):**
```
fub_axi_w_pkt = {wdata, wstrb, wlast, wuser}
Width = DW + SW + 1 + UW
```

**B Packet (Write Response):**
```
fub_axi_b_pkt = {bid, bresp, buser}
Width = IW + 2 + UW
```

### Read Channel Packets

**AR Packet (Read Address):**
```
fub_axi_ar_pkt = {arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser}
Width = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW
```

**R Packet (Read Data):**
```
fub_axi_r_pkt = {rid, rdata, rresp, rlast, ruser}
Width = IW + DW + 2 + 1 + UW
```

**Complete packet format details:** See [AXI4 Slave Write Stub](axi4_slave_wr_stub.md) and [AXI4 Slave Read Stub](axi4_slave_rd_stub.md)

---

## Transaction Flow

### Combined Read and Write Operations

```mermaid
sequenceDiagram
    participant MASTER as AXI4 Master
    participant BUS as AXI4 Bus
    participant STUB as AXI4 Slave Stub
    participant TB as Testbench

    Note over MASTER,TB: Write Transaction
    MASTER->>BUS: AW, W transactions
    BUS->>STUB: s_axi_awvalid, s_axi_wvalid
    STUB-->>TB: fub_axi_awvalid, fub_axi_aw_pkt
    STUB-->>TB: fub_axi_wvalid, fub_axi_w_pkt
    Note over TB: Process write
    TB->>STUB: fub_axi_bvalid, fub_axi_b_pkt
    STUB->>BUS: s_axi_bvalid
    BUS->>MASTER: B response

    Note over MASTER,TB: Read Transaction (can overlap)
    MASTER->>BUS: AR transaction
    BUS->>STUB: s_axi_arvalid
    STUB-->>TB: fub_axi_arvalid, fub_axi_ar_pkt
    Note over TB: Generate read data
    TB->>STUB: fub_axi_rvalid, fub_axi_r_pkt
    STUB->>BUS: s_axi_rvalid
    BUS->>MASTER: R data
```

### Timing

<!-- TODO: Add wavedrom timing diagram for combined stub -->
```
TODO: Wavedrom timing diagram showing:
- aclk
- AXI write channels (s_axi_aw*, s_axi_w*, s_axi_b*)
- Write packet interfaces (fub_axi_aw*, fub_axi_w*, fub_axi_b*)
- AXI read channels (s_axi_ar*, s_axi_r*)
- Read packet interfaces (fub_axi_ar*, fub_axi_r*)
- Overlapping read/write operations
```

---

## Usage Example

```systemverilog
axi4_slave_stub #(
    .SKID_DEPTH_AW   (2),
    .SKID_DEPTH_W    (4),
    .SKID_DEPTH_B    (2),
    .SKID_DEPTH_AR   (2),
    .SKID_DEPTH_R    (4),
    .AXI_ID_WIDTH    (8),
    .AXI_ADDR_WIDTH  (32),
    .AXI_DATA_WIDTH  (64),
    .AXI_USER_WIDTH  (4)
) u_axi4_slave_stub (
    .aclk            (axi_clk),
    .aresetn         (axi_rst_n),

    // AXI4 slave interface (all channels)
    .s_axi_awid      (s_axi_awid),
    .s_axi_awaddr    (s_axi_awaddr),
    .s_axi_awlen     (s_axi_awlen),
    .s_axi_awsize    (s_axi_awsize),
    .s_axi_awburst   (s_axi_awburst),
    .s_axi_awlock    (s_axi_awlock),
    .s_axi_awcache   (s_axi_awcache),
    .s_axi_awprot    (s_axi_awprot),
    .s_axi_awqos     (s_axi_awqos),
    .s_axi_awregion  (s_axi_awregion),
    .s_axi_awuser    (s_axi_awuser),
    .s_axi_awvalid   (s_axi_awvalid),
    .s_axi_awready   (s_axi_awready),

    .s_axi_wdata     (s_axi_wdata),
    .s_axi_wstrb     (s_axi_wstrb),
    .s_axi_wlast     (s_axi_wlast),
    .s_axi_wuser     (s_axi_wuser),
    .s_axi_wvalid    (s_axi_wvalid),
    .s_axi_wready    (s_axi_wready),

    .s_axi_bid       (s_axi_bid),
    .s_axi_bresp     (s_axi_bresp),
    .s_axi_buser     (s_axi_buser),
    .s_axi_bvalid    (s_axi_bvalid),
    .s_axi_bready    (s_axi_bready),

    .s_axi_arid      (s_axi_arid),
    .s_axi_araddr    (s_axi_araddr),
    .s_axi_arlen     (s_axi_arlen),
    .s_axi_arsize    (s_axi_arsize),
    .s_axi_arburst   (s_axi_arburst),
    .s_axi_arlock    (s_axi_arlock),
    .s_axi_arcache   (s_axi_arcache),
    .s_axi_arprot    (s_axi_arprot),
    .s_axi_arqos     (s_axi_arqos),
    .s_axi_arregion  (s_axi_arregion),
    .s_axi_aruser    (s_axi_aruser),
    .s_axi_arvalid   (s_axi_arvalid),
    .s_axi_arready   (s_axi_arready),

    .s_axi_rid       (s_axi_rid),
    .s_axi_rdata     (s_axi_rdata),
    .s_axi_rresp     (s_axi_rresp),
    .s_axi_rlast     (s_axi_rlast),
    .s_axi_ruser     (s_axi_ruser),
    .s_axi_rvalid    (s_axi_rvalid),
    .s_axi_rready    (s_axi_rready),

    // Write packet interfaces
    .fub_axi_awvalid (tb_aw_valid),
    .fub_axi_awready (tb_aw_ready),
    .fub_axi_aw_count(tb_aw_count),
    .fub_axi_aw_pkt  (tb_aw_pkt),

    .fub_axi_wvalid  (tb_w_valid),
    .fub_axi_wready  (tb_w_ready),
    .fub_axi_w_pkt   (tb_w_pkt),

    .fub_axi_bvalid  (tb_b_valid),
    .fub_axi_bready  (tb_b_ready),
    .fub_axi_b_pkt   (tb_b_pkt),

    // Read packet interfaces
    .fub_axi_arvalid (tb_ar_valid),
    .fub_axi_arready (tb_ar_ready),
    .fub_axi_ar_count(tb_ar_count),
    .fub_axi_ar_pkt  (tb_ar_pkt),

    .fub_axi_rvalid  (tb_r_valid),
    .fub_axi_rready  (tb_r_ready),
    .fub_axi_r_pkt   (tb_r_pkt)
);

// Parse incoming write address
wire [7:0]  aw_id     = tb_aw_pkt[AWSize-1:AWSize-8];
wire [31:0] aw_addr   = tb_aw_pkt[AWSize-9:AWSize-40];
wire [7:0]  aw_len    = tb_aw_pkt[AWSize-41:AWSize-48];
// ... additional fields

// Parse incoming write data
wire [63:0] w_data = tb_w_pkt[WSize-1:WSize-64];
wire [7:0]  w_strb = tb_w_pkt[WSize-65:WSize-72];
wire        w_last = tb_w_pkt[WSize-73];

// Generate write response (OKAY)
assign tb_b_pkt = {
    aw_id,    // bid (match request ID)
    2'b00,    // bresp (OKAY)
    4'h0      // buser
};

// Parse incoming read address
wire [7:0]  ar_id   = tb_ar_pkt[ARSize-1:ARSize-8];
wire [31:0] ar_addr = tb_ar_pkt[ARSize-9:ARSize-40];
wire [7:0]  ar_len  = tb_ar_pkt[ARSize-41:ARSize-48];
// ... additional fields

// Generate read data response
reg [63:0] read_data;  // From memory model
assign tb_r_pkt = {
    ar_id,      // rid (match request ID)
    read_data,  // rdata
    2'b00,      // rresp (OKAY)
    1'b1,       // rlast (single beat example)
    4'h0        // ruser
};
```

---

## Design Notes

### Internal Architecture

The stub instantiates two sub-modules:
- **`axi4_slave_wr_stub`** - Handles AW, W, and B channels
- **`axi4_slave_rd_stub`** - Handles AR and R channels

This hierarchical design:
- Reuses proven read/write stub modules
- Maintains clear channel separation
- Simplifies verification and testing
- Allows independent read/write operation

### Read/Write Independence

Read and write channels are completely independent:
- Can overlap in time (simultaneous read and write)
- Each has independent skid buffers
- No ordering constraints between reads and writes
- Testbench can respond at different rates

### Skid Buffer Depths

**Recommended configurations:**

**Low latency (fast response):**
```systemverilog
.SKID_DEPTH_AW(2), .SKID_DEPTH_W(2), .SKID_DEPTH_B(2),
.SKID_DEPTH_AR(2), .SKID_DEPTH_R(2)
```

**Typical system:**
```systemverilog
.SKID_DEPTH_AW(2), .SKID_DEPTH_W(4), .SKID_DEPTH_B(2),
.SKID_DEPTH_AR(2), .SKID_DEPTH_R(4)
```

**High throughput bursts:**
```systemverilog
.SKID_DEPTH_AW(4), .SKID_DEPTH_W(8), .SKID_DEPTH_B(4),
.SKID_DEPTH_AR(4), .SKID_DEPTH_R(8)
```

### Memory Model Integration

The slave stub is ideal for connecting to memory models:

```systemverilog
// Simple memory model
reg [63:0] memory [0:1023];

// Handle write requests
always @(posedge aclk) begin
    if (tb_aw_valid && tb_aw_ready) begin
        // Capture write address
    end
    if (tb_w_valid && tb_w_ready) begin
        // Write data to memory
        memory[write_addr] <= w_data;
    end
end

// Handle read requests
always @(posedge aclk) begin
    if (tb_ar_valid && tb_ar_ready) begin
        // Generate read data from memory
        read_data <= memory[ar_addr];
    end
end
```

---

## Related Documentation

- **[AXI4 Slave Read Stub](axi4_slave_rd_stub.md)** - Read-only stub (instantiated internally)
- **[AXI4 Slave Write Stub](axi4_slave_wr_stub.md)** - Write-only stub (instantiated internally)
- **[AXI4 Master Stub](axi4_master_stub.md)** - Corresponding combined master stub
- **[AXI4 Slave Read](axi4_slave_rd.md)** - Full AXI4 slave read module
- **[AXI4 Slave Write](axi4_slave_wr.md)** - Full AXI4 slave write module

---

## Navigation

- **[<- Back to AXI4 Index](README.md)**
- **[<- Back to RTLAmba Index](../index.md)**
- **[<- Back to Main Documentation Index](../../index.md)**
