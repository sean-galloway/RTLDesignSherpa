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

# AXI4 Master Write Stub

**Module:** `axi4_master_wr_stub.sv`
**Location:** `rtl/amba/axi4/stubs/`
**Status:** Production Ready

---

## Overview

The AXI4 Master Write Stub provides a simplified packed-data interface for driving AXI4 write transactions. It uses skid buffers to pack/unpack AXI4 AW (write address), W (write data), and B (write response) channels into simple packet interfaces, making it ideal for testbenches and integration scenarios where a simplified interface is preferred.

### Key Features

- Packed packet interface for AW, W, and B channels
- Configurable skid buffer depths for each channel
- Full AXI4 write transaction support
- Burst, ID, strobe, user signal support
- Parameterized data widths

---

## Module Architecture

```mermaid
flowchart LR
    subgraph PACKED["Packed Interface"]
        aw_pkt["AW Packet<br/>(Address)"]
        w_pkt["W Packet<br/>(Data)"]
        b_pkt["B Packet<br/>(Response)"]
    end

    subgraph STUB["AXI4 Master Write Stub"]
        aw_skid["AW Skid<br/>Buffer"]
        w_skid["W Skid<br/>Buffer"]
        b_skid["B Skid<br/>Buffer"]
    end

    subgraph AXI4["AXI4 Interface"]
        m_aw["AXI4<br/>AW Channel"]
        m_w["AXI4<br/>W Channel"]
        m_b["AXI4<br/>B Channel"]
    end

    aw_pkt --> aw_skid
    aw_skid --> m_aw

    w_pkt --> w_skid
    w_skid --> m_w

    m_b --> b_skid
    b_skid --> b_pkt
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AW | int | 2 | AW channel skid buffer depth (log2) |
| SKID_DEPTH_W | int | 4 | W channel skid buffer depth (log2) |
| SKID_DEPTH_B | int | 2 | B channel skid buffer depth (log2) |
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

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock |
| aresetn | 1 | Input | AXI reset (active low) |

### AXI4 Write Address Channel (AW)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_awid | IW | Output | Write address ID |
| m_axi_awaddr | AW | Output | Write address |
| m_axi_awlen | 8 | Output | Burst length |
| m_axi_awsize | 3 | Output | Burst size |
| m_axi_awburst | 2 | Output | Burst type |
| m_axi_awlock | 1 | Output | Lock type |
| m_axi_awcache | 4 | Output | Cache type |
| m_axi_awprot | 3 | Output | Protection type |
| m_axi_awqos | 4 | Output | Quality of service |
| m_axi_awregion | 4 | Output | Region identifier |
| m_axi_awuser | UW | Output | User signal |
| m_axi_awvalid | 1 | Output | Write address valid |
| m_axi_awready | 1 | Input | Write address ready |

### AXI4 Write Data Channel (W)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_wdata | DW | Output | Write data |
| m_axi_wstrb | SW | Output | Write strobes |
| m_axi_wlast | 1 | Output | Write last |
| m_axi_wuser | UW | Output | User signal |
| m_axi_wvalid | 1 | Output | Write data valid |
| m_axi_wready | 1 | Input | Write data ready |

### AXI4 Write Response Channel (B)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axi_bid | IW | Input | Response ID |
| m_axi_bresp | 2 | Input | Write response |
| m_axi_buser | UW | Input | User signal |
| m_axi_bvalid | 1 | Input | Write response valid |
| m_axi_bready | 1 | Output | Write response ready |

### AW Packet Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_awvalid | 1 | Input | AW packet valid |
| fub_axi_awready | 1 | Output | Ready to accept AW packet |
| fub_axi_aw_count | 4 | Output | AW buffer occupancy |
| fub_axi_aw_pkt | AWSize | Input | Packed AW packet data |

### W Packet Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_wvalid | 1 | Input | W packet valid |
| fub_axi_wready | 1 | Output | Ready to accept W packet |
| fub_axi_w_pkt | WSize | Input | Packed W packet data |

### B Packet Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_bvalid | 1 | Output | B packet valid |
| fub_axi_bready | 1 | Input | Ready to accept B packet |
| fub_axi_b_pkt | BSize | Output | Packed B packet data |

---

## Packet Formats

### AW Packet Structure (Write Address)

```mermaid
flowchart LR
    subgraph AW["AW Packet (MSB to LSB)"]
        awid["awid<br/>(IW)"]
        awaddr["awaddr<br/>(AW)"]
        awlen["awlen<br/>(8b)"]
        awsize["awsize<br/>(3b)"]
        awburst["awburst<br/>(2b)"]
        awlock["awlock<br/>(1b)"]
        awcache["awcache<br/>(4b)"]
        awprot["awprot<br/>(3b)"]
        awqos["awqos<br/>(4b)"]
        awregion["awregion<br/>(4b)"]
        awuser["awuser<br/>(UW)"]
    end
```

**Bit Positions:**
```
fub_axi_aw_pkt = {awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser}

Width = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW
```

### W Packet Structure (Write Data)

```mermaid
flowchart LR
    subgraph W["W Packet (MSB to LSB)"]
        wdata["wdata<br/>(DW)"]
        wstrb["wstrb<br/>(SW)"]
        wlast["wlast<br/>(1b)"]
        wuser["wuser<br/>(UW)"]
    end
```

**Bit Positions:**
```
fub_axi_w_pkt = {wdata, wstrb, wlast, wuser}

Width = DW + SW + 1 + UW
```

### B Packet Structure (Write Response)

```mermaid
flowchart LR
    subgraph B["B Packet (MSB to LSB)"]
        bid["bid<br/>(IW)"]
        bresp["bresp<br/>(2b)"]
        buser["buser<br/>(UW)"]
    end
```

**Bit Positions:**
```
fub_axi_b_pkt = {bid, bresp, buser}

Width = IW + 2 + UW
```

---

## Transaction Flow

### Write Transaction

```mermaid
sequenceDiagram
    participant TB as Testbench
    participant STUB as AXI4 Master Write Stub
    participant BUS as AXI4 Bus
    participant SLAVE as AXI4 Slave

    TB->>STUB: fub_axi_awvalid, fub_axi_aw_pkt
    TB->>STUB: fub_axi_wvalid, fub_axi_w_pkt
    Note over STUB: Unpack AW and W packets via skid buffers
    STUB->>BUS: m_axi_awvalid, AW signals
    STUB->>BUS: m_axi_wvalid, W signals
    BUS->>SLAVE: AW and W transactions
    SLAVE-->>BUS: m_axi_awready, m_axi_wready

    Note over SLAVE: Process write data

    SLAVE->>BUS: m_axi_bvalid, B signals
    BUS->>STUB: B channel response
    Note over STUB: Pack B response via skid buffer
    STUB-->>TB: fub_axi_bvalid, fub_axi_b_pkt
```

### Timing

<!-- TODO: Add wavedrom timing diagram for stub transactions -->
```
TODO: Wavedrom timing diagram showing:
- aclk
- fub_axi_awvalid, fub_axi_awready, fub_axi_aw_pkt
- fub_axi_wvalid, fub_axi_wready, fub_axi_w_pkt
- AXI AW signals (m_axi_awvalid, m_axi_awaddr, m_axi_awlen, etc.)
- AXI W signals (m_axi_wvalid, m_axi_wdata, m_axi_wstrb, m_axi_wlast, etc.)
- AXI B signals (m_axi_bvalid, m_axi_bid, m_axi_bresp, etc.)
- fub_axi_bvalid, fub_axi_bready, fub_axi_b_pkt
- Packet-to-AXI timing relationship with skid buffer operation
```

---

## Usage Example

```systemverilog
axi4_master_wr_stub #(
    .SKID_DEPTH_AW   (2),
    .SKID_DEPTH_W    (4),
    .SKID_DEPTH_B    (2),
    .AXI_ID_WIDTH    (8),
    .AXI_ADDR_WIDTH  (32),
    .AXI_DATA_WIDTH  (64),
    .AXI_USER_WIDTH  (4)
) u_axi4_master_wr_stub (
    .aclk            (axi_clk),
    .aresetn         (axi_rst_n),

    // AXI4 master write interface
    .m_axi_awid      (m_axi_awid),
    .m_axi_awaddr    (m_axi_awaddr),
    .m_axi_awlen     (m_axi_awlen),
    .m_axi_awsize    (m_axi_awsize),
    .m_axi_awburst   (m_axi_awburst),
    .m_axi_awlock    (m_axi_awlock),
    .m_axi_awcache   (m_axi_awcache),
    .m_axi_awprot    (m_axi_awprot),
    .m_axi_awqos     (m_axi_awqos),
    .m_axi_awregion  (m_axi_awregion),
    .m_axi_awuser    (m_axi_awuser),
    .m_axi_awvalid   (m_axi_awvalid),
    .m_axi_awready   (m_axi_awready),

    .m_axi_wdata     (m_axi_wdata),
    .m_axi_wstrb     (m_axi_wstrb),
    .m_axi_wlast     (m_axi_wlast),
    .m_axi_wuser     (m_axi_wuser),
    .m_axi_wvalid    (m_axi_wvalid),
    .m_axi_wready    (m_axi_wready),

    .m_axi_bid       (m_axi_bid),
    .m_axi_bresp     (m_axi_bresp),
    .m_axi_buser     (m_axi_buser),
    .m_axi_bvalid    (m_axi_bvalid),
    .m_axi_bready    (m_axi_bready),

    // Packed AW interface
    .fub_axi_awvalid (tb_aw_valid),
    .fub_axi_awready (tb_aw_ready),
    .fub_axi_aw_count(tb_aw_count),
    .fub_axi_aw_pkt  (tb_aw_pkt),

    // Packed W interface
    .fub_axi_wvalid  (tb_w_valid),
    .fub_axi_wready  (tb_w_ready),
    .fub_axi_w_pkt   (tb_w_pkt),

    // Packed B interface
    .fub_axi_bvalid  (tb_b_valid),
    .fub_axi_bready  (tb_b_ready),
    .fub_axi_b_pkt   (tb_b_pkt)
);

// Build AW packet (single beat write at address 0x1000)
localparam AWSize = 8 + 32 + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + 4;  // Calculate size
assign tb_aw_pkt = {
    8'd0,           // awid
    32'h0000_1000,  // awaddr
    8'd0,           // awlen (1 beat)
    3'b011,         // awsize (8 bytes)
    2'b01,          // awburst (INCR)
    1'b0,           // awlock
    4'b0011,        // awcache
    3'b000,         // awprot
    4'b0000,        // awqos
    4'b0000,        // awregion
    4'h0            // awuser
};

// Build W packet
localparam WSize = 64 + 8 + 1 + 4;  // Calculate size
assign tb_w_pkt = {
    64'hDEAD_BEEF_CAFE_BABE,  // wdata
    8'hFF,                     // wstrb (all bytes)
    1'b1,                      // wlast
    4'h0                       // wuser
};

// Parse B packet
wire [7:0] b_id   = tb_b_pkt[BSize-1:BSize-8];
wire [1:0] b_resp = tb_b_pkt[5:4];
wire [3:0] b_user = tb_b_pkt[3:0];
```

---

## Design Notes

### Skid Buffer Operation

The stub uses `gaxi_skid_buffer` modules to:
- Decouple timing between testbench and AXI bus
- Provide configurable buffering depth per channel
- Handle backpressure gracefully
- Support burst transactions without stalling

**Recommended Depths:**
- **AW Channel:** 2-4 (address transactions)
- **W Channel:** 4-8 (data beats for bursts)
- **B Channel:** 2-4 (responses)

### Channel Independence

The AW, W, and B channels are independent:
- AW and W can be driven in any order
- Stub handles proper AXI timing
- B responses arrive asynchronously

### Packet Packing Order

AW, W, and B packets are packed MSB-to-LSB following AXI signal order:
- Simplifies testbench packet creation
- Matches common concatenation order
- Efficient for burst transaction handling

### Internal Architecture

The stub instantiates three `gaxi_skid_buffer` modules:
- **AW Skid Buffer:** Unpacks AW packets to AXI AW channel
- **W Skid Buffer:** Unpacks W packets to AXI W channel
- **B Skid Buffer:** Packs AXI B channel to B packets

All AXI protocol handling is done by the skid buffers and downstream modules.

---

## Related Documentation

- **[AXI4 Master Write](axi4_master_wr.md)** - Full AXI4 master write module (if wrapping one)
- **[AXI4 Master Read Stub](axi4_master_rd_stub.md)** - Corresponding read stub
- **[AXI4 Master Stub](axi4_master_stub.md)** - Combined read/write stub
- **[AXI4 Slave Write Stub](axi4_slave_wr_stub.md)** - Slave-side write stub

---

## Navigation

- **[<- Back to AXI4 Index](README.md)**
- **[<- Back to RTLAmba Index](../index.md)**
- **[<- Back to Main Documentation Index](../../index.md)**
