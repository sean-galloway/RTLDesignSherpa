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

# AXI4 Slave Read Stub

**Module:** `axi4_slave_rd_stub.sv`
**Location:** `rtl/amba/axi4/stubs/`
**Status:** Production Ready

---

## Overview

The other end of the read transaction. The AXI4 Slave Read Stub receives AXI4 read transactions from a master and exposes them as simple packet interfaces — the AR channel arrives as one packed payload for your testbench to chew on, and you hand read data back the same way. Skid buffers do the pack/unpack work, which makes the stub ideal for testbenches and integration scenarios where a simplified slave interface is what you actually need.

### Key Features

- Packed packet interface for AR and R channels
- Configurable skid buffer depth on each channel
- Full AXI4 read transaction support
- Burst, ID, and user signal support
- Parameterized data widths

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AR | int | 2 | AR channel skid buffer depth in entries (2..8 inclusive, any integer) |
| SKID_DEPTH_R | int | 4 | R channel skid buffer depth in entries (2..8 inclusive, any integer) |
| AXI_ID_WIDTH | int | 8 | AXI transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address bus width |
| AXI_DATA_WIDTH | int | 32 | AXI data bus width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| AXI_WSTRB_WIDTH | int | AXI_DATA_WIDTH/8 | Write strobe width (unused) |
| AW | int | AXI_ADDR_WIDTH | Short alias for address width |
| DW | int | AXI_DATA_WIDTH | Short alias for data width |
| IW | int | AXI_ID_WIDTH | Short alias for ID width |
| SW | int | AXI_WSTRB_WIDTH | Short alias for strobe width |
| UW | int | AXI_USER_WIDTH | Short alias for user width |
| ARSize | int | IW+AW+8+3+2+1+4+3+4+4+UW | AR packet size (calculated) |
| RSize | int | IW+DW+2+1+UW | R packet size (calculated) |

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| aclk | Input | 1 | AXI clock |
| aresetn | Input | 1 | AXI reset (active low) |

### AXI4 Read Address Channel (AR)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_arid | Input | IW | Read address ID |
| s_axi_araddr | Input | AW | Read address |
| s_axi_arlen | Input | 8 | Burst length |
| s_axi_arsize | Input | 3 | Burst size |
| s_axi_arburst | Input | 2 | Burst type |
| s_axi_arlock | Input | 1 | Lock type |
| s_axi_arcache | Input | 4 | Cache type |
| s_axi_arprot | Input | 3 | Protection type |
| s_axi_arqos | Input | 4 | Quality of service |
| s_axi_arregion | Input | 4 | Region identifier |
| s_axi_aruser | Input | UW | User signal |
| s_axi_arvalid | Input | 1 | Read address valid |
| s_axi_arready | Output | 1 | Read address ready |

### AXI4 Read Data Channel (R)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| s_axi_rid | Output | IW | Read data ID |
| s_axi_rdata | Output | DW | Read data |
| s_axi_rresp | Output | 2 | Read response |
| s_axi_rlast | Output | 1 | Read last |
| s_axi_ruser | Output | UW | User signal |
| s_axi_rvalid | Output | 1 | Read data valid |
| s_axi_rready | Input | 1 | Read data ready |

### AR Packet Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_axi_arvalid | Output | 1 | AR packet valid |
| fub_axi_arready | Input | 1 | Ready to accept AR packet |
| fub_axi_ar_count | Output | 4 | AR buffer occupancy |
| fub_axi_ar_pkt | Output | ARSize | Packed AR packet data |

### R Packet Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| fub_axi_rvalid | Input | 1 | R packet valid |
| fub_axi_rready | Output | 1 | Ready to accept R packet |
| fub_axi_r_pkt | Input | RSize | Packed R packet data |

---

## Functional Description

### Architecture

```mermaid
flowchart LR
    subgraph AXI4["AXI4 Interface"]
        s_ar["AXI4<br/>AR Channel"]
        s_r["AXI4<br/>R Channel"]
    end

    subgraph STUB["AXI4 Slave Read Stub"]
        ar_skid["AR Skid<br/>Buffer"]
        r_skid["R Skid<br/>Buffer"]
    end

    subgraph PACKED["Packed Interface"]
        ar_pkt["AR Packet<br/>(Address Request)"]
        r_pkt["R Packet<br/>(Read Data)"]
    end

    s_ar --> ar_skid
    ar_skid --> ar_pkt

    r_pkt --> r_skid
    r_skid --> s_r
```

### Packet Formats

Packets are packed MSB-to-LSB in AXI signal order, so parsing one in the testbench is plain slicing.

#### AR Packet Structure (Read Address)

```mermaid
flowchart LR
    subgraph AR["AR Packet (MSB to LSB)"]
        arid["arid<br/>(IW)"]
        araddr["araddr<br/>(AW)"]
        arlen["arlen<br/>(8b)"]
        arsize["arsize<br/>(3b)"]
        arburst["arburst<br/>(2b)"]
        arlock["arlock<br/>(1b)"]
        arcache["arcache<br/>(4b)"]
        arprot["arprot<br/>(3b)"]
        arqos["arqos<br/>(4b)"]
        arregion["arregion<br/>(4b)"]
        aruser["aruser<br/>(UW)"]
    end
```

**Bit Positions:**
```
fub_axi_ar_pkt = {arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser}

Width = IW + AW + 8 + 3 + 2 + 1 + 4 + 3 + 4 + 4 + UW
```

#### R Packet Structure (Read Data)

```mermaid
flowchart LR
    subgraph R["R Packet (MSB to LSB)"]
        rid["rid<br/>(IW)"]
        rdata["rdata<br/>(DW)"]
        rresp["rresp<br/>(2b)"]
        rlast["rlast<br/>(1b)"]
        ruser["ruser<br/>(UW)"]
    end
```

**Bit Positions:**
```
fub_axi_r_pkt = {rid, rdata, rresp, rlast, ruser}

Width = IW + DW + 2 + 1 + UW
```

### Transaction Flow

```mermaid
sequenceDiagram
    participant MASTER as AXI4 Master
    participant BUS as AXI4 Bus
    participant STUB as AXI4 Slave Read Stub
    participant TB as Testbench

    MASTER->>BUS: AR transaction
    BUS->>STUB: s_axi_arvalid, AR signals
    Note over STUB: Pack AR data via skid buffer
    STUB-->>TB: fub_axi_arvalid, fub_axi_ar_pkt
    TB->>STUB: Process address

    Note over TB: Generate read data

    TB->>STUB: fub_axi_rvalid, fub_axi_r_pkt
    Note over STUB: Unpack R packet via skid buffer
    STUB->>BUS: s_axi_rvalid, R signals
    BUS->>MASTER: R channel data
```

---

## Timing Characteristics
<!-- TODO: Add wavedrom timing diagram for stub transactions -->
> **Timing diagram pending.** The signals and sequence this scenario
> exercises:
>
> - aclk
> - AXI AR signals (s_axi_arvalid, s_axi_araddr, s_axi_arlen, etc.)
> - fub_axi_arvalid, fub_axi_arready, fub_axi_ar_pkt
> - fub_axi_rvalid, fub_axi_rready, fub_axi_r_pkt
> - AXI R signals (s_axi_rvalid, s_axi_rdata, s_axi_rlast, etc.)
> - Packet-to-AXI timing relationship with skid buffer operation

---

## Usage Examples
```systemverilog
axi4_slave_rd_stub #(
    .SKID_DEPTH_AR   (2),
    .SKID_DEPTH_R    (4),
    .AXI_ID_WIDTH    (8),
    .AXI_ADDR_WIDTH  (32),
    .AXI_DATA_WIDTH  (64),
    .AXI_USER_WIDTH  (4)
) u_axi4_slave_rd_stub (
    .aclk            (axi_clk),
    .aresetn         (axi_rst_n),

    // AXI4 slave read interface
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

    // Packed AR interface
    .fub_axi_arvalid (tb_ar_valid),
    .fub_axi_arready (tb_ar_ready),
    .fub_axi_ar_count(tb_ar_count),
    .fub_axi_ar_pkt  (tb_ar_pkt),

    // Packed R interface
    .fub_axi_rvalid  (tb_r_valid),
    .fub_axi_rready  (tb_r_ready),
    .fub_axi_r_pkt   (tb_r_pkt)
);

// Parse AR packet
localparam int ARSize = 8+32+8+3+2+1+4+3+4+4+4;  // match your instance widths
wire [7:0]  ar_id     = tb_ar_pkt[ARSize-1:ARSize-8];
wire [31:0] ar_addr   = tb_ar_pkt[ARSize-9:ARSize-40];
wire [7:0]  ar_len    = tb_ar_pkt[ARSize-41:ARSize-48];
wire [2:0]  ar_size   = tb_ar_pkt[ARSize-49:ARSize-51];
wire [1:0]  ar_burst  = tb_ar_pkt[ARSize-52:ARSize-53];
// ... additional fields as needed

// Build R packet (single beat response with data 0xDEADBEEFCAFEBABE)
localparam RSize = 8 + 64 + 2 + 1 + 4;  // Calculate size
assign tb_r_pkt = {
    ar_id,                      // rid (match request ID)
    64'hDEAD_BEEF_CAFE_BABE,   // rdata
    2'b00,                      // rresp (OKAY)
    1'b1,                       // rlast
    4'h0                        // ruser
};
```

---

## Design Notes

### Skid Buffer Operation

The stub is two `gaxi_skid_buffer` instances, and they earn their keep. They:

- Decouple timing between AXI bus and testbench
- Provide configurable buffering depth per channel
- Handle backpressure gracefully
- Support burst transactions without stalling

**Recommended Depths:**
- **AR Channel:** 2-4 (address transactions)
- **R Channel:** 4-8 (data beats for bursts)

### Packet Packing Order

AR and R packets are packed MSB-to-LSB following AXI signal order:
- Simplifies testbench packet parsing
- Matches common concatenation order
- Efficient for burst transaction handling

### Internal Architecture

The stub instantiates two `gaxi_skid_buffer` modules:
- **AR Skid Buffer:** Packs AXI AR channel to AR packets
- **R Skid Buffer:** Unpacks R packets to AXI R channel

All AXI protocol handling is done by the skid buffers and upstream modules.

---

## Related Modules

- **[AXI4 Slave Read](axi4_slave_rd.md)** - Full AXI4 slave read module (if wrapping one)
- **[AXI4 Slave Write Stub](axi4_slave_wr_stub.md)** - Corresponding write stub
- **[AXI4 Slave Stub](axi4_slave_stub.md)** - Combined read/write stub
- **[AXI4 Master Read Stub](axi4_master_rd_stub.md)** - Master-side read stub

---

## Testing

**No dedicated testbench, and none is expected.** This is a stub: a tie-off
shell that presents the interface and drives inert values, so there is no
behaviour to verify beyond elaboration. `make verilator` lints it as its own
top on every run, which is the coverage that applies.

Treat any behaviour described on this page as unverified by simulation.

---

## Navigation

- **[← Back to AXI4 Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
