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

# AXI4 Interface Overview

## Interface Organization

### Master-Side Interfaces

Bridge presents **slave interfaces** to upstream masters. Each master port includes:

| Channel | Signals | Direction (to Bridge) |
|---------|---------|----------------------|
| AW | AWVALID, AWREADY, AWADDR, AWID, AWLEN, AWSIZE, AWBURST, ... | Input |
| W | WVALID, WREADY, WDATA, WSTRB, WLAST | Input |
| B | BVALID, BREADY, BID, BRESP | Output |
| AR | ARVALID, ARREADY, ARADDR, ARID, ARLEN, ARSIZE, ARBURST, ... | Input |
| R | RVALID, RREADY, RDATA, RID, RRESP, RLAST | Output |

: Table 4.9: Master-Side Interface Channels

### Slave-Side Interfaces

Bridge presents **master interfaces** to downstream slaves. Each slave port includes:

| Channel | Signals | Direction (from Bridge) |
|---------|---------|------------------------|
| AW | AWVALID, AWREADY, AWADDR, AWID, AWLEN, AWSIZE, AWBURST, ... | Output |
| W | WVALID, WREADY, WDATA, WSTRB, WLAST | Output |
| B | BVALID, BREADY, BID, BRESP | Input |
| AR | ARVALID, ARREADY, ARADDR, ARID, ARLEN, ARSIZE, ARBURST, ... | Output |
| R | RVALID, RREADY, RDATA, RID, RRESP, RLAST | Input |

: Table 4.10: Slave-Side Interface Channels

## Signal Naming Convention

### Custom Prefixes

Each port uses a custom prefix for signal naming:

```systemverilog
// Example: Master 0 with prefix "cpu_m_axi_"
input  logic [31:0] cpu_m_axi_awaddr,
input  logic [3:0]  cpu_m_axi_awid,
input  logic        cpu_m_axi_awvalid,
output logic        cpu_m_axi_awready,
// ... remaining AW signals

// Example: Slave 0 with prefix "ddr_s_axi_"
output logic [31:0] ddr_s_axi_awaddr,
output logic [7:0]  ddr_s_axi_awid,  // Extended ID
output logic        ddr_s_axi_awvalid,
input  logic        ddr_s_axi_awready,
```

### ID Width Extension

Slave-side IDs are wider than master-side:

```
Master ID Width: ID_WIDTH (configuration parameter)
Bridge ID Width: clog2(NUM_MASTERS)
Slave ID Width: ID_WIDTH + clog2(NUM_MASTERS)
```

## Channel-Specific Interfaces

### Write-Only Master (wr)

Only AW, W, B channels generated:

```systemverilog
// Write Address Channel
input  logic [ADDR_WIDTH-1:0] descr_m_axi_awaddr,
input  logic [ID_WIDTH-1:0]   descr_m_axi_awid,
// ... full AW channel

// Write Data Channel
input  logic [DATA_WIDTH-1:0] descr_m_axi_wdata,
input  logic [STRB_WIDTH-1:0] descr_m_axi_wstrb,
// ... full W channel

// Write Response Channel
output logic [ID_WIDTH-1:0]   descr_m_axi_bid,
output logic [1:0]            descr_m_axi_bresp,
// ... full B channel

// NO AR or R channels
```

### Read-Only Master (rd)

Only AR, R channels generated:

```systemverilog
// Read Address Channel
input  logic [ADDR_WIDTH-1:0] src_m_axi_araddr,
input  logic [ID_WIDTH-1:0]   src_m_axi_arid,
// ... full AR channel

// Read Data Channel
output logic [DATA_WIDTH-1:0] src_m_axi_rdata,
output logic [ID_WIDTH-1:0]   src_m_axi_rid,
// ... full R channel

// NO AW, W, or B channels
```

## Handshake Protocol

### Valid/Ready Handshake

All channels use AXI4 valid/ready handshake:

```
Transfer occurs when: VALID && READY
```

### Backpressure

- Bridge asserts READY when able to accept
- Masters must hold VALID until READY
- Bridge does not drop transactions

## Burst Support

### Supported Burst Types

| AWBURST/ARBURST | Type | Description |
|-----------------|------|-------------|
| 2'b00 | FIXED | Same address each beat |
| 2'b01 | INCR | Incrementing address |
| 2'b10 | WRAP | Wrapping at boundary |
| 2'b11 | Reserved | Not used |

: Table 4.11: Supported Burst Types

### Burst Length

- AWLEN/ARLEN: 8-bit field
- Length = AXLEN + 1 (1 to 256 beats)
- Burst does not cross 4KB boundary (AXI4 rule)
