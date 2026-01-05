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

# 3.3 AXI4-Lite to AXI4 Converter

The **axil4_to_axi4** converter family upgrades AXI4-Lite single-beat transactions to full AXI4 protocol by adding default burst signals.

## 3.3.1 Module Organization

```
axil4_to_axi4.sv          # Full bidirectional wrapper
├── axil4_to_axi4_rd.sv   # Read path converter
└── axil4_to_axi4_wr.sv   # Write path converter
```

## 3.3.2 Design Philosophy

**Zero-Overhead Upgrade:**
- Purely combinational logic
- No state machines or buffers
- Adds default values for missing AXI4 signals

**Why This Works:**
- AXI4-Lite is a subset of AXI4
- All AXI4-Lite transactions are single-beat
- Missing AXI4 signals have well-defined defaults

## 3.3.3 Signal Mapping

### Address Channel Signals

| AXI4-Lite Signal | AXI4 Signal | Default/Mapping |
|------------------|-------------|-----------------|
| ARADDR | ARADDR | Passthrough |
| ARPROT | ARPROT | Passthrough |
| ARVALID | ARVALID | Passthrough |
| ARREADY | ARREADY | Passthrough |
| - | ARLEN | 8'h00 (single beat) |
| - | ARSIZE | $clog2(DATA_WIDTH/8) |
| - | ARBURST | 2'b01 (INCR) |
| - | ARLOCK | 1'b0 (normal) |
| - | ARCACHE | 4'b0000 (non-cacheable) |
| - | ARQOS | 4'b0000 (no QoS) |
| - | ARID | Configurable default |

: Table 3.10: AR Channel Mapping

### Data Channel Signals

| AXI4-Lite Signal | AXI4 Signal | Default/Mapping |
|------------------|-------------|-----------------|
| RDATA | RDATA | Passthrough |
| RRESP | RRESP | Passthrough |
| RVALID | RVALID | Passthrough |
| RREADY | RREADY | Passthrough |
| - | RLAST | 1'b1 (always last) |
| - | RID | Matches ARID |

: Table 3.11: R Channel Mapping

## 3.3.4 Read Path (axil4_to_axi4_rd)

### Block Diagram

### Figure 3.4: AXI4-Lite to AXI4 Read Path

![AXIL4 to AXI4 Read](../assets/mermaid/axil4_to_axi4_rd.png)

### Implementation

```systemverilog
module axil4_to_axi4_rd #(
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter logic [ID_WIDTH-1:0] DEFAULT_ARID = '0
) (
    // AXI4-Lite slave interface (input)
    input  logic                    s_arvalid,
    output logic                    s_arready,
    input  logic [ADDR_WIDTH-1:0]   s_araddr,
    input  logic [2:0]              s_arprot,

    output logic                    s_rvalid,
    input  logic                    s_rready,
    output logic [DATA_WIDTH-1:0]   s_rdata,
    output logic [1:0]              s_rresp,

    // AXI4 master interface (output)
    output logic                    m_arvalid,
    input  logic                    m_arready,
    output logic [ADDR_WIDTH-1:0]   m_araddr,
    output logic [7:0]              m_arlen,
    output logic [2:0]              m_arsize,
    output logic [1:0]              m_arburst,
    output logic                    m_arlock,
    output logic [3:0]              m_arcache,
    output logic [2:0]              m_arprot,
    output logic [3:0]              m_arqos,
    output logic [ID_WIDTH-1:0]     m_arid,

    input  logic                    m_rvalid,
    output logic                    m_rready,
    input  logic [DATA_WIDTH-1:0]   m_rdata,
    input  logic [1:0]              m_rresp,
    input  logic                    m_rlast,
    input  logic [ID_WIDTH-1:0]     m_rid
);

    // AR channel - passthrough with defaults
    assign m_arvalid = s_arvalid;
    assign s_arready = m_arready;
    assign m_araddr  = s_araddr;
    assign m_arprot  = s_arprot;

    // AXI4 burst defaults
    assign m_arlen   = 8'h00;                    // Single beat
    assign m_arsize  = $clog2(DATA_WIDTH/8);     // Full width
    assign m_arburst = 2'b01;                    // INCR
    assign m_arlock  = 1'b0;                     // Normal access
    assign m_arcache = 4'b0000;                  // Non-cacheable
    assign m_arqos   = 4'b0000;                  // No QoS
    assign m_arid    = DEFAULT_ARID;             // Configurable ID

    // R channel - passthrough (ignore RLAST and RID)
    assign s_rvalid  = m_rvalid;
    assign m_rready  = s_rready;
    assign s_rdata   = m_rdata;
    assign s_rresp   = m_rresp;

endmodule
```

**Key Points:**
- No registers - purely combinational
- RLAST from AXI4 is ignored (always 1 for AXIL4)
- RID from AXI4 is ignored (no ID tracking in AXIL4)

## 3.3.5 Write Path (axil4_to_axi4_wr)

### Block Diagram

### Figure 3.5: AXI4-Lite to AXI4 Write Path

![AXIL4 to AXI4 Write](../assets/mermaid/axil4_to_axi4_wr.png)

### Implementation

```systemverilog
module axil4_to_axi4_wr #(
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter logic [ID_WIDTH-1:0] DEFAULT_AWID = '0
) (
    // AXI4-Lite slave interface (input)
    input  logic                    s_awvalid,
    output logic                    s_awready,
    input  logic [ADDR_WIDTH-1:0]   s_awaddr,
    input  logic [2:0]              s_awprot,

    input  logic                    s_wvalid,
    output logic                    s_wready,
    input  logic [DATA_WIDTH-1:0]   s_wdata,
    input  logic [DATA_WIDTH/8-1:0] s_wstrb,

    output logic                    s_bvalid,
    input  logic                    s_bready,
    output logic [1:0]              s_bresp,

    // AXI4 master interface (output)
    output logic                    m_awvalid,
    input  logic                    m_awready,
    output logic [ADDR_WIDTH-1:0]   m_awaddr,
    output logic [7:0]              m_awlen,
    output logic [2:0]              m_awsize,
    output logic [1:0]              m_awburst,
    output logic                    m_awlock,
    output logic [3:0]              m_awcache,
    output logic [2:0]              m_awprot,
    output logic [3:0]              m_awqos,
    output logic [ID_WIDTH-1:0]     m_awid,

    output logic                    m_wvalid,
    input  logic                    m_wready,
    output logic [DATA_WIDTH-1:0]   m_wdata,
    output logic [DATA_WIDTH/8-1:0] m_wstrb,
    output logic                    m_wlast,

    input  logic                    m_bvalid,
    output logic                    m_bready,
    input  logic [1:0]              m_bresp,
    input  logic [ID_WIDTH-1:0]     m_bid
);

    // AW channel
    assign m_awvalid = s_awvalid;
    assign s_awready = m_awready;
    assign m_awaddr  = s_awaddr;
    assign m_awprot  = s_awprot;
    assign m_awlen   = 8'h00;
    assign m_awsize  = $clog2(DATA_WIDTH/8);
    assign m_awburst = 2'b01;
    assign m_awlock  = 1'b0;
    assign m_awcache = 4'b0000;
    assign m_awqos   = 4'b0000;
    assign m_awid    = DEFAULT_AWID;

    // W channel
    assign m_wvalid  = s_wvalid;
    assign s_wready  = m_wready;
    assign m_wdata   = s_wdata;
    assign m_wstrb   = s_wstrb;
    assign m_wlast   = 1'b1;  // Always last (single beat)

    // B channel
    assign s_bvalid  = m_bvalid;
    assign m_bready  = s_bready;
    assign s_bresp   = m_bresp;

endmodule
```

## 3.3.6 Bidirectional Wrapper

```systemverilog
module axil4_to_axi4 #(
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter logic [ID_WIDTH-1:0] DEFAULT_ID = '0
) (
    // ... all port declarations
);

    axil4_to_axi4_rd #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .DEFAULT_ARID(DEFAULT_ID)
    ) u_rd (/* connections */);

    axil4_to_axi4_wr #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .DEFAULT_AWID(DEFAULT_ID)
    ) u_wr (/* connections */);

endmodule
```

## 3.3.7 Resource Utilization

| Module | Registers | LUTs |
|--------|-----------|------|
| axil4_to_axi4_rd | 0 | ~50 |
| axil4_to_axi4_wr | 0 | ~60 |
| axil4_to_axi4 (combined) | 0 | ~110 |

: Table 3.12: AXIL4 to AXI4 Resources

**Note:** Zero registers - purely combinational logic.

## 3.3.8 Performance

| Metric | Value |
|--------|-------|
| Latency | 0 cycles |
| Throughput | 100% |
| Max frequency | Wire speed |

: Table 3.13: AXIL4 to AXI4 Performance

## 3.3.9 Test Coverage

**Test Suite:** 14 tests passing

| Test Category | Tests | Status |
|---------------|-------|--------|
| Single-beat read | 3 | Pass |
| Single-beat write | 3 | Pass |
| Mixed traffic | 4 | Pass |
| Default ID verification | 2 | Pass |
| Edge cases | 2 | Pass |

: Table 3.14: Test Coverage Summary

## 3.3.10 Usage Example

```systemverilog
// Upgrade simple register block to AXI4 fabric
axil4_to_axi4 #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(32),
    .ID_WIDTH(4),
    .DEFAULT_ID(4'h5)  // Unique ID for this IP
) u_protocol_upgrade (
    // Connect AXIL4 register block
    .s_arvalid (reg_block_arvalid),
    .s_arready (reg_block_arready),
    .s_araddr  (reg_block_araddr),
    // ... other AXIL4 signals

    // Connect to AXI4 crossbar
    .m_arvalid (xbar_arvalid),
    .m_arready (xbar_arready),
    .m_araddr  (xbar_araddr),
    .m_arlen   (xbar_arlen),
    // ... other AXI4 signals
);
```

---

**Next:** [AXI4 to APB](04_axi4_to_apb.md)
