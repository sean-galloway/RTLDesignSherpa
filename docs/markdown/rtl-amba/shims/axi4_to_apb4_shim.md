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

# axi4_to_apb4_shim

**Module:** `axi4_to_apb4_shim.sv`
**Location:** `projects/components/converters/rtl/`
**Status:** Production (see the module page history for review state)

---

## Overview

The top-level bridge: AXI4 memory-mapped transactions in, APB peripheral bus accesses out, with full dual-clock domain crossing (CDC) support in between. This shim stitches together the AXI slave stub, the converter core, two async FIFOs, and the APB master stub so you don't have to — drop it between your AXI interconnect and your APB bus and it does the whole job.

### Key Features

- **Full AXI4 to APB Bridge:** Complete protocol conversion with burst decomposition
- **Dual-Clock Support:** Independent AXI (aclk) and APB (pclk) clock domains
- **CDC-Safe Handshakes:** Asynchronous clock domain crossing with proper synchronization
- **Configurable Buffering:** Skid buffers on all AXI channels for timing closure
- **Width Adaptation:** Automatic data width conversion (AXI → APB)
- **Burst Decomposition:** AXI bursts → APB single-beat transfers
- **Error Propagation:** APB PSLVERR mapped to AXI RRESP/BRESP

---

## Parameters

### Skid Buffer Depths

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| DEPTH_AW | int | 2 | AW channel skid buffer depth (2..8 inclusive (any integer) -- gaxi_skid_buffer elaboration guard) |
| DEPTH_W | int | 4 | W channel skid buffer depth |
| DEPTH_B | int | 2 | B channel skid buffer depth |
| DEPTH_AR | int | 2 | AR channel skid buffer depth |
| DEPTH_R | int | 4 | R channel skid buffer depth |

**Recommendation:** Use deeper depths (4-8) for high-latency paths, shallow (2) for low-latency. All five DEPTH_* parameters must be 2..8 inclusive (any integer): gaxi_skid_buffer rejects anything else at elaboration.

### Internal Buffering

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SIDE_DEPTH | int | 4 | Side information FIFO depth (tracks ID, last, user) |
| APB_CMD_DEPTH | int | 4 | APB command CDC FIFO depth. Legal values with the default Gray encoding: {2, 3, 4, 8} -- the value feeds BOTH the apb4_master skid buffers (2..8 inclusive guard) and, floored to `max(DEPTH,4)`, the Gray CDC FIFO (power-of-2 guard; 2 and 3 floor to 4), so 5/6/7 elaborate only with USE_JOHNSON=1 |
| APB_RSP_DEPTH | int | 4 | APB response CDC FIFO depth. Same constraint set as APB_CMD_DEPTH |
| USE_JOHNSON | int | 0 | Pointer encoding for the two CDC FIFOs: 0 = Gray (requires power-of-2 depths -- elaboration $error otherwise), 1 = Johnson (any depth) |

### AXI Interface

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| AXI_ID_WIDTH | int | 8 | Transaction ID width (1-16) |
| AXI_ADDR_WIDTH | int | 32 | Address width (12-64) |
| AXI_DATA_WIDTH | int | 32 | Data width (32, 64, 128, 256, 512) |
| AXI_USER_WIDTH | int | 1 | User sideband signal width |

### APB Interface

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| APB_ADDR_WIDTH | int | 32 | APB address width (must match AXI) |
| APB_DATA_WIDTH | int | 32 | APB data width (8, 16, 32, 64) |

**Note:** APB_DATA_WIDTH must be ≤ AXI_DATA_WIDTH. Width adaptation is automatic.

---

## Ports

The full interface — all five AXI4 channels on the slave side, a classic APB3 master on the other:

```systemverilog
module axi4_to_apb4_shim #(
    // Skid buffer depths (AXI side)
    parameter int DEPTH_AW          = 2,   // AW channel depth
    parameter int DEPTH_W           = 4,   // W channel depth
    parameter int DEPTH_B           = 2,   // B channel depth
    parameter int DEPTH_AR          = 2,   // AR channel depth
    parameter int DEPTH_R           = 4,   // R channel depth

    // Internal buffering
    parameter int SIDE_DEPTH        = 4,   // Side info FIFO depth
    parameter int APB_CMD_DEPTH     = 4,   // APB command FIFO depth
    parameter int APB_RSP_DEPTH     = 4,   // APB response FIFO depth

    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // APB parameters
    parameter int APB_ADDR_WIDTH    = 32,
    parameter int APB_DATA_WIDTH    = 32
) (
    // Clock and Reset
    input  logic                          aclk,      // AXI clock domain
    input  logic                          aresetn,   // AXI reset (active-low)
    input  logic                          pclk,      // APB clock domain
    input  logic                          presetn,   // APB reset (active-low)

    // AXI4 Slave Interface (all 5 channels)
    // Write address channel (AW)
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0]   s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    // Read address channel (AR)
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // APB Master Interface
    output logic                          m_apb_PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     m_apb_PADDR,
    output logic                          m_apb_PENABLE,
    output logic                          m_apb_PWRITE,
    output logic [APB_DATA_WIDTH-1:0]     m_apb_PWDATA,
    output logic [APB_DATA_WIDTH/8-1:0]   m_apb_PSTRB,
    output logic [2:0]                    m_apb_PPROT,

    input  logic [APB_DATA_WIDTH-1:0]     m_apb_PRDATA,
    input  logic                          m_apb_PREADY,
    input  logic                          m_apb_PSLVERR
);
```

---

## Functional Description

### Architecture

```
axi4_to_apb4_shim (this module)
├── axi4_slave_stub
│   └── Provides AXI slave interface with skid buffers
│
├── axi4_to_apb4_convert
│   ├── Core conversion logic
│   ├── Burst decomposition
│   ├── Width adaptation
│   └── gaxi_fifo_sync (side info)
│
├── gaxi_fifo_async (command, aclk → pclk)
│   └── gray/Johnson-pointer async FIFO CDC
│
├── gaxi_fifo_async (response, pclk → aclk)
│   └── gray/Johnson-pointer async FIFO CDC
│
└── apb4_master_stub
    └── Provides APB master interface with buffering
```

### Data Flow

**Write Transaction:**
```
AXI Master → AW/W skid buffers (aclk)
          → axi4_to_apb4_convert (burst decomposition, aclk)
          → cmd CDC handshake (aclk → pclk)
          → apb4_master_stub (APB protocol, pclk)
          → APB Slave (pclk)
          → rsp CDC handshake (pclk → aclk)
          → B channel response (aclk)
```

**Read Transaction:**
```
AXI Master → AR skid buffer (aclk)
          → axi4_to_apb4_convert (burst decomposition, aclk)
          → cmd CDC handshake (aclk → pclk)
          → apb4_master_stub (APB protocol, pclk)
          → APB Slave (pclk)
          → rsp CDC handshake (pclk → aclk)
          → R channel response + data (aclk)
```

### AXI to APB Conversion

**Burst Decomposition:**
- AXI burst (AWLEN > 0) → Multiple APB single-beat transfers
- Each beat addressed individually (address increments per burst type)
- Burst completion is counted from AWLEN (`r_burst_count`); WLAST is carried but never sampled -- a malformed W stream with wrong WLAST placement is not detected

That last point is worth repeating: if your master misplaces WLAST, this bridge won't catch it. Verify your masters.

**Width Adaptation:**
- When `AXI_DATA_WIDTH > APB_DATA_WIDTH`:
  - Single AXI beat → Multiple APB beats
  - Data sliced according to APB_DATA_WIDTH
  - WSTRB mapped to PSTRB per beat
- When `AXI_DATA_WIDTH == APB_DATA_WIDTH`:
  - Direct 1:1 mapping

**Protection Signals:**
- `AWPROT/ARPROT` → `PPROT` (direct mapping)

**Error Handling:**
- `PSLVERR` → `BRESP[1]` (write errors)
- `PSLVERR` → `RRESP[1]` (read errors)
- Write errors accumulated (OR'd) into B; read beats accumulate PSLVERR across their APB slices per beat (see the convert page; the per-slice loss was TASK-064, fixed)

### Clock Domain Crossing

**CDC Handshake Protocol:**
- Uses two `gaxi_fifo_async` async FIFOs (Gray or Johnson pointer encoding via `USE_JOHNSON`); the earlier 2-phase `cdc_handshake` scheme was replaced -- it could permanently offset the response stream
- Command path: `aclk` → `pclk`
- Response path: `pclk` → `aclk`
- Zero data loss, proper synchronization

**Timing:**
- Command CDC latency: 3-5 cycles (depending on clock ratio)
- Response CDC latency: 3-5 cycles
- Total round-trip latency: AXI skid + convert + 2×CDC + APB protocol

---

## Timing

### Latency

| Configuration | Typical Latency | Notes |
|--------------|-----------------|-------|
| Same clock, no width convert | 5-7 cycles | Minimal overhead |
| Same clock, width convert | 8-12 cycles | +1 cycle per APB beat |
| Dual-clock, no width convert | 12-16 cycles | +3-5 cycles per CDC |
| Dual-clock, width convert | 15-20 cycles | Combined overhead |

**Components:**
- AXI skid buffers: 1 cycle
- Conversion logic: 2-3 cycles
- CMD CDC: 3-5 cycles
- APB protocol: 2 cycles minimum
- RSP CDC: 3-5 cycles

### Throughput

**Maximum AXI Burst Throughput:**
- Limited by APB protocol (2 cycles per beat minimum)
- Width conversion: N APB beats per AXI beat (N = AXI_DW / APB_DW)
- **Example:** 64b AXI → 32b APB = 4 APB cycles per AXI beat

**Sustained Bandwidth:**
```
AXI Bandwidth → APB Bandwidth:
- Same width: APB_BW = AXI_BW / 2 (APB overhead)
- 2:1 ratio:  APB_BW = AXI_BW / 4
- 4:1 ratio:  APB_BW = AXI_BW / 8
```

---

## Usage Example

### Example 1: Same Clock, Same Width

```systemverilog
// Simplest configuration: same clock, same data width
axi4_to_apb4_shim #(
    .DEPTH_AW(2),
    .DEPTH_W(2),
    .DEPTH_B(2),
    .DEPTH_AR(2),
    .DEPTH_R(2),
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .APB_ADDR_WIDTH(32),
    .APB_DATA_WIDTH(32)
) u_shim (
    .aclk(system_clk),
    .aresetn(system_resetn),
    .pclk(system_clk),       // Same clock
    .presetn(system_resetn), // Same reset

    // Connect AXI slave interface
    .s_axi_awid(axi_awid),
    .s_axi_awaddr(axi_awaddr),
    // ... all AXI signals ...

    // Connect APB master interface
    .m_apb_PSEL(apb_psel),
    .m_apb_PADDR(apb_paddr),
    // ... all APB signals ...
);
```

### Example 2: Dual-Clock with Width Conversion

```systemverilog
// AXI @ 200 MHz, 64-bit → APB @ 100 MHz, 32-bit
axi4_to_apb4_shim #(
    .DEPTH_AW(4),            // Deeper for CDC
    .DEPTH_W(8),             // Extra depth for width conversion
    .DEPTH_B(4),
    .DEPTH_AR(4),
    .DEPTH_R(8),
    .SIDE_DEPTH(8),          // More side info for bursts
    .APB_CMD_DEPTH(8),       // Deeper CDC FIFOs
    .APB_RSP_DEPTH(8),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),     // 64-bit AXI
    .APB_ADDR_WIDTH(32),
    .APB_DATA_WIDTH(32)      // 32-bit APB (2:1 ratio)
) u_shim (
    .aclk(axi_clk_200mhz),
    .aresetn(axi_resetn),
    .pclk(apb_clk_100mhz),   // Different clock
    .presetn(apb_resetn),
    // ... connections ...
);
```

### Example 3: CPU-Peripheral Bridge

```systemverilog
// ARM AXI CPU → APB peripherals
axi4_to_apb4_shim #(
    .DEPTH_AW(2),
    .DEPTH_W(4),
    .DEPTH_B(2),
    .DEPTH_AR(2),
    .DEPTH_R(4),
    .AXI_ID_WIDTH(12),       // CPU master ID width
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .AXI_USER_WIDTH(8),      // CPU user signals
    .APB_ADDR_WIDTH(32),
    .APB_DATA_WIDTH(32)
) u_cpu_to_periph (
    .aclk(cpu_clk),
    .aresetn(cpu_resetn),
    .pclk(periph_clk),
    .presetn(periph_resetn),

    // From CPU AXI master
    .s_axi_awid(cpu_m_axi_awid),
    .s_axi_awaddr(cpu_m_axi_awaddr),
    // ... rest of AXI interface ...

    // To APB peripheral bus
    .m_apb_PSEL(periph_psel),
    .m_apb_PADDR(periph_paddr),
    // ... rest of APB interface ...
);
```

---

## Design Notes

### Constraints and Limitations

**Parameter Constraints:**
- `APB_DATA_WIDTH` must be ≤ `AXI_DATA_WIDTH`
- `AXI_DATA_WIDTH / APB_DATA_WIDTH` must be power of 2
- `APB_ADDR_WIDTH` should match `AXI_ADDR_WIDTH` (or be subset)
- All DEPTH_* parameters must be 2..8 inclusive (any integer) (gaxi_skid_buffer elaboration guard)

**Protocol Limitations:**
- APB does not support outstanding transactions (serialized)
- APB does not support bursts (AXI bursts decomposed)
- No support for AXI exclusive access (AWLOCK/ARLOCK ignored)
- No support for AXI cache hints (AWCACHE/ARCACHE ignored)

**CDC Requirements:**
- Clock domains must be asynchronous (no phase relationship assumed)
- Resets must be properly synchronized in each domain
- Metastability-hardened flip-flops recommended for CDC paths

### Synthesis Notes

**Resource Usage (Typical):**

| Configuration | LUTs | FFs | BRAM | Notes |
|--------------|------|-----|------|-------|
| 32b/32b, shallow | ~800 | ~600 | 0 | Minimal buffering |
| 64b/32b, moderate | ~1200 | ~900 | 0 | Width conversion |
| 64b/32b, deep | ~1500 | ~1100 | 0 | CDC + deep buffers |

**Breakdown:**
- 2× gaxi_fifo_async (depth 4): FIFO storage + gray-pointer synchronizers

**Critical Paths:**
- AXI packet unpacking (combinatorial)
- Width conversion muxing
- CDC synchronizers (use proper constraints)

**Recommended Constraints:**
```tcl
# Set false path between clock domains
set_false_path -from [get_clocks aclk] -to [get_clocks pclk]
set_false_path -from [get_clocks pclk] -to [get_clocks aclk]

# Constrain CDC paths
# The CDC FIFOs' pointer synchronizers carry the crossing; constrain the
# async FIFO instances, not a cdc_handshake hierarchy (none exists here)
set_max_delay -from [get_pins */u_cmd_cdc_fifo/*] \
              -to   [get_pins */u_cmd_cdc_fifo/*] 10.0 -datapath_only
set_max_delay -from [get_pins */u_rsp_cdc_fifo/*] \
              -to   [get_pins */u_rsp_cdc_fifo/*] 10.0 -datapath_only
```

### When to Use

**Use This Shim When:**
- Bridging AXI4 system interconnect to APB peripherals
- Different clock domains for AXI and APB buses
- Need protocol conversion with full CDC support
- CPU/DMA master accessing peripheral registers

**Consider Alternatives When:**
- Both sides are AXI (use AXI crossbar/interconnect instead)
- Both sides are APB (use APB crossbar)
- Need high-performance memory access (APB is slow, use AXI4)

---

## Related Modules

- **[axi4_to_apb4_convert](axi4_to_apb4_convert.md)** - Core conversion logic (instantiated internally)
- **[axi4_slave_stub](../axi4/axi4_slave_stub.md)** - AXI slave interface wrapper
- **[apb4_master_stub](../apb4/apb4_master_stub.md)** - APB master interface wrapper
- **[gaxi_fifo_async](../../rtl-cdc/gaxi_fifo_async.md)** - the CDC FIFO used for both crossings

---

## Testing

```bash
# Run integration test
pytest projects/components/converters/dv/tests/test_axi2apb4_shim.py -v

# Test with waveforms
pytest projects/components/converters/dv/tests/test_axi2apb4_shim.py --vcd=shim.vcd -v
gtkwave shim.vcd

# Run with specific configuration
pytest "projects/components/converters/dv/tests/test_axi2apb4_shim.py::test_axi2apb4[64-32]" -v
```

---

**Last Updated:** 2025-10-20

---

## Navigation

- [Back to Shims Index](README.md)
- [Back to rtl-amba Index](../index.md)
