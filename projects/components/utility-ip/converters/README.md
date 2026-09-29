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

# Converters - Data Width and Protocol Conversion Modules

**Status:** Production Ready
**Version:** 1.2
**Last Updated:** 2025-10-25

---

## Quick Start

The Converters component provides both data width conversion and protocol conversion modules, enabling seamless integration between components with different data widths or protocols.

### Key Features

**Data Width Converters:**
- **Bidirectional Conversion** - Upsize (narrow→wide) and Downsize (wide→narrow)
- **Flexible Width Ratios** - Any integer ratio (2:1, 4:1, 8:1, 16:1, etc.)
- **Sideband Support** - Configurable handling for WSTRB (slice) and RRESP (broadcast)
- **Burst Tracking** - Optional burst-aware LAST signal generation (read path)
- **Generic Building Blocks** - Reusable `axi_data_upsize` and `axi_data_dnsize` modules

**Protocol Converters:**
- **AXI4-to-APB Bridge** - Full AXI4 to APB protocol conversion with address/data width adaptation
- **PeakRDL Adapter** - Convert PeakRDL register interface to custom command/response protocol

### Performance Summary

| Module | Mode | Throughput | Area | Use Case |
|--------|------|------------|------|----------|
| **axi_data_upsize** | Single buffer | 100% | 1× | Narrow→Wide (always optimal) |
| **axi_data_dnsize** | Single buffer | 80% | 1× | Wide→Narrow (one-cycle gap per wide beat; the ping-pong `DUAL_BUFFER` mode was removed, see MAS 2.3) |

---

## Architecture Overview

### Component Hierarchy

```
Converters Component
├── Data Width Converters:
│   ├── Generic Building Blocks:
│   │   ├── axi_data_upsize.sv      - Narrow→Wide accumulator (100% throughput)
│   │   ├── axi_data_dnsize.sv      - Wide→Narrow splitter (80% throughput)
│   │   └── Key Features:
│   │       ├── Configurable sideband handling
│   │       └── Optional burst tracking
│   │
│   └── Full AXI4 Converters:
│       ├── axi4_dwidth_converter_wr.sv  - Write path converter (AW + W + B channels)
│       ├── axi4_dwidth_converter_rd.sv  - Read path converter (AR + R channels)
│       └── Integration:
│           ├── Skid buffers for flow control
│           ├── Address phase management
│           └── Response path handling
│
└── Protocol Converters:
    ├── axi4_to_apb4_convert.sv   - AXI4-to-APB bridge (full protocol conversion)
    ├── axi4_to_apb4_shim.sv      - AXI4-to-APB adapter (simplified wrapper)
    └── peakrdl_to_cmdrsp.sv     - PeakRDL adapter (register→command/response)
```

### Data Flow Examples

**Write Path Downsize (512→128 bits):**
```
┌────────────────────────────────────────────────────┐
│ Slave Interface (512-bit)                          │
│   ┌──────────┐                                     │
│   │ AW       │ ← 1 address                         │
│   │ W        │ ← 1 wide beat (512-bit + 64-bit WSTRB)
│   │ B        │ → 1 response                        │
│   └──────────┘                                     │
│       ↓                                            │
│   ┌──────────────────┐                             │
│   │ axi_data_dnsize  │                             │
│   │  512→128 split   │                             │
│   └──────────────────┘                             │
│       ↓                                            │
│   ┌──────────┐                                     │
│   │ Master Interface (128-bit)                     │
│   │ AW       │ → 1 address                         │
│   │ W        │ → 4 narrow beats (128-bit + 16-bit WSTRB each)
│   │ B        │ ← 1 response                        │
│   └──────────┘                                     │
└────────────────────────────────────────────────────┘
```

**Read Path Upsize (128→512 bits):**
```
┌────────────────────────────────────────────────────┐
│ Master Interface (512-bit)                         │
│   ┌──────────┐                                     │
│   │ AR       │ → 1 address                         │
│   │ R        │ ← 1 wide beat (512-bit + 2-bit RRESP)
│   └──────────┘                                     │
│       ↑                                            │
│   ┌──────────────────┐                             │
│   │ axi_data_upsize  │ (TRACK_BURSTS=1)            │
│   │  128→512 accum   │                             │
│   └──────────────────┘                             │
│       ↑                                            │
│   ┌──────────┐                                     │
│   │ Slave Interface (128-bit)                      │
│   │ AR       │ ← 1 address                         │
│   │ R        │ → 4 narrow beats (128-bit + 2-bit RRESP each)
│   └──────────┘                                     │
└────────────────────────────────────────────────────┘
```

---

## Module Documentation

### 1. axi_data_upsize.sv - Narrow→Wide Accumulator

**Purpose:** Accumulates multiple narrow beats into a single wide beat

**Throughput:** 100% (single buffer sufficient)

**Key Parameters:**
```systemverilog
parameter int NARROW_WIDTH    = 32;      // Input data width
parameter int WIDE_WIDTH      = 128;     // Output data width (must be integer multiple)
parameter int NARROW_SB_WIDTH = 4;       // Narrow sideband width (WSTRB: WIDTH/8)
parameter int WIDE_SB_WIDTH   = 16;      // Wide sideband width (WSTRB: WIDTH/8)
parameter int SB_OR_MODE      = 0;       // 0=concatenate (WSTRB), 1=OR (RRESP)
```

**Sideband Modes:**
- **SB_OR_MODE=0 (Concatenate):** For WSTRB - assemble strobe bits
  ```
  narrow[0].wstrb = 4'b1111 → wide.wstrb[3:0]
  narrow[1].wstrb = 4'b1100 → wide.wstrb[7:4]
  narrow[2].wstrb = 4'b0011 → wide.wstrb[11:8]
  narrow[3].wstrb = 4'b1111 → wide.wstrb[15:12]
  Result: wide.wstrb = 16'b1111_0011_1100_1111
  ```

- **SB_OR_MODE=1 (OR Together):** For RRESP - propagate errors
  ```
  narrow[0].rresp = 2'b00 (OK)
  narrow[1].rresp = 2'b10 (SLVERR)
  narrow[2].rresp = 2'b00 (OK)
  narrow[3].rresp = 2'b00 (OK)
  Result: wide.rresp = 2'b10 (SLVERR - any error propagates)
  ```

**Usage Example:**
```systemverilog
axi_data_upsize #(
    .NARROW_WIDTH(128),
    .WIDE_WIDTH(512),
    .NARROW_SB_WIDTH(16),  // WSTRB: 128/8 = 16
    .WIDE_SB_WIDTH(64),    // WSTRB: 512/8 = 64
    .SB_OR_MODE(0)         // Concatenate WSTRB
) u_upsize (
    .aclk             (aclk),
    .aresetn          (aresetn),

    // Narrow input
    .narrow_valid     (s_wvalid),
    .narrow_ready     (s_wready),
    .narrow_data      (s_wdata),
    .narrow_sideband  (s_wstrb),
    .narrow_last      (s_wlast),
    .start_lane       ('0),            // lane the burst's first narrow beat lands on;
                                       // '0 for word-aligned starts, the tracked
                                       // value for mid-word INCR packing

    // Wide output
    .wide_valid       (m_wvalid),
    .wide_ready       (m_wready),
    .wide_data        (m_wdata),
    .wide_sideband    (m_wstrb),
    .wide_last        (m_wlast)
);
```

---

### 2. axi_data_dnsize.sv - Wide→Narrow Splitter

**Purpose:** Splits single wide beat into multiple narrow beats

**Throughput:** 80% -- a one-cycle gap per wide beat while the single buffer
refills. (An earlier `DUAL_BUFFER` ping-pong mode reached 100%; it was removed
from the RTL -- `git log -S DUAL_BUFFER rtl/axi_data_dnsize.sv` -- and the
MAS, `docs/converter_mas/ch02_width_blocks/03_axi_data_dnsize.md`, records why.)

**Key Parameters:**
```systemverilog
parameter int WIDE_WIDTH        = 512;     // Input data width
parameter int NARROW_WIDTH      = 128;     // Output data width (must be integer divisor)
parameter int WIDE_SB_WIDTH     = 2;       // Wide sideband width (RRESP: 2 bits)
parameter int NARROW_SB_WIDTH   = 2;       // Narrow sideband width
parameter int SB_BROADCAST      = 1;       // 1=broadcast (RRESP), 0=slice (WSTRB)
parameter int TRACK_BURSTS      = 0;       // 1=track bursts for LAST, 0=simple passthrough
parameter int BURST_LEN_WIDTH   = 8;       // Burst length counter width
```

**Sideband Modes:**
- **SB_BROADCAST=1:** Broadcast same value to all narrow beats (RRESP)
  ```
  wide.rresp = 2'b10 (SLVERR)
  → narrow[0].rresp = 2'b10
  → narrow[1].rresp = 2'b10
  → narrow[2].rresp = 2'b10
  → narrow[3].rresp = 2'b10
  ```

- **SB_BROADCAST=0:** Slice into narrow portions (WSTRB)
  ```
  wide.wstrb = 64'h000F_F0FF_00FF_FFFF
  → narrow[0].wstrb[15:0]  = 16'hFFFF
  → narrow[1].wstrb[15:0]  = 16'h00FF
  → narrow[2].wstrb[15:0]  = 16'hF0FF
  → narrow[3].wstrb[15:0]  = 16'h000F
  ```

**Burst Tracking Mode:**
- **TRACK_BURSTS=0:** Pass wide_last to last narrow beat (simple mode)
- **TRACK_BURSTS=1:** Generate LAST on final beat of entire burst (read path)

**Usage Example:**
```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(2),      // RRESP: 2 bits
    .NARROW_SB_WIDTH(2),
    .SB_BROADCAST(1),       // Broadcast RRESP
    .TRACK_BURSTS(1),       // Track bursts for LAST
    .BURST_LEN_WIDTH(8)
) u_dnsize (
    .aclk             (aclk),
    .aresetn          (aresetn),

    // Burst control (TRACK_BURSTS=1)
    .burst_len        (arlen),
    .burst_start      (arvalid && arready),

    // Wide input
    .wide_valid       (s_rvalid),
    .wide_ready       (s_rready),
    .wide_data        (s_rdata),
    .wide_sideband    (s_rresp),
    .wide_last        (s_rlast),

    // Narrow output
    .narrow_valid     (m_rvalid),
    .narrow_ready     (m_rready),
    .narrow_data      (m_rdata),
    .narrow_sideband  (m_rresp),
    .narrow_last      (m_rlast)
);
```

---

### 3. Full AXI4 Converters

**axi4_dwidth_converter_wr.sv** - Complete write path converter (AW + W + B)

**axi4_dwidth_converter_rd.sv** - Complete read path converter (AR + R)

These integrate the generic building blocks with:
- Address phase management
- Skid buffers for flow control
- Response path handling
- Full AXI4 protocol compliance

---

## Protocol Converters

### 4. AXI4-to-APB Bridge (axi4_to_apb4_convert.sv)

**Purpose:** Full protocol conversion from AXI4 to APB with address/data width adaptation

**Key Features:**
- Converts AXI4 read/write transactions to APB protocol
- Handles address width conversion (AXI4 64-bit → APB 32-bit)
- Data width adaptation (configurable)
- State machine for AXI→APB protocol translation
- Error response handling (SLVERR/DECERR)

**Usage Example:**
```systemverilog
// axi4_to_apb4_convert works on PACKED channel beats (one vector per AXI
// channel, as the gaxi skid buffers emit them) and a packed APB command /
// response pair; axi4_to_apb4_shim wraps it with plain AXI4 and APB ports.
axi4_to_apb4_convert #(
    .AXI_ID_WIDTH   (8),
    .AXI_ADDR_WIDTH (32),
    .AXI_DATA_WIDTH (64),
    .APB_ADDR_WIDTH (32),
    .APB_DATA_WIDTH (32),       // AXI2APBRATIO = 64/32 = 2 narrow beats per wide beat
    .SIDE_DEPTH     (6)
) u_axi_apb_convert (
    .aclk             (aclk),
    .aresetn          (aresetn),

    // AXI4 slave side: packed AW / W / B / AR / R beats
    .r_s_axi_aw_pkt   (aw_pkt),    .r_s_axi_aw_count (aw_count),
    .r_s_axi_awvalid  (aw_valid),  .w_s_axi_awready  (aw_ready),
    .r_s_axi_w_pkt    (w_pkt),     .r_s_axi_wvalid   (w_valid),   .w_s_axi_wready (w_ready),
    .r_s_axi_b_pkt    (b_pkt),     .w_s_axi_bvalid   (b_valid),   .r_s_axi_bready (b_ready),
    .r_s_axi_ar_pkt   (ar_pkt),    .r_s_axi_ar_count (ar_count),
    .r_s_axi_arvalid  (ar_valid),  .w_s_axi_arready  (ar_ready),
    .r_s_axi_r_pkt    (r_pkt),     .w_s_axi_rvalid   (r_valid),   .r_s_axi_rready (r_ready),

    // APB master side: packed command out, packed response in
    .w_cmd_valid      (cmd_valid), .r_cmd_ready      (cmd_ready), .r_cmd_data (cmd_data),
    .r_rsp_valid      (rsp_valid), .w_rsp_ready      (rsp_ready), .r_rsp_data (rsp_data)
);
```

**Use Cases:**
- Connecting AXI4 masters to APB peripherals
- CPU to APB peripheral bus bridges
- System integration with mixed protocols

---

### 4a. AXI4-Lite-to-Wishbone Bridge (axil4_to_wb4.sv)

**Purpose:** AXI4-Lite slave in, Wishbone B4 master out (pipelined, or classic with `CLASSIC=1`)

**Key Features:**
- Built from the AXI4-Lite slave skids, a small in-order conversion core and `wb4_master`
- Write and read paths merged into one command queue; responses routed back by issue order (a B4 rule), no IDs, no FSM
- Alternates between a pending write and a pending read, so neither starves
- ACK -> OKAY, ERR -> SLVERR, RTY -> `RTY_RESP` (SLVERR by default; AXI has no retry)
- Same address and data width both sides; use the width converters in front when they differ

**Use Cases:**
- AXI4-Lite interconnects reaching Wishbone peripherals
- Wishbone IP reuse behind an AXI4-Lite register fabric

See the MAS chapter `docs/converter_mas/ch03_protocol_blocks/10_axil4_to_wb4.md`.

---

### 5. PeakRDL-to-CmdRsp Adapter (peakrdl_to_cmdrsp.sv)

**Purpose:** Convert PeakRDL-generated register interface to custom command/response protocol

**Key Features:**
- Converts APB-style register interface to command/response handshake
- Supports read/write operations
- Configurable command/response data widths
- Single-cycle command issue
- Pipelined response handling

**Usage Example:**
```systemverilog
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH (12),
    .DATA_WIDTH (32)
) u_peakrdl_adapter (
    .aclk                 (aclk),
    .aresetn              (aresetn),

    // Command in (APB-shaped request), response out
    .cmd_valid            (cmd_valid),  .cmd_ready  (cmd_ready),
    .cmd_pwrite           (cmd_pwrite), .cmd_paddr  (cmd_paddr),
    .cmd_pwdata           (cmd_pwdata), .cmd_pstrb  (cmd_pstrb),
    .rsp_valid            (rsp_valid),  .rsp_ready  (rsp_ready),
    .rsp_prdata           (rsp_prdata), .rsp_pslverr(rsp_pslverr),

    // PeakRDL regblock "passthrough" cpuif
    .regblk_req           (regblk_req),          .regblk_req_is_wr    (regblk_req_is_wr),
    .regblk_addr          (regblk_addr),         .regblk_wr_data      (regblk_wr_data),
    .regblk_wr_biten      (regblk_wr_biten),
    .regblk_req_stall_wr  (regblk_req_stall_wr), .regblk_req_stall_rd (regblk_req_stall_rd),
    .regblk_rd_ack        (regblk_rd_ack),       .regblk_rd_err       (regblk_rd_err),
    .regblk_rd_data       (regblk_rd_data),
    .regblk_wr_ack        (regblk_wr_ack),       .regblk_wr_err       (regblk_wr_err)
);
```

**Use Cases:**
- Interfacing PeakRDL register blocks to custom control logic
- Register access through command/response protocol
- Decoupling register interface from implementation

---

## Configuration Examples

### Example 1: Write Path Downsize (128→32 bits)

**Use Case:** ARM Cortex-M7 (128-bit AXI) → APB Bridge (32-bit)

```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(128),
    .NARROW_WIDTH(32),
    .WIDE_SB_WIDTH(16),     // WSTRB: 128/8 = 16
    .NARROW_SB_WIDTH(4),    // WSTRB: 32/8 = 4
    .SB_BROADCAST(0),       // Slice WSTRB
    .TRACK_BURSTS(0)        // Write path: simple mode
) u_wr_dnsize (
    // ... ports
);
```

**Result:** 1 wide W beat (128-bit) → 4 narrow W beats (32-bit each)

---

### Example 2: Read Path Upsize (256→512 bits)

**Use Case:** DDR4 Controller (512-bit) ← FPGA Fabric (256-bit)

```systemverilog
axi_data_upsize #(
    .NARROW_WIDTH(256),
    .WIDE_WIDTH(512),
    .NARROW_SB_WIDTH(2),    // RRESP: 2 bits
    .WIDE_SB_WIDTH(2),      // RRESP: 2 bits
    .SB_OR_MODE(1)          // OR together RRESP
) u_rd_upsize (
    // ... ports
);
```

**Result:** 2 narrow R beats (256-bit) → 1 wide R beat (512-bit)

---

## Testing

### Test Organization

```
projects/components/utility-ip/converters/dv/tests/
├── test_axi_data_upsize.py       - Generic upsize module tests
├── test_axi_data_dnsize.py       - Generic dnsize module tests (8 configs)
├── test_axi4_dwidth_converter_wr.py  - Full write converter tests
└── test_axi4_dwidth_converter_rd.py  - Full read converter tests
```

### Test Configurations (test_axi_data_dnsize.py)

The `test_params` table in the test file is the list; as of 2026-09-29 it holds
eight configurations, each run at every REG_LEVEL:

1. 128→32 WSTRB slice (simple mode)
2. 256→64 WSTRB slice (simple mode)
3. 128→32 RRESP broadcast (simple mode)
4. 256→64 RRESP broadcast (simple mode)
5. 128→32 RRESP broadcast (burst tracking)
6. 256→64 RRESP broadcast (burst tracking)
7. 512→128 RRESP broadcast (burst tracking)
8. 128→64 no sideband (simple mode)

### Running Tests

```bash
# Run all converter tests
cd $REPO_ROOT/projects/components/utility-ip/converters/dv/tests
make run-all-parallel          # FUNC level, 48 workers

# Run specific module tests
make run-dnsize-func           # Downsize tests
make run-upsize-func           # Upsize tests

# Run with different test levels
make run-all-gate-parallel     # Quick smoke test
make run-all-func-parallel     # Functional coverage (default)
make run-all-full-parallel     # Comprehensive validation

# Individual test
pytest test_axi_data_dnsize.py -k 128to32_wstrb_slice_simple -v
```

---

## Quality Assurance

### Lint Checks

```bash
# Run all lint tools
cd $REPO_ROOT/projects/components/utility-ip/converters/rtl
make lint-all

# Individual tools
make verilator    # Verilator lint
make verible      # Verible style check
make yosys        # Yosys synthesis check

# View status
make status
```

### Expected Lint Results

**axi_data_upsize.sv and axi_data_dnsize.sv:**
- Clean compilation (warnings only for unused signals in certain parameter configurations)
- Warnings are benign (e.g., narrow_sideband unused when NARROW_SB_WIDTH=0)

**axi4_dwidth_converter_*.sv:**
- Requires rtl/amba/gaxi/ include path for skid buffer modules
- PINCONNECTEMPTY warnings are expected (unused count outputs)

---

## Documentation

### Available Documentation

- **README.md** (this file) -- quick start and overview; a link page, not the spec
- **`docs/converter_mas/`** -- the Micro-Architecture Spec: per-block chapters
  (`ch02_width_blocks/` for upsize/dnsize/dwidth/wide-align, `ch03_protocol_blocks/`
  for the APB/AXIL/WB4/PeakRDL converters), FSMs, verification. The dnsize chapter
  records why the dual-buffer mode was removed; the APB chapter (3.4.12) records
  why its width conversion is inline rather than built from the generic blocks.
- **`docs/AXI4_DATA_WIDTH_CONVERTER_SPEC.md`**, **`docs/peakrdl_to_cmdrsp.md`** -- block specs

## Quick Commands

```bash
# Setup environment
source $REPO_ROOT/env_python

# Run all tests (parallel)
cd $REPO_ROOT/projects/components/utility-ip/converters/dv/tests
make run-all-parallel

# Lint all RTL
cd $REPO_ROOT/projects/components/utility-ip/converters/rtl
make lint-all

# View test status
cd $REPO_ROOT/projects/components/utility-ip/converters/dv/tests
make status

# Clean all artifacts
make clean-all
```

---

## Design Decisions

### Why No Dual-Buffer for Upsize?

**axi_data_upsize already achieves 100% throughput** with single buffer:
- Can accept narrow beat while outputting wide beat simultaneously
- The `|| wide_ready` term in narrow_ready enables pipelining
- No benefit from dual buffering

### Why No Dual-Buffer for Dnsize Either?

There was one (`DUAL_BUFFER`, a ping-pong pair for 100% throughput at 2x
area). It was removed from `axi_data_dnsize.sv`; the dwidth converters that
need full-rate downsizing get it from their skid buffers instead. The MAS
dnsize chapter records the reasoning; this README only points at it.

### Why Separate Upsize/Dnsize Modules?

**Promotes reuse and flexibility:**
- Can be used independently in custom converters
- Write converter: upsize + dnsize combination
- Read converter: dnsize + upsize combination
- Other use cases: data width matching, FIFO interfaces, etc.

---

## Known Limitations

1. **Width Ratio Constraint:** WIDE_WIDTH must be exact integer multiple of NARROW_WIDTH
2. **Alignment:** Full converters require aligned addresses (handled by full converter modules)
3. **Burst Length:** Burst tracking mode supports AXI4 burst lengths (BURST_LEN_WIDTH=8)
4. **Sideband Width:** Must match data width ratios for slice mode

---

## Future Enhancements

1. **Configurable Buffer Depth:** Allow >2 buffers for higher throughput
2. **Performance Counters:** Monitor stalls, utilization, throughput
3. **Power Gating:** Disable unused buffer in dual-buffer mode
4. **Credit-Based Flow Control:** Integration with upstream credit systems

---

## Version History

- **v1.1 (2025-10-25):** Added dual-buffer mode for axi_data_dnsize (100% throughput)
- **v1.0 (2025-10-24):** Initial release with generic modules and full converters

---

## Related Components

- **STREAM** - DMA engine using width converters for descriptor fetch
- **RAPIDS** - Accelerator with width conversion on data paths
- **APB HPET** - APB peripheral using narrow interfaces
- **Bridge** - Protocol converters with width adaptation

---

**Author:** RTL Design Sherpa Project
**Last Updated:** 2025-10-25
