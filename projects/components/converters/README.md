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
- **High Throughput** - Optional dual-buffer mode for 100% throughput (downsize)
- **Generic Building Blocks** - Reusable `axi_data_upsize` and `axi_data_dnsize` modules

**Protocol Converters:**
- **AXI4-to-APB Bridge** - Full AXI4 to APB protocol conversion with address/data width adaptation
- **PeakRDL Adapter** - Convert PeakRDL register interface to custom command/response protocol

### Performance Summary

| Module | Mode | Throughput | Area | Use Case |
|--------|------|------------|------|----------|
| **axi_data_upsize** | Single buffer | 100% | 1× | Narrow→Wide (always optimal) |
| **axi_data_dnsize** | Single buffer | 80% | 1× | Wide→Narrow (area-efficient) |
| **axi_data_dnsize** | Dual buffer | 100% | 2× | Wide→Narrow (high-performance) |

---

## Architecture Overview

### Component Hierarchy

```
Converters Component
├── Data Width Converters:
│   ├── Generic Building Blocks:
│   │   ├── axi_data_upsize.sv      - Narrow→Wide accumulator (100% throughput)
│   │   ├── axi_data_dnsize.sv      - Wide→Narrow splitter (80% or 100% throughput)
│   │   └── Key Features:
│   │       ├── Configurable sideband handling
│   │       ├── Optional burst tracking
│   │       └── Dual-buffer mode (dnsize only)
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
    ├── axi4_to_apb_convert.sv   - AXI4-to-APB bridge (full protocol conversion)
    ├── axi4_to_apb_shim.sv      - AXI4-to-APB adapter (simplified wrapper)
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
│   │ axi_data_dnsize  │ (DUAL_BUFFER=1)             │
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

**Throughput:**
- Single-buffer mode (DUAL_BUFFER=0): 80% (1-cycle gap per wide beat)
- Dual-buffer mode (DUAL_BUFFER=1): 100% (continuous streaming)

**Key Parameters:**
```systemverilog
parameter int WIDE_WIDTH        = 512;     // Input data width
parameter int NARROW_WIDTH      = 128;     // Output data width (must be integer divisor)
parameter int WIDE_SB_WIDTH     = 2;       // Wide sideband width (RRESP: 2 bits)
parameter int NARROW_SB_WIDTH   = 2;       // Narrow sideband width
parameter int SB_BROADCAST      = 1;       // 1=broadcast (RRESP), 0=slice (WSTRB)
parameter int TRACK_BURSTS      = 0;       // 1=track bursts for LAST, 0=simple passthrough
parameter int BURST_LEN_WIDTH   = 8;       // Burst length counter width
parameter int DUAL_BUFFER       = 0;       // 1=dual buffer (100% throughput, 2× area)
                                           // 0=single buffer (80% throughput, 1× area)
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

**Dual-Buffer Mode (NEW in v1.1):**

Single-buffer mode achieves 80% throughput due to 1-cycle gap when transitioning between wide beats:
```
Cycle: 1    2    3    4    5    6    7    8    9   10
Wide:  [====BEAT_0====]  WAIT [====BEAT_1====]  WAIT
Narrow: n0   n1   n2   n3  IDLE  n0   n1   n2   n3  IDLE
                            ↑ 1-cycle dead time
```

Dual-buffer mode eliminates the gap by ping-ponging between two buffers:
```
Cycle: 1    2    3    4    5    6    7    8    9
Wide:  [====BEAT_0====][====BEAT_1====][====BEAT_2====]
Narrow: n0   n1   n2   n3   n0   n1   n2   n3   n0
Buffer: BUF0 reading────┘   BUF1 reading────┘   BUF0...
        BUF1 writing────────┘   BUF0 writing────┘
```

**When to Use Dual-Buffer Mode:**
- High-bandwidth DMA engines with continuous streaming
- Performance-critical data paths where 100% utilization required
- Sufficient area budget (~2× increase for buffer registers)

**When to Use Single-Buffer Mode:**
- Area-constrained designs
- Throughput requirements <100%
- Natural gaps in traffic from upstream/downstream

**Usage Example (Single-Buffer):**
```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(2),      // RRESP: 2 bits
    .NARROW_SB_WIDTH(2),
    .SB_BROADCAST(1),       // Broadcast RRESP
    .TRACK_BURSTS(1),       // Track bursts for LAST
    .BURST_LEN_WIDTH(8),
    .DUAL_BUFFER(0)         // Single buffer (80% throughput, area-efficient)
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

**Usage Example (Dual-Buffer - High Performance):**
```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(64),     // WSTRB: 512/8 = 64
    .NARROW_SB_WIDTH(16),   // WSTRB: 128/8 = 16
    .SB_BROADCAST(0),       // Slice WSTRB
    .TRACK_BURSTS(0),       // Simple mode for write path
    .DUAL_BUFFER(1)         // Dual buffer (100% throughput, 2× area)
) u_dnsize_hp (
    .aclk             (aclk),
    .aresetn          (aresetn),

    // Burst control (unused in TRACK_BURSTS=0)
    .burst_len        (8'd0),
    .burst_start      (1'b0),

    // Wide input
    .wide_valid       (s_wvalid),
    .wide_ready       (s_wready),
    .wide_data        (s_wdata),
    .wide_sideband    (s_wstrb),
    .wide_last        (s_wlast),

    // Narrow output
    .narrow_valid     (m_wvalid),
    .narrow_ready     (m_wready),
    .narrow_data      (m_wdata),
    .narrow_sideband  (m_wstrb),
    .narrow_last      (m_wlast)
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

### 4. AXI4-to-APB Bridge (axi4_to_apb_convert.sv)

**Purpose:** Full protocol conversion from AXI4 to APB with address/data width adaptation

**Key Features:**
- Converts AXI4 read/write transactions to APB protocol
- Handles address width conversion (AXI4 64-bit → APB 32-bit)
- Data width adaptation (configurable)
- State machine for AXI→APB protocol translation
- Error response handling (SLVERR/DECERR)

**Usage Example:**
```systemverilog
axi4_to_apb_convert #(
    .S_AXI_ADDR_WIDTH(64),
    .S_AXI_DATA_WIDTH(32),
    .M_APB_ADDR_WIDTH(32),
    .M_APB_DATA_WIDTH(32)
) u_axi_apb_bridge (
    .aclk           (clk),
    .aresetn        (rst_n),

    // AXI4 Slave Interface
    .s_axi_awaddr   (s_awaddr),
    .s_axi_awvalid  (s_awvalid),
    .s_axi_awready  (s_awready),
    // ... (full AXI4 AW/W/B/AR/R channels)

    // APB Master Interface
    .m_apb_paddr    (m_paddr),
    .m_apb_psel     (m_psel),
    .m_apb_penable  (m_penable),
    .m_apb_pwrite   (m_pwrite),
    .m_apb_pwdata   (m_pwdata),
    .m_apb_pready   (m_pready),
    .m_apb_prdata   (m_prdata),
    .m_apb_pslverr  (m_pslverr)
);
```

**Use Cases:**
- Connecting AXI4 masters to APB peripherals
- CPU to APB peripheral bus bridges
- System integration with mixed protocols

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
    .ADDR_WIDTH(16),
    .DATA_WIDTH(32)
) u_peakrdl_adapter (
    .clk            (clk),
    .rst_n          (rst_n),

    // PeakRDL Register Interface (APB-style)
    .reg_addr       (reg_addr),
    .reg_wdata      (reg_wdata),
    .reg_write      (reg_write),
    .reg_read       (reg_read),
    .reg_rdata      (reg_rdata),
    .reg_error      (reg_error),

    // Command/Response Interface
    .cmd_valid      (cmd_valid),
    .cmd_ready      (cmd_ready),
    .cmd_addr       (cmd_addr),
    .cmd_data       (cmd_data),
    .cmd_write      (cmd_write),

    .rsp_valid      (rsp_valid),
    .rsp_ready      (rsp_ready),
    .rsp_data       (rsp_data),
    .rsp_error      (rsp_error)
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
    .TRACK_BURSTS(0),       // Write path: simple mode
    .DUAL_BUFFER(0)         // Area-efficient
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

### Example 3: High-Performance Write Downsize (512→128 bits)

**Use Case:** DMA Engine (512-bit) → PCIe Endpoint (128-bit), continuous streaming

```systemverilog
axi_data_dnsize #(
    .WIDE_WIDTH(512),
    .NARROW_WIDTH(128),
    .WIDE_SB_WIDTH(64),     // WSTRB: 512/8 = 64
    .NARROW_SB_WIDTH(16),   // WSTRB: 128/8 = 16
    .SB_BROADCAST(0),       // Slice WSTRB
    .TRACK_BURSTS(0),       // Write path: simple mode
    .DUAL_BUFFER(1)         // HIGH-PERFORMANCE: 100% throughput
) u_wr_dnsize_hp (
    // ... ports
);
```

**Result:** 100% throughput (no dead cycles), 2× area cost

---

## Testing

### Test Organization

```
projects/components/converters/dv/tests/
├── test_axi_data_upsize.py       - Generic upsize module tests
├── test_axi_data_dnsize.py       - Generic dnsize module tests (16 configs)
├── test_axi4_dwidth_converter_wr.py  - Full write converter tests
└── test_axi4_dwidth_converter_rd.py  - Full read converter tests
```

### Test Configurations (axi_data_dnsize.py)

**Single-Buffer Tests (DUAL_BUFFER=0):**
1. 128→32 WSTRB slice (simple mode)
2. 256→64 WSTRB slice (simple mode)
3. 128→32 RRESP broadcast (simple mode)
4. 256→64 RRESP broadcast (simple mode)
5. 128→32 RRESP broadcast (burst tracking)
6. 256→64 RRESP broadcast (burst tracking)
7. 512→128 RRESP broadcast (burst tracking)
8. 128→64 no sideband (simple mode)

**Dual-Buffer Tests (DUAL_BUFFER=1):**
9-16. Same configurations as above with DUAL_BUFFER=1

### Running Tests

```bash
# Run all converter tests
cd $REPO_ROOT/projects/components/converters/dv/tests
make run-all-parallel          # FUNC level, 48 workers

# Run specific module tests
make run-dnsize-func           # Downsize tests
make run-upsize-func           # Upsize tests

# Run with different test levels
make run-all-gate-parallel     # Quick smoke test
make run-all-func-parallel     # Functional coverage (default)
make run-all-full-parallel     # Comprehensive validation

# Individual test
pytest test_axi_data_dnsize.py::test_axi_data_dnsize[128to32_wstrb_slice_simple_DUAL] -v
```

---

## Quality Assurance

### Lint Checks

```bash
# Run all lint tools
cd $REPO_ROOT/projects/components/converters/rtl
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

- **README.md** (this file) - Quick start and overview
- **GENERIC_MODULES_USAGE_GUIDE.md** - Detailed parameter guide for upsize/dnsize
- **DUAL_BUFFER_IMPLEMENTATION.md** - Comprehensive dual-buffer feature documentation
- **ANALYSIS_APB_CONVERTER.md** - APB protocol converter analysis

### Key Resources

**For Understanding Parameters:**
```bash
cat $REPO_ROOT/projects/components/converters/rtl/GENERIC_MODULES_USAGE_GUIDE.md
```

**For Dual-Buffer Mode:**
```bash
cat $REPO_ROOT/projects/components/converters/DUAL_BUFFER_IMPLEMENTATION.md
```

**For APB Integration:**
```bash
cat $REPO_ROOT/projects/components/converters/ANALYSIS_APB_CONVERTER.md
```

---

## Quick Commands

```bash
# Setup environment
source $REPO_ROOT/env_python

# Run all tests (parallel)
cd $REPO_ROOT/projects/components/converters/dv/tests
make run-all-parallel

# Lint all RTL
cd $REPO_ROOT/projects/components/converters/rtl
make lint-all

# View test status
cd $REPO_ROOT/projects/components/converters/dv/tests
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

### Why Optional Dual-Buffer for Dnsize?

**Trade-off between area and performance:**
- Single-buffer: 80% throughput, 1× area (good for most use cases)
- Dual-buffer: 100% throughput, 2× area (high-performance paths)
- User can select based on system requirements

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
