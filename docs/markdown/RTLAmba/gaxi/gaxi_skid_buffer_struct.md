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

# gaxi_skid_buffer_struct

**Module:** `gaxi_skid_buffer_struct.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** ✅ Production Ready

---

## Overview

Struct-aware variant of **[gaxi_skid_buffer](gaxi_skid_buffer.md)** that accepts SystemVerilog type parameters instead of explicit data width. This enables clean handling of complex data structures (e.g., AXI channels, custom packets) without manual packing/unpacking.

### Key Features

- ✅ **Type-Parameterized:** Accepts any SystemVerilog type (struct, union, enum, packed array)
- ✅ **Automatic Width Calculation:** Uses `$bits()` to determine buffer width
- ✅ **Zero-Latency Bypass:** Identical performance to base skid buffer
- ✅ **Same Architecture:** Shift register with valid/ready flow control
- ✅ **Debug Support:** Instance naming and transaction logging

---

## Module Declaration

```systemverilog
module gaxi_skid_buffer_struct #(
    parameter type STRUCT_TYPE = logic [31:0],  // Any SystemVerilog type
    parameter int  DEPTH = 2,                   // Must be {2, 4, 6, 8}
    parameter      INSTANCE_NAME = "DEADF1F0",  // Debug identifier

    // Automatically derived
    localparam int STRUCT_WIDTH = $bits(STRUCT_TYPE),
    localparam int BUF_WIDTH = STRUCT_WIDTH * DEPTH
) (
    // Global Clock and Reset
    input  logic        axi_aclk,
    input  logic        axi_aresetn,

    // Input side
    input  logic        wr_valid,
    output logic        wr_ready,
    input  STRUCT_TYPE  wr_data,     // Type-safe input

    // Output side
    output logic [3:0]  count,
    output logic        rd_valid,
    input  logic        rd_ready,
    output logic [3:0]  rd_count,
    output STRUCT_TYPE  rd_data      // Type-safe output
);
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `STRUCT_TYPE` | type | `logic [31:0]` | Any SystemVerilog type (struct, union, enum, array) |
| `DEPTH` | int | 2 | Buffer depth (must be 2, 4, 6, or 8) |
| `INSTANCE_NAME` | string | "DEADF1F0" | Debug identifier for simulation messages |

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `axi_aclk` | 1 | Input | Clock |
| `axi_aresetn` | 1 | Input | Active-low asynchronous reset |

### Write Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `wr_valid` | 1 | Input | Write data valid |
| `wr_ready` | 1 | Output | Ready to accept write |
| `wr_data` | STRUCT_TYPE | Input | Input data (type-safe) |

### Read Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `rd_valid` | 1 | Output | Read data valid |
| `rd_ready` | 1 | Input | Ready to consume read |
| `rd_data` | STRUCT_TYPE | Output | Output data (type-safe) |

### Status

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `count` | 4 | Output | Current buffer occupancy (0 to DEPTH) |
| `rd_count` | 4 | Output | Same as count (for compatibility) |

---

## Usage Examples

### Example 1: AXI Read Address Channel

```systemverilog
// Define AXI AR channel struct
typedef struct packed {
    logic [7:0]  arid;
    logic [31:0] araddr;
    logic [7:0]  arlen;
    logic [2:0]  arsize;
    logic [1:0]  arburst;
    logic        arlock;
    logic [3:0]  arcache;
    logic [2:0]  arprot;
    logic [3:0]  arqos;
} axi_ar_t;

// Instantiate struct-aware buffer
gaxi_skid_buffer_struct #(
    .STRUCT_TYPE(axi_ar_t),
    .DEPTH(4),
    .INSTANCE_NAME("AXI_AR_BUF")
) u_ar_buffer (
    .axi_aclk    (axi_clk),
    .axi_aresetn (axi_resetn),

    // Input: Directly assign struct
    .wr_valid    (master_arvalid),
    .wr_ready    (master_arready),
    .wr_data     ({master_arid, master_araddr, master_arlen,
                   master_arsize, master_arburst, master_arlock,
                   master_arcache, master_arprot, master_arqos}),

    // Output: Unpack struct
    .rd_valid    (slave_arvalid),
    .rd_ready    (slave_arready),
    .rd_data     ({slave_arid, slave_araddr, slave_arlen,
                   slave_arsize, slave_arburst, slave_arlock,
                   slave_arcache, slave_arprot, slave_arqos}),

    .count       (ar_buf_count),
    .rd_count    ()
);
```

### Example 2: Custom Packet with Mixed Fields

```systemverilog
// Define custom packet structure
typedef struct packed {
    logic [15:0] packet_id;
    logic [7:0]  packet_type;
    logic [31:0] timestamp;
    logic [63:0] payload;
    logic [3:0]  priority;
    logic        last;
} custom_pkt_t;

// Buffer for packet pipeline
gaxi_skid_buffer_struct #(
    .STRUCT_TYPE(custom_pkt_t),
    .DEPTH(8),
    .INSTANCE_NAME("PKT_PIPELINE")
) u_pkt_buffer (
    .axi_aclk    (pkt_clk),
    .axi_aresetn (pkt_resetn),

    .wr_valid    (ingress_pkt_valid),
    .wr_ready    (ingress_pkt_ready),
    .wr_data     (ingress_pkt),      // Direct struct assignment

    .rd_valid    (egress_pkt_valid),
    .rd_ready    (egress_pkt_ready),
    .rd_data     (egress_pkt),       // Direct struct output

    .count       (pkt_buf_depth),
    .rd_count    ()
);
```

### Example 3: Simple Data Array

```systemverilog
// Array of samples
typedef logic [15:0] sample_array_t [4];

gaxi_skid_buffer_struct #(
    .STRUCT_TYPE(sample_array_t),
    .DEPTH(4),
    .INSTANCE_NAME("SAMPLE_BUF")
) u_sample_buffer (
    .axi_aclk    (dsp_clk),
    .axi_aresetn (dsp_resetn),

    .wr_valid    (sample_valid),
    .wr_ready    (sample_ready),
    .wr_data     (sample_array),     // 4 x 16-bit samples

    .rd_valid    (proc_valid),
    .rd_ready    (proc_ready),
    .rd_data     (proc_array),

    .count       (sample_count),
    .rd_count    ()
);
```

---

## Behavior

### Identical to gaxi_skid_buffer

The internal behavior is **identical** to **[gaxi_skid_buffer](gaxi_skid_buffer.md)**:

1. **Shift Register:** Data stored in array, shifts on read
2. **Zero-Latency Bypass:** Empty buffer passes data combinatorially
3. **Valid/Ready Handshake:** Transfer occurs when `valid && ready`
4. **Backpressure:** `wr_ready` deasserts when full

### Key Difference: Type Safety

**gaxi_skid_buffer:**
```systemverilog
.DATA_WIDTH(96),           // Manual width calculation
.wr_data(packed_data),     // Manual packing required
.rd_data(packed_out)       // Manual unpacking required
```

**gaxi_skid_buffer_struct:**
```systemverilog
.STRUCT_TYPE(axi_ar_t),    // Type parameter
.wr_data(ar_struct),       // Direct struct assignment
.rd_data(ar_out_struct)    // Direct struct output
```

---

## Advantages Over Base Skid Buffer

### Advantage 1: Type Safety

```systemverilog
// Base skid buffer - error-prone
gaxi_skid_buffer #(.DATA_WIDTH(96)) u_buf (
    .wr_data({arid, araddr, arlen, ...})  // Easy to get field order wrong
);

// Struct buffer - compiler-checked
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_ar_t)) u_buf (
    .wr_data(ar_channel)  // Struct ensures correct fields
);
```

### Advantage 2: No Manual Width Calculation

```systemverilog
// Base: Must calculate width manually
localparam AR_WIDTH = 8 + 32 + 8 + 3 + 2 + 1 + 4 + 3 + 4;  // Error-prone

// Struct: Automatic using $bits()
localparam AR_WIDTH = $bits(axi_ar_t);  // Always correct
```

### Advantage 3: Cleaner Code

```systemverilog
// Before: Manual packing/unpacking
wire [95:0] packed_ar;
assign packed_ar = {arid, araddr, arlen, arsize, ...};
assign {slave_arid, slave_araddr, ...} = unpacked_ar;

// After: Direct struct assignment
axi_ar_t master_ar, slave_ar;
assign slave_ar = master_ar;  // Clean and readable
```

---

## Design Patterns

### Pattern 1: AXI Channel Buffering

```systemverilog
// Define all AXI channel structs
typedef struct packed {
    logic [ID_W-1:0]   awid;
    logic [ADDR_W-1:0] awaddr;
    // ... all AW signals
} axi_aw_t;

// Buffer each channel with appropriate type
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_aw_t)) u_aw_buf (...);
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_w_t))  u_w_buf  (...);
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_b_t))  u_b_buf  (...);
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_ar_t)) u_ar_buf (...);
gaxi_skid_buffer_struct #(.STRUCT_TYPE(axi_r_t))  u_r_buf  (...);
```

### Pattern 2: Pipeline Stages with Complex Data

```systemverilog
// Define pipeline stage struct
typedef struct packed {
    logic [31:0] instruction;
    logic [4:0]  rs1, rs2, rd;
    logic [31:0] imm;
    logic [6:0]  opcode;
    logic        valid;
} pipeline_stage_t;

// Each pipeline stage buffered
pipeline_stage_t fetch_stage, decode_stage, execute_stage;

gaxi_skid_buffer_struct #(
    .STRUCT_TYPE(pipeline_stage_t),
    .INSTANCE_NAME("FETCH_DECODE")
) u_fd_buf (
    .wr_data(fetch_stage),
    .rd_data(decode_stage),
    ...
);
```

---

## Testing

```bash
# Tests use parameterized structs
pytest val/amba/test_gaxi_skid_buffer_struct.py -v

# Test with different struct types
pytest val/amba/test_gaxi_skid_buffer_struct.py::test_axi_channel -v
pytest val/amba/test_gaxi_skid_buffer_struct.py::test_custom_struct -v
```

---

## Synthesis Notes

### Resource Usage

Same as **gaxi_skid_buffer** with equivalent DATA_WIDTH:
- Logic: ~50 LUTs (for DEPTH=4)
- Storage: DEPTH × $bits(STRUCT_TYPE) flip-flops
- No additional overhead from type parameter

### Type Requirements

**SystemVerilog types that work:**
- ✅ `struct packed` (recommended)
- ✅ Packed arrays: `logic [N:0][M:0]`
- ✅ Simple types: `logic [N:0]`
- ⚠️ `struct` (unpacked) - will be automatically packed by synthesis

**Not supported:**
- ❌ Dynamic types
- ❌ Classes
- ❌ Queues/associative arrays

---

## Related Modules

- **[gaxi_skid_buffer](gaxi_skid_buffer.md)** - Base implementation (DATA_WIDTH parameter)
- **[gaxi_fifo_sync](gaxi_fifo_sync.md)** - Synchronous FIFO alternative
- **[gaxi_skid_buffer_async](gaxi_skid_buffer_async.md)** - Clock domain crossing variant

---

## When to Use

**✅ Use gaxi_skid_buffer_struct When:**
- Working with complex data structures (AXI channels, custom packets)
- Want type safety and compiler checks
- Need cleaner, more readable code
- Struct definition already exists

**✅ Use gaxi_skid_buffer When:**
- Simple data widths (no complex structure)
- Need absolute minimum resource usage
- Working with legacy code that uses explicit widths

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to GAXI Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
