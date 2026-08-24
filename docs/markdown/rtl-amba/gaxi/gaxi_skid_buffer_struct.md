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
**Status:** Production Ready

---

## Overview

Struct-aware variant of **[gaxi_skid_buffer](gaxi_skid_buffer.md)** — it takes a SystemVerilog type parameter instead of an explicit data width. If your payload is a complex data structure (an AXI channel, a custom packet), this gives you clean handling without manual packing and unpacking.

### Key Features

- **Type-Parameterized:** Accepts any SystemVerilog type (struct, union, enum, packed array)
- **Automatic Width Calculation:** Uses `$bits()` to determine buffer width
- **Registered Output:** Identical latency to the base skid buffer (1 clock)
- **Same Architecture:** Shift register with valid/ready flow control
- **Debug Support:** INSTANCE_NAME parameter for waveform/error identification (no transaction logging in the RTL)

---

## Module Interface

```systemverilog
module gaxi_skid_buffer_struct #(
    parameter type STRUCT_TYPE = logic [31:0],  // Any SystemVerilog type
    parameter int  DEPTH = 2,                   // Must be {2, 4, 6, 8}

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

---

## Ports

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `axi_aclk` | input | 1 | Clock |
| `axi_aresetn` | input | 1 | Active-low asynchronous reset |

### Write Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `wr_valid` | input | 1 | Write data valid |
| `wr_ready` | output | 1 | Ready to accept write |
| `wr_data` | input | STRUCT_TYPE | Input data (type-safe) |

### Read Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `rd_valid` | output | 1 | Read data valid |
| `rd_ready` | input | 1 | Ready to consume read |
| `rd_data` | output | STRUCT_TYPE | Output data (type-safe) |

### Status

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `count` | output | 4 | Current buffer occupancy (0 to DEPTH) |
| `rd_count` | output | 4 | Same as count (for compatibility) |

---

## Functional Description

### Identical to gaxi_skid_buffer

The internal behavior is **identical** to **[gaxi_skid_buffer](gaxi_skid_buffer.md)**:

1. **Shift Register:** Data stored in array, shifts on read
2. **Registered Output:** `rd_data` is driven from a flop; minimum latency 1 clock
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
    .DEPTH(4)

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
    .DEPTH(8)

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
    .DEPTH(4)

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

### Example 4: AXI Channel Buffering

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

### Example 5: Pipeline Stages with Complex Data

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
    .STRUCT_TYPE(pipeline_stage_t)

) u_fd_buf (
    .wr_data(fetch_stage),
    .rd_data(decode_stage),
    ...
);
```

---

## Design Notes

### Resource Usage

Same as **gaxi_skid_buffer** with equivalent DATA_WIDTH:
- Logic: ~50 LUTs (for DEPTH=4)
- Storage: DEPTH × $bits(STRUCT_TYPE) flip-flops
- No additional overhead from type parameter

### Type Requirements

**SystemVerilog types that work:**
- `struct packed` (recommended)
- Packed arrays: `logic [N:0][M:0]`
- Simple types: `logic [N:0]`
- Caveat: `struct` (unpacked) - will be automatically packed by synthesis

**Not supported:**
- Dynamic types
- Classes
- Queues/associative arrays

---

## Testing

**This module has no test of its own.** The commands that used to stand here
named a `test_gaxi_skid_buffer_struct.py` that has never existed. The closest
coverage is the packed-vector sibling:

```bash
pytest val/amba/test_gaxi_skid_buffer.py -v
```

That exercises the same handshake and depth logic; what it does not exercise is
the struct packing/unpacking this module adds. Treat that as unverified.

---

## Comparison with the Base Skid Buffer

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

### When to Use

**Use gaxi_skid_buffer_struct When:**
- Working with complex data structures (AXI channels, custom packets)
- Want type safety and compiler checks
- Need cleaner, more readable code
- Struct definition already exists

**Use gaxi_skid_buffer When:**
- Simple data widths (no complex structure)
- Need absolute minimum resource usage
- Working with legacy code that uses explicit widths

---

## Related Modules

- **[gaxi_skid_buffer](gaxi_skid_buffer.md)** - Base implementation (DATA_WIDTH parameter)
- **[gaxi_fifo_sync](gaxi_fifo_sync.md)** - Synchronous FIFO alternative
- **[gaxi_skid_buffer_async](../../rtl-cdc/gaxi_skid_buffer_async.md)** - Clock domain crossing variant

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to GAXI Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
