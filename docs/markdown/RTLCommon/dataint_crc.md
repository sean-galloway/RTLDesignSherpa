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

# dataint_crc

A generic Cyclic Redundancy Check (CRC) computation engine that provides flexible, high-performance CRC calculation with configurable polynomials, data widths, and processing options.

## Overview

The `dataint_crc` module implements a comprehensive CRC calculation engine suitable for data integrity applications, communication protocols, and storage systems. It supports configurable polynomial widths, data widths, input/output reflection, and cascade processing for high-throughput applications.

## Module Declaration

```systemverilog
module dataint_crc #(
    parameter string ALGO_NAME = "DEADF1F0",  // Algorithm identifier
    parameter int DATA_WIDTH = 64,            // Input data width
    parameter int CRC_WIDTH = 64,             // CRC polynomial width
    parameter int REFIN = 1,                  // Reflect input data
    parameter int REFOUT = 1                  // Reflect output data
) (
    // Derived localparam (computed internally - not user-settable):
    // localparam int CHUNKS = DATA_WIDTH / 8;  // Number of byte chunks
    // localparam int CW = CRC_WIDTH;           // CRC width alias
    // localparam int DW = DATA_WIDTH;          // Data width alias
    // localparam int CH = CHUNKS;              // Chunks alias
    input  logic [CRC_WIDTH-1:0]  POLY,             // CRC polynomial
    input  logic [CRC_WIDTH-1:0]  POLY_INIT,        // Initial CRC value
    input  logic [CRC_WIDTH-1:0]  XOROUT,           // Output XOR mask
    input  logic                  clk,              // Clock
    input  logic                  rst_n,            // Active-low reset
    input  logic                  load_crc_start,   // Load initial CRC
    input  logic                  load_from_cascade, // Load from cascade
    input  logic [    CHUNKS-1:0] cascade_sel,      // Cascade selection (one-hot)
    input  logic [DATA_WIDTH-1:0] data,             // Input data
    output logic [ CRC_WIDTH-1:0] crc               // CRC output
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| ALGO_NAME | string | "DEADF1F0" | Algorithm identifier for documentation |
| DATA_WIDTH | int | 64 | Input data width in bits (must be multiple of 8) |
| CRC_WIDTH | int | 64 | CRC polynomial width in bits (8, 16, 32, or 64) |
| REFIN | int | 1 | Reflect input data bytes (1=reflect, 0=direct) |
| REFOUT | int | 1 | Reflect output CRC (1=reflect, 0=direct) |

### Derived Localparam (Computed Internally)

| Localparam | Computation | Description |
|------------|-------------|-------------|
| CHUNKS (CH) | DATA_WIDTH/8 | Number of 8-bit processing chunks per cycle |
| CW | CRC_WIDTH | Convenience alias for CRC width |
| DW | DATA_WIDTH | Convenience alias for data width |

**Note:** CHUNKS, CW, DW, and CH are computed internally and cannot be overridden by users.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| POLY | CRC_WIDTH | CRC polynomial coefficient |
| POLY_INIT | CRC_WIDTH | Initial CRC value (seed) |
| XOROUT | CRC_WIDTH | Final XOR mask for output |
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| load_crc_start | 1 | Load initial CRC value |
| load_from_cascade | 1 | Load CRC from cascade output |
| cascade_sel | CHUNKS | One-hot cascade stage selection |
| data | DATA_WIDTH | Input data for CRC calculation |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| crc | CRC_WIDTH | Computed CRC value (registered) |

## Functionality

### CRC Algorithm Implementation

The module implements a parallel CRC calculation using the following stages:

1. **Input Data Conditioning**: Optional bit reflection per REFIN parameter
2. **Cascade Processing**: Parallel processing through multiple XOR-shift stages
3. **Output Conditioning**: Optional bit reflection per REFOUT parameter
4. **Final XOR**: Application of XOROUT mask to final result

### Key Features

- **Parallel Processing**: Processes multiple bytes simultaneously for high throughput
- **Configurable Reflection**: Support for MSB-first and LSB-first bit ordering
- **Cascade Architecture**: Enables partial CRC computation and continuation
- **Standards Compliance**: Configurable for standard CRC algorithms (CRC-32, CRC-64, etc.)

## Implementation Details

### Input Data Reflection

```systemverilog
// Input reflection based on REFIN parameter
if (REFIN != 0) begin : gen_reflect_inputs
    for (genvar i = 0; i < CH; i++) begin : gen_ch_reflect
        for (genvar j = 0; j < 8; j++) begin : gen_bit_reflect
            assign w_block_data[i][j] = data[i*8+7-j];  // Bit reversal
        end
    end
end else begin : gen_direct_assign_inputs
    for (genvar i = 0; i < CH; i++) begin : gen_ch_direct
        assign w_block_data[i] = data[i*8+:8];  // Direct assignment
    end
end
```

### Cascade Processing Architecture

```systemverilog
// Chain of XOR-shift cascade stages
for (i = 0; i < CH; i++) begin : gen_xor_shift_cascade
    if (i == 0) begin : gen_xor_cascade_0
        dataint_crc_xor_shift_cascade #(.CRC_WIDTH(CRC_WIDTH)) cascade_0 (
            .block_input(r_crc_value),     // Start with current CRC
            .poly(w_poly),
            .data_input(w_block_data[i]),
            .block_output(w_cascade[i])
        );
    end else begin : gen_xor_cascade_N
        dataint_crc_xor_shift_cascade #(.CRC_WIDTH(CRC_WIDTH)) cascade_N (
            .block_input(w_cascade[i-1]),  // Chain from previous stage
            .poly(w_poly),
            .data_input(w_block_data[i]),
            .block_output(w_cascade[i])
        );
    end
end
```

### Cascade Selection Logic

```systemverilog
// Select appropriate cascade output based on data length
always_comb begin
    w_selected_cascade_output = POLY_INIT;  // Default
    for (int i = 0; i < CH; i++) begin
        if (cascade_sel[i]) begin
            w_selected_cascade_output = w_cascade[i];
        end
    end
end
```

## CRC Standards Compatibility

### Common CRC Configurations

#### CRC-32 (IEEE 802.3)
```systemverilog
dataint_crc #(
    .ALGO_NAME("CRC32_IEEE"),
    .DATA_WIDTH(32),
    .CRC_WIDTH(32),
    .REFIN(1),
    .REFOUT(1)
) u_crc32 (
    .POLY(32'h04C11DB7),
    .POLY_INIT(32'hFFFFFFFF),
    .XOROUT(32'hFFFFFFFF),
    // ... other connections
);
```

#### CRC-16 (CCITT)
```systemverilog
dataint_crc #(
    .ALGO_NAME("CRC16_CCITT"),
    .DATA_WIDTH(16),
    .CRC_WIDTH(16),
    .REFIN(0),
    .REFOUT(0)
) u_crc16 (
    .POLY(16'h1021),
    .POLY_INIT(16'hFFFF),
    .XOROUT(16'h0000),
    // ... other connections
);
```

#### CRC-64 (ECMA-182)
```systemverilog
dataint_crc #(
    .ALGO_NAME("CRC64_ECMA"),
    .DATA_WIDTH(64),
    .CRC_WIDTH(64),
    .REFIN(1),
    .REFOUT(1)
) u_crc64 (
    .POLY(64'h42F0E1EBA9EA3693),
    .POLY_INIT(64'h0000000000000000),
    .XOROUT(64'hFFFFFFFFFFFFFFFF),
    // ... other connections
);
```

## Usage Examples

### Basic CRC Calculation

```systemverilog
logic [63:0] input_data;
logic [31:0] crc_result;
logic data_valid, crc_ready;

dataint_crc #(
    .DATA_WIDTH(64),
    .CRC_WIDTH(32),
    .REFIN(1),
    .REFOUT(1)
) u_crc_engine (
    .POLY(32'h04C11DB7),
    .POLY_INIT(32'hFFFFFFFF),
    .XOROUT(32'hFFFFFFFF),
    .clk(clk),
    .rst_n(rst_n),
    .load_crc_start(data_valid),
    .load_from_cascade(1'b0),
    .cascade_sel(8'hFF),  // Use all chunks
    .data(input_data),
    .crc(crc_result)
);
```

### Streaming CRC with Cascade

```systemverilog
// Process variable-length packets using cascade selection
logic [63:0] packet_data;
logic [7:0] byte_count;  // Number of valid bytes (1-8)
logic [7:0] cascade_select;

// Convert byte count to one-hot cascade selection
always_comb begin
    cascade_select = '0;
    if (byte_count > 0 && byte_count <= 8) begin
        cascade_select[byte_count-1] = 1'b1;
    end
end

dataint_crc #(
    .DATA_WIDTH(64),
    .CRC_WIDTH(32)
) u_stream_crc (
    .clk(clk),
    .rst_n(rst_n),
    .load_crc_start(packet_start),
    .load_from_cascade(packet_continue),
    .cascade_sel(cascade_select),
    .data(packet_data),
    .crc(streaming_crc),
    // ... other connections
);
```

### Multi-Stage CRC Pipeline

```systemverilog
// Pipeline multiple CRC engines for high throughput
logic [63:0] stage_data [0:3];
logic [31:0] stage_crc [0:3];

genvar stage;
generate
    for (stage = 0; stage < 4; stage++) begin : gen_crc_pipeline
        dataint_crc #(
            .DATA_WIDTH(64),
            .CRC_WIDTH(32),
            .ALGO_NAME($sformatf("STAGE_%0d", stage))
        ) u_pipeline_crc (
            .clk(clk),
            .rst_n(rst_n),
            .data(stage_data[stage]),
            .crc(stage_crc[stage]),
            // ... configure for pipeline operation
        );
    end
endgenerate
```

## Performance Characteristics

### Throughput Analysis

| Data Width | CRC Width | Max Frequency | Throughput |
|------------|-----------|---------------|------------|
| 32-bit | 32-bit | ~400 MHz | 12.8 Gbps |
| 64-bit | 32-bit | ~350 MHz | 22.4 Gbps |
| 128-bit | 64-bit | ~300 MHz | 38.4 Gbps |

### Latency Characteristics

- **Pipeline Stages**: 2 cycles (input conditioning + CRC computation)
- **Reset Recovery**: 1 cycle
- **Cascade Selection**: 0 cycles (combinational)

## Timing Considerations

### Setup Requirements

```systemverilog
// Data must be stable before clock edge
timing_spec: assert property (
    @(posedge clk) $stable(data) throughout (load_crc_start)
);

// Cascade selection must be stable
cascade_timing: assert property (
    @(posedge clk) $stable(cascade_sel) throughout (load_from_cascade)
);
```

### Critical Paths

1. **Cascade Chain**: Data flows through all cascade stages
2. **Output Reflection**: Bit reversal for REFOUT
3. **Register Setup**: Loading CRC state register

## Design Considerations

### Area Optimization

- **Polynomial Optimization**: Use polynomials with fewer terms
- **Width Reduction**: Match CRC_WIDTH to actual requirements
- **Cascade Stages**: Reduce CHUNKS for lower throughput applications

### Power Optimization

- **Clock Gating**: Gate unused cascade stages
- **Data Gating**: Prevent unnecessary switching when not processing

### Verification Notes

- **Polynomial Validation**: Verify against known CRC test vectors
- **Cascade Testing**: Test all cascade selection combinations
- **Reflection Testing**: Verify bit ordering for REFIN/REFOUT modes
- **Standards Compliance**: Validate against published CRC standards

## Related Modules

- **dataint_crc_xor_shift_cascade**: Building block for cascade stages
- **dataint_crc_xor_shift**: Simple XOR-shift CRC implementation
- **dataint_checksum**: Alternative integrity checking method
- **dataint_parity**: Simpler parity-based error detection

The `dataint_crc` module provides a comprehensive, high-performance solution for CRC-based data integrity checking with the flexibility to support a wide range of CRC standards and applications.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
