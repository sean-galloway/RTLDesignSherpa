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

# dataint_crc_xor_shift_cascade

## Overview

Eight instances of `dataint_crc_xor_shift`, chained back to back so a full byte of data gets chewed through in a single combinational operation. Byte in, updated CRC out — no clock involved.

### Module Declaration

```systemverilog
module dataint_crc_xor_shift_cascade #(
    parameter int CRC_WIDTH = 32
) (
    input  [CRC_WIDTH-1:0] block_input,
    input  [CRC_WIDTH-1:0] poly,
    input  [          7:0] data_input,
    output [CRC_WIDTH-1:0] block_output
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `CRC_WIDTH` | 32 | Width of the CRC register and polynomial |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `block_input` | Input | CRC_WIDTH | Initial CRC state for the byte |
| `poly` | Input | CRC_WIDTH | CRC polynomial |
| `data_input` | Input | 8 | 8-bit data byte to process |
| `block_output` | Output | CRC_WIDTH | Final CRC state after processing 8 bits |

## Functional Description

### Cascade Operation

Eight CRC calculation stages, chained end to end:
1. **Stage 0**: Processes the MSB of the data byte against the initial CRC state
2. **Stages 1-6**: Each processes the next data bit against the previous stage's output
3. **Stage 7**: Processes the LSB and produces the final result

### Data Bit Ordering

Data bits run MSB to LSB:
- `data_input[7]` is processed first
- `data_input[0]` is processed last
- This matches typical serial transmission order

### Architecture Overview

```
block_input → [Stage 0] → [Stage 1] → ... → [Stage 7] → block_output
              data[7]     data[6]           data[0]
```

### Generate Block Structure

The cascade is built from a parameterized generate block:

```systemverilog
generate
    for (i = 0; i < 8; i++) begin : gen_xor_shift_cascade
        if (i == 0) begin : gen_xor_shift_0
            // First stage uses block_input
            dataint_crc_xor_shift #(.CRC_WIDTH(CRC_WIDTH)) stage (
                .stage_input(block_input),
                .poly(poly),
                .new_bit(data_input[7-i]),
                .stage_output(w_cascade[i])
            );
        end else begin : gen_xor_shift_N
            // Subsequent stages chain previous output
            dataint_crc_xor_shift #(.CRC_WIDTH(CRC_WIDTH)) stage (
                .stage_input(w_cascade[i-1]),
                .poly(poly),
                .new_bit(data_input[7-i]),
                .stage_output(w_cascade[i])
            );
        end
    end
endgenerate
```

### Intermediate Signals

- **`w_cascade[0:7]`**: Array holding intermediate CRC states
- **Fixed Width**: Each element is `CRC_WIDTH` bits wide
- **Sequential Chain**: Each stage feeds the next

### Key Features

- **Parallel Byte Processing**: 8 bits in one combinational operation, no clock required — suitable for high-speed applications
- **Bit Order Handling**: MSB-first processing (network byte order), with the bit index calculated as `data_input[7-i]`, matching standard CRC bit processing order
- **Scalable Architecture**: Easy to modify for different byte sizes; generate blocks enable clean scaling, parameterized for different CRC widths

## Timing

### Combinational Delay

Total delay is the sum of 8 CRC stage delays:
- Each stage: ~2-3 gate delays
- Total cascade: ~16-24 gate delays
- May require pipelining for very high frequencies

Do that math against your clock period before you promise timing closure — 24 gate levels is not free at 400 MHz.

### Critical Path

The critical path runs through all 8 stages:

```
block_input → Stage0 → Stage1 → ... → Stage7 → block_output
```

## Usage Example

### Basic Usage

```systemverilog
dataint_crc_xor_shift_cascade #(
    .CRC_WIDTH(16)
) crc_byte_processor (
    .block_input(current_crc_state),
    .poly(16'h1021),           // CRC-16-CCITT
    .data_input(data_byte),
    .block_output(updated_crc_state)
);
```

### Multi-Byte Processing

```systemverilog
// Process 4 bytes (32 bits) of data
wire [CRC_WIDTH-1:0] stage_output[0:3];

genvar i;
generate
    for (i = 0; i < 4; i++) begin : gen_multi_byte
        dataint_crc_xor_shift_cascade #(.CRC_WIDTH(CRC_WIDTH)) cascade (
            .block_input(i == 0 ? initial_crc : stage_output[i-1]),
            .poly(polynomial),
            .data_input(data_bytes[i]),
            .block_output(stage_output[i])
        );
    end
endgenerate

assign final_crc = stage_output[3];
```

## Design Notes

### Performance Optimization

For high-frequency operation:
- Consider adding pipeline registers between cascades
- Balance latency vs. throughput requirements
- You may need to pipeline within the 8-stage cascade

For area:
- Each stage requires ~CRC_WIDTH XOR gates
- Total area scales with CRC_WIDTH × 8
- Consider time-multiplexed alternatives for area-critical applications

### Integration with the CRC System

This module is used by `dataint_crc` for:
- Processing data in byte-sized chunks
- Building wider data processing capability
- Maintaining processing efficiency

On the interface with the parent module:
- Multiple cascade instances handle wide data
- Cascade selection allows intermediate results
- Enables flexible data width support

### Applications

- High-speed packet processing
- Real-time data integrity checking
- Communication protocol implementations
- Storage system error detection
- Building block for wider CRC processors

## Related Modules

- **`dataint_crc_xor_shift`**: Single-bit processing building block
- **`dataint_crc`**: Parent CRC calculation module
- Used together to create flexible CRC calculation systems

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
