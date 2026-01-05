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

# dataint_crc_xor_shift Module Documentation

## Purpose
The `dataint_crc_xor_shift` module performs CRC calculation for a single bit of input data. It implements the fundamental CRC operation: shifting the current CRC state and XORing with the polynomial when the feedback bit is set.

## Module Declaration
```systemverilog
module dataint_crc_xor_shift #(
    parameter int CRC_WIDTH = 32
) (
    input [CRC_WIDTH-1:0] stage_input,
    input [CRC_WIDTH-1:0] poly,
    input new_bit,
    output [CRC_WIDTH-1:0] stage_output
);
```

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| `CRC_WIDTH` | 32 | Width of the CRC register and polynomial |

## Ports
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `stage_input` | Input | CRC_WIDTH | Current CRC state |
| `poly` | Input | CRC_WIDTH | CRC polynomial |
| `new_bit` | Input | 1 | New data bit to process |
| `stage_output` | Output | CRC_WIDTH | Updated CRC state |

## Functionality

### Core CRC Operation
The module implements the basic CRC shift-and-XOR operation:
1. **Feedback Calculation**: XOR the new input bit with the MSB of current CRC
2. **Shift Operation**: Shift CRC register left by one position
3. **Polynomial XOR**: If feedback bit is 1, XOR with polynomial

### Mathematical Foundation
The CRC operation follows this algorithm:
```
feedback = new_bit ⊕ CRC[MSB]
CRC_new[0] = feedback
CRC_new[MSB:1] = CRC[MSB-1:0] ⊕ (polynomial[MSB:1] & {WIDTH-1{feedback}})
```

## Implementation Details

### Key Features
- **Single Bit Processing**: Processes exactly one bit per operation
- **Combinational Logic**: Pure combinational implementation (no clock)
- **Parameterizable Width**: Supports any CRC width
- **Optimized Design**: Breaks circular dependency with intermediate signal

### Circular Dependency Solution
The original implementation could have a circular dependency. This is solved by:
```systemverilog
logic feedback_bit;

// Calculate feedback first
assign feedback_bit = new_bit ^ stage_input[CRC_WIDTH-1];

// Then use it for output calculation
assign stage_output[0] = feedback_bit;
assign stage_output[CRC_WIDTH-1:1] = stage_input[CRC_WIDTH-2:0] ^ 
    ({CRC_WIDTH-1{feedback_bit}} & poly[CRC_WIDTH-1:1]);
```

### Bit-wise Operations
- **LSB Assignment**: Always gets the feedback bit
- **MSBs Assignment**: Shifted previous bits XORed with polynomial when feedback is active
- **Conditional XOR**: Uses bit replication to create conditional XOR mask

## Special Implementation Features

### Feedback Bit Logic
The feedback bit is critical for CRC operation:
- Determines whether polynomial is applied
- Calculated as XOR of input bit and current MSB
- Used to gate polynomial application

### Polynomial Application
The polynomial is applied conditionally:
- Only bits [MSB:1] of polynomial are used (bit 0 is implicit)
- Applied via AND mask created by replicating feedback bit
- XORed with shifted CRC bits

### No State Elements
This module is purely combinational:
- No clock or reset signals needed
- Instantaneous response to input changes
- Can be cascaded for multi-bit processing

## Usage in CRC Chain
This module is typically used as a building block:

### Single Bit Processing
```systemverilog
dataint_crc_xor_shift #(.CRC_WIDTH(16)) crc_stage (
    .stage_input(current_crc),
    .poly(crc_polynomial),
    .new_bit(data_bit),
    .stage_output(next_crc)
);
```

### Cascaded for Multiple Bits
Multiple instances can be chained to process multiple bits:
```systemverilog
// Process 8 bits
wire [CRC_WIDTH-1:0] stage[0:7];
assign stage[0] = initial_crc;

genvar i;
generate
    for (i = 0; i < 8; i++) begin
        dataint_crc_xor_shift #(.CRC_WIDTH(CRC_WIDTH)) stage_inst (
            .stage_input(i == 0 ? initial_crc : stage[i-1]),
            .poly(polynomial),
            .new_bit(data_byte[7-i]),
            .stage_output(stage[i])
        );
    end
endgenerate

assign final_crc = stage[7];
```

## Mathematical Verification
For a polynomial P(x) and data bit d:
- If feedback = 0: Simple left shift
- If feedback = 1: Left shift XOR polynomial

This implements the mathematical CRC division in hardware.

## Applications
- Building block for CRC calculation engines
- Serial CRC processors
- Component in parallel CRC architectures
- Educational CRC implementations
- Custom protocol CRC calculators

## Performance Characteristics
- **Latency**: Combinational (zero clock cycles)
- **Throughput**: One bit per clock when used in sequential system
- **Area**: Minimal - few XOR gates and multiplexers
- **Power**: Low - simple combinational logic

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
