# Decoder Module (`decoder.sv`)

## Purpose
Converts an M-bit binary encoded input to a one-hot N-bit output where N = 2^M. This is a standard binary-to-one-hot decoder implementation.

## Ports

### Input Ports
- **`encoded[M-1:0]`** - Binary encoded input value

### Output Ports  
- **`data[N-1:0]`** - One-hot decoded output vector

### Parameters
- **`M`** - Width of binary input (default: 4)
- **`N`** - Width of one-hot output (default: 2^M = 16)

## Implementation Details

### Core Logic
The decoder uses a generate loop to create comparison logic for each output bit:

```systemverilog
assign data = 0;  // Initialize all outputs to 0

genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_DECODER_LOOP
        assign data[i] = (encoded == i) ? 1'b1 : 1'b0;
    end
endgenerate
```

### Operation Principle
- Each output bit corresponds to one possible input value
- Only one output bit is high at any time (one-hot encoding)
- Output bit `i` is high when `encoded` input equals `i`

## Functional Behavior

### Truth Table Example (M=2, N=4)
| encoded[1:0] | data[3] | data[2] | data[1] | data[0] |
|--------------|---------|---------|---------|---------|
| 00           | 0       | 0       | 0       | 1       |
| 01           | 0       | 0       | 1       | 0       |
| 10           | 0       | 1       | 0       | 0       |
| 11           | 1       | 0       | 0       | 0       |

### Key Characteristics
- **Combinational logic**: No clock dependency, immediate response
- **One-hot output**: Exactly one bit high for valid inputs
- **Complete decoding**: All possible input combinations decoded
- **Default initialization**: All outputs start at 0

## Design Features

### Parameterization
- **Scalable width**: M parameter controls input width
- **Automatic sizing**: N automatically calculated as 2^M
- **Generate loops**: Synthesizes efficiently for any size

### Synthesis Considerations
- **Resource usage**: Typically implements as LUT-based logic
- **Propagation delay**: Single LUT delay in most FPGA architectures  
- **Fan-out**: Each input bit fans out to multiple output comparisons

## Use Cases
- **Address decoding**: Memory or register select signals
- **State machine outputs**: Decode binary state to control signals
- **Multiplexer control**: Generate select signals for data routing
- **Interrupt controllers**: Decode interrupt vectors
- **Bus decoding**: Generate chip select signals

## Common Applications

### Memory Address Decoding
```systemverilog
decoder #(.M(2), .N(4)) addr_decoder (
    .encoded(address[1:0]),
    .data(chip_select)  // 4 chip selects
);
```

### State Machine Output Decoding
```systemverilog
decoder #(.M(3), .N(8)) state_decoder (
    .encoded(current_state),
    .data(state_outputs)  // 8 control signals
);
```

## Timing Characteristics
- **Propagation delay**: Typically 1 LUT delay
- **Setup/hold**: None (purely combinational)
- **Output changes**: Immediately follow input changes

## Related Modules
- **Encoder**: Performs inverse operation (one-hot to binary)
- **Priority Encoder**: Handles multiple simultaneous inputs
- **Multiplexer**: Often used together for data routing

## Design Notes
- No error checking for invalid inputs (though all combinations are valid)
- Output initialization ensures clean power-up behavior
- Generate loop structure scales efficiently to any required size

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
