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

# decoder

## Overview

Converts an M-bit binary encoded input to a one-hot N-bit output where N = 2^M. Standard binary-to-one-hot decoding — nothing exotic.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `M` | 4 | Width of binary input |
| `N` | 2^M = 16 | Width of one-hot output |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `encoded` | Input | M | Binary encoded input value |
| `data` | Output | N | One-hot decoded output vector |

## Functional Description

### Operation Principle

- Each output bit maps to one possible input value
- Only one output bit is high at any time (that's the one-hot part)
- Output bit `i` is high when the `encoded` input equals `i`

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
- **No default initialization**: because `N = 2^M` covers every input value, exactly one output is high at all times — the outputs are never all-zero, and the RTL contains no default assignment

### Core Logic

A generate loop spins up one comparator per output bit:

```systemverilog
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_DECODER_LOOP
        assign data[i] = (encoded == i) ? 1'b1 : 1'b0;
    end
endgenerate
```

### Parameterization

- **Scalable width**: M sets the input width
- **Automatic sizing**: N falls out as 2^M
- **Generate loops**: Synthesizes cleanly for any size

## Timing Characteristics
- **Setup/hold**: None (purely combinational)
- **Output changes**: Follow the inputs immediately

## Usage Examples

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

## Design Notes

### Applications

- **Address decoding**: Memory or register select signals
- **State machine outputs**: Decode binary state to control signals
- **Multiplexer control**: Generate select signals for data routing
- **Interrupt controllers**: Decode interrupt vectors
- **Bus decoding**: Generate chip select signals

### Synthesis Considerations

- **Resource usage**: Typically lands in LUT-based logic
- **Propagation delay**: Single LUT delay in most FPGA architectures
- **Fan-out**: Each input bit feeds multiple output comparisons

### Other Notes

- No error checking for invalid inputs (though all combinations are valid)
- Purely combinational: the generate loop drives every `data[i]` exactly once,
  so all outputs are defined at all times (no separate initialization needed —
  and none exists in the RTL)
- The generate loop structure scales efficiently to any required size

## Related Modules

- **Encoder**: Performs inverse operation (one-hot to binary)
- **Priority Encoder**: Handles multiple simultaneous inputs
- **Multiplexer**: Often used together for data routing

## Testing

`val/common/test_decoder.py` exercises this module. It collects 3 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/common/test_decoder.py -v
```

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
