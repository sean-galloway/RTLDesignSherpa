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

# reverse_vector

## Overview

The `reverse_vector` module flips the bit order of an input vector end for end:
MSB swaps with LSB, second MSB with second LSB, and so on down the line. It's a
purely combinational operation — no clock, no state, just wires with an opinion
about ordering.

- Combinational bit reversal operation
- Parameterizable vector width
- Zero propagation delay (combinational logic only)
- No clock or reset required

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | — | 32 | Width of the input/output vectors |

## Ports

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `vector_in` | WIDTH | Input vector to be reversed |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `vector_rev` | WIDTH | Bit-reversed output vector |

## Functional Description

### Bit Reversal Logic
```systemverilog
always_comb begin
    for (integer i = 0; i < WIDTH; i++) begin
        vector_rev[(WIDTH-1)-i] = vector_in[i];
    end
end
```

A simple for-loop maps each input bit to its mirrored output position:
- Input bit 0 → Output bit (WIDTH-1)
- Input bit 1 → Output bit (WIDTH-2)
- Input bit i → Output bit (WIDTH-1-i)
- Input bit (WIDTH-1) → Output bit 0

### 8-bit Vector Reversal
```
Input:  vector_in  = 8'b10110001
Output: vector_rev = 8'b10001101

Bit mapping:
vector_in[7] = 1 → vector_rev[0] = 1
vector_in[6] = 0 → vector_rev[1] = 0  
vector_in[5] = 1 → vector_rev[2] = 1
vector_in[4] = 1 → vector_rev[3] = 1
vector_in[3] = 0 → vector_rev[4] = 0
vector_in[2] = 0 → vector_rev[5] = 0
vector_in[1] = 0 → vector_rev[6] = 0
vector_in[0] = 1 → vector_rev[7] = 1
```

### 4-bit Vector Reversal
```
Input:  vector_in  = 4'b1011
Output: vector_rev = 4'b1101

Bit mapping:
vector_in[3] = 1 → vector_rev[0] = 1
vector_in[2] = 0 → vector_rev[1] = 0
vector_in[1] = 1 → vector_rev[2] = 1  
vector_in[0] = 1 → vector_rev[3] = 1
```

## Timing Characteristics
There is no clock and no state here, so timing in the usual sense doesn't
apply. The output follows the input after gate and wire delay, and that's the
whole story:

- **Propagation Delay**: Minimal (wire delay only), < 1ns typical
- **Critical Path**: Direct wire connections
- **Setup/Hold**: Not applicable (combinational)
- **Maximum Frequency**: Unlimited by this module — limited by surrounding logic
- **Throughput**: One operation per clock cycle (if clocked)

## Usage Examples

### Endianness Conversion
```systemverilog
// Convert between big-endian and little-endian bit ordering
little_endian_data = reverse_vector(big_endian_data);
```

### Serial Communication
```systemverilog
// Reverse bit order for serial transmission protocols
// that send LSB first instead of MSB first
serial_data = reverse_vector(parallel_data);
```

### Cryptographic Operations
```systemverilog
// Bit permutation operations in encryption algorithms
permuted_key = reverse_vector(encryption_key);
```

### Signal Processing
```systemverilog
// Bit-reversed addressing for FFT algorithms
reversed_address = reverse_vector(sequential_address);
```

### Data Format Conversion
```systemverilog
// Convert between different data representation formats
converted_data = reverse_vector(input_format);
```

### Mirror Pattern Generation
```systemverilog
// Create mirror patterns for display or test applications
mirror_pattern = reverse_vector(original_pattern);
```

### Instantiation with Different Widths
```systemverilog
// 16-bit reversal
reverse_vector #(.WIDTH(16)) rev16 (
    .vector_in(data_16bit),
    .vector_rev(reversed_16bit)
);

// 64-bit reversal  
reverse_vector #(.WIDTH(64)) rev64 (
    .vector_in(data_64bit),
    .vector_rev(reversed_64bit)
);
```

### Pipeline Integration
```systemverilog
// Use in data processing pipeline
always_ff @(posedge clk) begin
    stage1_data <= input_data;
    stage2_data <= reverse_vector_inst.vector_rev;
    stage3_data <= process(stage2_data);
end
```

### Conditional Reversal
```systemverilog
// Conditional bit reversal based on control signal
assign output_data = reverse_enable ? 
                     reverse_vector_inst.vector_rev : 
                     vector_in;
```

## Design Notes

### 1. Combinational Operation
- No clock signal required
- No sequential logic elements
- Output changes immediately when input changes
- Zero propagation delay (limited only by gate delays)

### 2. Parameterizable Width
The module works with any vector width specified by the WIDTH parameter:
- Automatically scales to any desired width
- Synthesis tools optimize for the specific width
- No hardcoded bit indices

### 3. For-Loop Synthesis
Synthesis unrolls the for-loop completely, leaving one wire assignment per bit
position. What you get:
- Parallel bit assignments (no sequential operation)
- Optimal timing characteristics
- Efficient hardware implementation

### 4. Bidirectional Property
Reverse twice and you're back where you started:
```systemverilog
original_vector == reverse(reverse(original_vector))
```

### Power Consumption
- **Static Power**: Minimal (no storage elements)
- **Dynamic Power**: Only during input transitions
- **Switching Activity**: Proportional to input bit toggles

### Area Utilization
- **Logic Elements**: Zero (pure routing)
- **Routing Resources**: WIDTH wire connections
- **Memory**: None required
- **Scalability**: Linear with WIDTH

### Hardware Implementation
What synthesis actually builds:
- Direct wire connections from input bits to output bits
- No logic gates required (just routing)
- Minimal area overhead
- Excellent timing characteristics

### Optimization
```systemverilog
// Synthesis tools will optimize this to simple wire assignments:
assign vector_rev[WIDTH-1] = vector_in[0];
assign vector_rev[WIDTH-2] = vector_in[1];
// ...
assign vector_rev[1] = vector_in[WIDTH-2];
assign vector_rev[0] = vector_in[WIDTH-1];
```

### Performance Metrics

Area:
- **Gate Count**: 0 (wire-only implementation)
- **Equivalent Gates**: WIDTH (for routing complexity)
- **Memory Bits**: 0

Power:
- **Leakage**: Negligible
- **Dynamic**: Proportional to toggle rate
- **Peak Power**: During simultaneous bit transitions

### Common Pitfalls

Simulation warnings:
```systemverilog
// Use 'integer' instead of 'int' for compatibility
for (integer i = 0; i < WIDTH; i++) begin
```

Synthesis issues:
```systemverilog
// Ensure WIDTH is properly parameterized
localparam int W = WIDTH;  // Local parameter for clarity
```

Timing closure:
```systemverilog
// Add pipeline stage if needed for timing
always_ff @(posedge clk) begin
    vector_rev_reg <= vector_rev;
end
```

## Related Modules

### Byte Reversal
If what you actually need is byte-level endianness conversion, a separate module
is the better tool:
```systemverilog
// Reverse byte order instead of bit order
assign byte_reversed = {data[7:0], data[15:8], data[23:16], data[31:24]};
```

### Configurable Reversal
An enhanced version could add an enable:
```systemverilog
assign vector_out = enable ? vector_rev : vector_in;
```

### Multi-Width Reversal
Support multiple data widths in a single module:
```systemverilog
generate
    case (WIDTH)
        8: assign vector_rev = {vector_in[0], vector_in[1], ...};
        16: assign vector_rev = {vector_in[0], vector_in[1], ...};
        32: assign vector_rev = {vector_in[0], vector_in[1], ...};
    endcase
endgenerate
```

## Testing

### Test Cases
```systemverilog
// Test all zeros
vector_in = '0;
assert(vector_rev == '0);

// Test all ones  
vector_in = '1;
assert(vector_rev == '1);

// Test alternating pattern
vector_in = 8'b10101010;
assert(vector_rev == 8'b01010101);

// Test double reversal
temp = reverse_vector_inst1.vector_rev;
assert(reverse_vector_inst2.vector_rev == vector_in);
```

### Coverage Points
- All bit positions exercised
- Boundary conditions (all 0s, all 1s)
- Random patterns
- Double reversal verification

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
