# Gray-to-Binary Converter (`gray2bin.sv`)

## Purpose
Converts Gray code (reflected binary code) to standard binary representation using XOR reduction. Essential component for asynchronous FIFO pointer comparison and other CDC applications.

## Ports

### Input Ports
- **`gray[WIDTH-1:0]`** - Gray code input

### Output Ports
- **`binary[WIDTH-1:0]`** - Binary code output

### Parameters
- **`WIDTH`** - Data width in bits (default: 4)

## Gray Code Theory

### What is Gray Code?
Gray code (also called reflected binary code) is a binary numeral system where **only one bit changes** between consecutive values:

```
Binary  Gray   Transitions
000  →  000    
001  →  001    1 bit change
010  →  011    1 bit change  
011  →  010    1 bit change
100  →  110    1 bit change
101  →  111    1 bit change
110  →  101    1 bit change
111  →  100    1 bit change
```

### Why Gray Codes Matter for CDC
- **Metastability protection**: Only one bit transition eliminates multi-bit race conditions
- **Safe sampling**: Intermediate values during transition are still valid Gray codes
- **FIFO pointers**: Essential for async FIFO full/empty detection

## Conversion Algorithm

### Mathematical Foundation
For Gray-to-binary conversion, each binary bit is the XOR of all Gray bits from that position to the MSB:

```
binary[i] = gray[MSB] ⊕ gray[MSB-1] ⊕ ... ⊕ gray[i]
```

### Implementation
```systemverilog
genvar i;
generate
    for (i = 0; i < WIDTH; i++) begin : gen_gray_to_bin
        assign binary[i] = ^(gray >> i);
    end
endgenerate
```

### Bit-by-Bit Breakdown
```systemverilog
// For 4-bit example:
assign binary[3] = gray[3];                           // MSB unchanged
assign binary[2] = gray[3] ^ gray[2];                 // XOR from MSB down
assign binary[1] = gray[3] ^ gray[2] ^ gray[1];       // XOR from MSB down  
assign binary[0] = gray[3] ^ gray[2] ^ gray[1] ^ gray[0]; // XOR all bits
```

## Functional Examples

### 4-Bit Conversion Table
| Gray[3:0] | Binary[3:0] | Calculation |
|-----------|-------------|-------------|
| 0000      | 0000        | 0⊕0⊕0⊕0=0, 0⊕0⊕0=0, 0⊕0=0, 0=0 |
| 0001      | 0001        | 0⊕0⊕0⊕1=1, 0⊕0⊕0=0, 0⊕0=0, 0=0 |
| 0011      | 0010        | 0⊕0⊕1⊕1=0, 0⊕0⊕1=1, 0⊕0=0, 0=0 |
| 0010      | 0011        | 0⊕0⊕1⊕0=1, 0⊕0⊕1=1, 0⊕0=0, 0=0 |
| 0110      | 0100        | 0⊕1⊕1⊕0=0, 0⊕1⊕1=0, 0⊕1=1, 0=0 |
| 0111      | 0101        | 0⊕1⊕1⊕1=1, 0⊕1⊕1=0, 0⊕1=1, 0=0 |
| 0101      | 0110        | 0⊕1⊕0⊕1=0, 0⊕1⊕0=1, 0⊕1=1, 0=0 |
| 0100      | 0111        | 0⊕1⊕0⊕0=1, 0⊕1⊕0=1, 0⊕1=1, 0=0 |

### Step-by-Step Example (Gray 0110 → Binary)
```
Gray input: 0110

binary[3] = gray[3] = 0
binary[2] = gray[3] ^ gray[2] = 0 ^ 1 = 1  
binary[1] = gray[3] ^ gray[2] ^ gray[1] = 0 ^ 1 ^ 1 = 0
binary[0] = gray[3] ^ gray[2] ^ gray[1] ^ gray[0] = 0 ^ 1 ^ 1 ^ 0 = 0

Result: binary = 0100 (decimal 4)
```

## Implementation Analysis

### XOR Reduction Technique
```systemverilog
assign binary[i] = ^(gray >> i);
```

**How it works:**
- `gray >> i`: Right-shift gray by i positions
- `^(...)`: XOR-reduce all bits in the shifted value
- **Effect**: XORs all bits from position i to MSB

### Generate Loop Benefits
- **Parameterizable**: Works for any WIDTH
- **Synthesis friendly**: Tools recognize and optimize pattern
- **Parallel computation**: All bits calculated simultaneously
- **Resource efficient**: Maps to XOR tree structures

## Use Cases in Digital Design

### Asynchronous FIFO Pointers
```systemverilog
// Convert synchronized Gray pointers back to binary for comparison
gray2bin #(.WIDTH(5)) wr_ptr_conv (
    .gray(sync_wr_ptr_gray),
    .binary(sync_wr_ptr_bin)
);

gray2bin #(.WIDTH(5)) rd_ptr_conv (
    .gray(sync_rd_ptr_gray),  
    .binary(sync_rd_ptr_bin)
);

// Now can perform binary arithmetic for occupancy calculation
assign occupancy = sync_wr_ptr_bin - sync_rd_ptr_bin;
```

### Clock Domain Crossing Counters
```systemverilog
// Convert Gray counter back to binary for address generation
gray2bin #(.WIDTH(AW)) addr_converter (
    .gray(gray_counter),
    .binary(memory_address)
);
```

### Position Encoding
```systemverilog
// Convert Gray-encoded position to binary for processing
gray2bin #(.WIDTH(8)) position_decoder (
    .gray(gray_position),
    .binary(bin_position)
);
```

## Timing Characteristics

### Propagation Delay
- **XOR tree depth**: `log2(WIDTH)` levels
- **Typical delay**: 1-2 LUT delays for most widths
- **Critical path**: From MSB input to LSB output

### Delay Analysis by Width
| WIDTH | XOR Levels | Typical Delay |
|-------|------------|---------------|
| 4     | 2          | 1 LUT delay   |
| 8     | 3          | 2 LUT delays  |
| 16    | 4          | 2 LUT delays  |
| 32    | 5          | 3 LUT delays  |

### Synthesis Optimization
Modern synthesis tools:
- **Recognize pattern**: Optimize XOR reduction automatically
- **Balance trees**: Create balanced XOR structures
- **Resource sharing**: Reuse XOR gates where possible

## Design Considerations

### Width Scaling
- **Linear resource growth**: XOR gates increase with WIDTH
- **Logarithmic delay growth**: Delay scales with log(WIDTH)
- **Practical limits**: Works well up to 64+ bits

### Input Validation
```systemverilog
// Gray codes have no invalid states - all inputs are valid
// However, may want to validate source of Gray code
always_comb begin
    if (gray_code_valid) begin
        binary_out = converted_binary;
    end else begin
        binary_out = '0;  // Default when invalid
    end
end
```

### Pipeline Considerations
For very high-speed applications:
```systemverilog
// Optional pipeline stage for timing closure
always_ff @(posedge clk) begin
    if (!rst_n) begin
        binary_reg <= '0;
    end else begin
        binary_reg <= binary_comb;
    end
end
```

## Verification Strategies

### Exhaustive Testing
```systemverilog
// For reasonable widths, test all possible inputs
for (int i = 0; i < (1 << WIDTH); i++) begin
    gray_input = int_to_gray(i);      // Convert integer to Gray
    expected_binary = i;              // Expected result
    #1;
    assert(binary_output == expected_binary);
end
```

### Property-Based Verification
```systemverilog
// Verify round-trip conversion
property round_trip;
    @(posedge clk) 
    binary_output == original_binary;
endproperty

// Apply after binary→Gray→binary conversion
assert property (round_trip);
```

### Random Testing
```systemverilog
repeat (10000) begin
    random_gray = $random();
    expected_result = reference_gray2bin(random_gray);
    #1;
    assert(binary_output == expected_result);
end
```

## Common Mistakes and Pitfalls

### Bit Order Confusion
```systemverilog
// WRONG: Bit order matters in Gray codes
assign binary[i] = ^(gray << i);  // Left shift instead of right

// CORRECT:
assign binary[i] = ^(gray >> i);  // Right shift
```

### Width Mismatches
```systemverilog
// WRONG: Input/output width mismatch
gray2bin #(.WIDTH(4)) converter (
    .gray(gray_5bit),     // 5-bit input
    .binary(binary_4bit)  // 4-bit output
);

// CORRECT: Match widths
gray2bin #(.WIDTH(5)) converter (
    .gray(gray_5bit),
    .binary(binary_5bit)
);
```

### Timing Assumptions
```systemverilog
// WRONG: Assuming zero delay
gray_in <= new_value;
binary_out <= converted_value;  // May not be updated yet

// CORRECT: Account for combinational delay
gray_in <= new_value;
#1;  // Wait for conversion
binary_out <= converted_value;
```

## Related Modules
- **bin2gray**: Performs inverse conversion (binary to Gray)
- **counter_bingray**: Combined binary/Gray counter
- **fifo_async**: Uses Gray codes for CDC
- **grayj2bin**: Johnson counter to binary converter (different algorithm)

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
