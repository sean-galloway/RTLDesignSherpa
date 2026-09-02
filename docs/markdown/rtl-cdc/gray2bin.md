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

# Gray-to-binary converter (`gray2bin.sv`)

## Overview

`gray2bin` converts Gray code (reflected binary code) back to standard binary
using XOR reduction. When a Gray pointer crosses into a domain that needs to do
arithmetic on it, this is the module that turns it back into a number --
asynchronous FIFO pointer comparison is the classic case, and it shows up in
plenty of other CDC paths too.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `WIDTH` | 4 | Data width in bits |

: gray2bin parameters

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `gray` | input | WIDTH | Gray code input |
| `binary` | output | WIDTH | Binary code output |

: gray2bin ports

## Functional Description

Gray code is a binary numeral system where **only one bit changes** between
consecutive values:

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

That property is exactly what CDC needs:

- **Metastability protection**: only one bit in transition means no multi-bit
  race conditions
- **Safe sampling**: intermediate values during a transition are still valid
  Gray codes
- **FIFO pointers**: essential for async FIFO full/empty detection

### Conversion algorithm

Each binary bit is the XOR of all Gray bits from that position up to the MSB:

```
binary[i] = gray[MSB] ⊕ gray[MSB-1] ⊕ ... ⊕ gray[i]
```

The RTL says the same thing with a shift and a reduction:

```systemverilog
genvar i;
generate
    for (i = 0; i < WIDTH; i++) begin : gen_gray_to_bin
        assign binary[i] = ^(gray >> i);
    end
endgenerate
```

Bit by bit, for a 4-bit converter:

```systemverilog
// For 4-bit example:
assign binary[3] = gray[3];                           // MSB unchanged
assign binary[2] = gray[3] ^ gray[2];                 // XOR from MSB down
assign binary[1] = gray[3] ^ gray[2] ^ gray[1];       // XOR from MSB down  
assign binary[0] = gray[3] ^ gray[2] ^ gray[1] ^ gray[0]; // XOR all bits
```

### Worked conversions

#### 4-Bit Conversion Table
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

#### Step-by-Step Example (Gray 0110 → Binary)
```
Gray input: 0110

binary[3] = gray[3] = 0
binary[2] = gray[3] ^ gray[2] = 0 ^ 1 = 1  
binary[1] = gray[3] ^ gray[2] ^ gray[1] = 0 ^ 1 ^ 1 = 0
binary[0] = gray[3] ^ gray[2] ^ gray[1] ^ gray[0] = 0 ^ 1 ^ 1 ^ 0 = 0

Result: binary = 0100 (decimal 4)
```

### Implementation

The whole module is one line per bit:

```systemverilog
assign binary[i] = ^(gray >> i);
```

Read it as: shift `gray` right by `i`, then XOR-reduce whatever is left -- which
XORs together every bit from position `i` to the MSB. The generate loop makes
it work for any WIDTH, synthesis tools recognize the pattern and optimize it,
all bits compute in parallel, and the result maps onto XOR tree structures.

## Timing Characteristics
The delay is an XOR tree of depth `log2(WIDTH)` -- typically 1-2 LUT delays for
most widths, with the critical path running from the MSB input to the LSB
output.

| WIDTH | XOR Levels | Typical Delay |
|-------|------------|---------------|
| 4     | 2          | 1 LUT delay   |
| 8     | 3          | 2 LUT delays  |
| 16    | 4          | 2 LUT delays  |
| 32    | 5          | 3 LUT delays  |

: gray2bin delay by width

Modern synthesis tools need no help here: they recognize the XOR-reduction
pattern, build balanced trees, and share XOR gates where possible.

## Usage Examples

### Asynchronous FIFO pointers

Convert the synchronized Gray pointers back to binary so you can do arithmetic
on them:

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

### Clock domain crossing counter

```systemverilog
// Convert Gray counter back to binary for address generation
gray2bin #(.WIDTH(AW)) addr_converter (
    .gray(gray_counter),
    .binary(memory_address)
);
```

### Position encoding

```systemverilog
// Convert Gray-encoded position to binary for processing
gray2bin #(.WIDTH(8)) position_decoder (
    .gray(gray_position),
    .binary(bin_position)
);
```

## Design Notes

**Width scaling.** `binary[i]` is the XOR of Gray bits `i..WIDTH-1`, so the
unshared cost is `WIDTH*(WIDTH-1)/2` XOR gates -- quadratic in WIDTH, as the
module header notes ("WIDTH * (WIDTH/2 average)"). Synthesis shares the common
prefixes, so realised area lands between linear and quadratic; do not budget it
as linear for wide converters. Delay grows with log(WIDTH), and the module
works well up to 64+ bits.

**Input validation.** Gray codes have no invalid states -- every input decodes
to something. If you want to gate on the *source* of the Gray code instead:

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

**Pipelining.** If you're closing timing at very high speed, a pipeline stage
is cheap insurance:

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

### Common mistakes

**Bit order confusion.** The shift direction matters:

```systemverilog
// WRONG: Bit order matters in Gray codes
assign binary[i] = ^(gray << i);  // Left shift instead of right

// CORRECT:
assign binary[i] = ^(gray >> i);  // Right shift
```

**Width mismatches.** Match the parameter to the actual bus width:

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

**Timing assumptions.** The output is combinational, not instantaneous:

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
- **johnson2bin**: Johnson counter to binary converter (different algorithm)

## Testing

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
// gray2bin is purely combinational -- no clock port, so there is no clocking
// event for a concurrent assertion to sample. Use IMMEDIATE assertions in an
// always_comb block, the same shape bin2gray.md uses: they re-evaluate whenever
// an input settles, need no clock, and hold under simulation and formal alike.
//
// The checker declares PORTS. Binding one with no ports via `(.*)` connects
// nothing, and every assertion then evaluates silently on X.

module gray2bin_properties #(
    parameter int WIDTH = 4
) (
    input logic [WIDTH-1:0] gray,
    input logic [WIDTH-1:0] binary
);

    function automatic logic [WIDTH-1:0] gray_encode(input logic [WIDTH-1:0] bin);
        gray_encode = bin ^ (bin >> 1);
    endfunction

    always_comb begin
        // MSB passes through unchanged
        a_msb_unchanged: assert (binary[WIDTH-1] == gray[WIDTH-1]);

        // Round trip: re-encoding the output reproduces the input
        a_round_trip: assert (gray_encode(binary) == gray);
    end

endmodule

// Bind at the point of use, OUTSIDE the checker.
bind gray2bin gray2bin_properties #(.WIDTH(WIDTH)) u_props (.*);
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

### Test files

- `val/cdc/test_gray2bin.py` -- functional verification

```bash
pytest val/cdc/test_gray2bin.py -v
```

## Navigation

- [← Back to CDC Index](index.md)
- [← Back to Main Documentation Index](../index.md)
