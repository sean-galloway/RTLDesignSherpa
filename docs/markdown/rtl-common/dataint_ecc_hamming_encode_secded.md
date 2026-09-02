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

# dataint_ecc_hamming_encode_secded

## Overview

The encoder half of a SECDED Hamming scheme (Single Error Correction, Double Error Detection). It generates the check bits that let the far end detect up to 2-bit errors and correct single-bit errors in the data.

### Module Declaration

```systemverilog
module dataint_ecc_hamming_encode_secded #(
    parameter int WIDTH = 4,
    parameter int DEBUG = 0
) (
    input  logic [     WIDTH-1:0] data,
    output logic [TotalWidth-1:0] encoded_data
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `WIDTH` | 4 | Width of input data in bits |
| `DEBUG` | 0 | Enable debug output (1=enabled, 0=disabled) |

### Calculated Parameters

| Parameter | Formula | Description |
|-----------|---------|-------------|
| `ParityBits` | `$clog2(WIDTH + $clog2(WIDTH) + 1)` | Number of Hamming parity bits |
| `TotalWidth` | `WIDTH + ParityBits + 1` | Total encoded data width (includes SECDED bit) |

### Example Configurations

4-bit data (the common example):
- Data bits: 4
- Parity bits: 3 (positions 0, 1, 3)
- SECDED bit: 1 (position 7)
- Total width: 8 bits

8-bit data:
- Data bits: 8
- Parity bits: 4 (positions 0, 1, 3, 7)
- SECDED bit: 1 (position 12)
- Total width: 13 bits

16-bit data:
- Data bits: 16
- Parity bits: 5 (positions 0, 1, 3, 7, 15)
- SECDED bit: 1 (position 21)
- Total width: 22 bits

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `data` | Input | WIDTH | Original data to be encoded |
| `encoded_data` | Output | TotalWidth | Encoded data with parity and SECDED bits |

## Functional Description

### Hamming Code Structure

The encoded word carries three things:
1. **Data Bits**: Your original data, parked at specific positions
2. **Parity Bits**: Hamming parity bits at the power-of-2 positions (1, 2, 4, 8, ...)
3. **SECDED Bit**: One extra overall parity bit for double error detection

### Bit Position Layout

```
Position: 1  2  3  4  5  6  7  8  9  10 11 12 ...
Content:  P1 P2 D1 P4 D2 D3 D4 P8 D5 D6 D7 D8 ...

Where: P = Parity bit, D = Data bit
```

### Key Functions

#### `bit_position(k)` Function

Works out where data bit `k` belongs in the encoded stream:

```systemverilog
function automatic integer bit_position(input integer k);
    integer j, pos;
    begin
        pos = k + 1;  // Start at k+1 to account for parity at position 0
        for (j = 0; j < ParityBits; j++) begin
            if (pos >= (2 ** j)) pos = pos + 1;  // Skip parity positions
        end
        bit_position = pos - 1;  // Convert to 0-based index
    end
endfunction
```

#### `get_covered_bits(parity_bit)` Function

Returns a bitmask of every position a specific parity bit covers:

```systemverilog
function automatic [TotalWidth-1:0] get_covered_bits(input integer parity_bit);
    integer j;
    begin
        get_covered_bits = 'b0;
        for (j = 0; j < TotalWidth; j++) begin
            // Check if position j+1 has parity_bit set in its binary representation
            if (|(((j + 1) >> parity_bit) & 1)) 
                get_covered_bits[j] = 1'b1;
        end
    end
endfunction
```

### Encoding Algorithm

#### Step 1: Data Placement

```systemverilog
// Initialize with zeros
w_data_with_parity = {TotalWidth{1'b0}};

// Insert data bits into correct positions
for (i = 0; i < WIDTH; i++) begin
    w_data_with_parity[bit_position(i)] = data[i];
end
```

#### Step 2: Parity Calculation

```systemverilog
// Calculate each Hamming parity bit
for (i = 0; i < ParityBits; i++) begin
    parity_pos = (2 ** i) - 1;  // Positions 0, 1, 3, 7, 15, ...
    w_data_with_parity[parity_pos] = 1'b0;  // Initialize
    
    // XOR all covered positions
    w_covered_bits = get_covered_bits(i);
    for (bit_index = 0; bit_index < TotalWidth; bit_index++) begin
        if (w_covered_bits[bit_index]) begin
            w_data_with_parity[parity_pos] = 
                w_data_with_parity[parity_pos] ^ w_data_with_parity[bit_index];
        end
    end
end
```

#### Step 3: SECDED Bit Calculation

```systemverilog
// Calculate overall parity for SECDED
w_data_with_parity[TotalWidth-1] = ^w_data_with_parity[TotalWidth-2:0];
```

### Error Correction Capabilities

Single error correction:
- Can correct any single-bit error in the encoded data
- Uses the Hamming parity bits to locate the error
- The decoder flips the bad bit

Double error detection:
- The SECDED bit is what spots double-bit errors
- Can't fix them, but it flags them
- No silent data corruption

| Error Type | Detection | Correction |
|------------|-----------|------------|
| No Error | Yes | N/A |
| Single Bit Error | Yes | Yes |
| Double Bit Error | Yes | No |
| Triple+ Bit Error | Partial | No |

### Combinational Design

- **No Clock Required**: Purely combinational logic
- **Immediate Output**: Encoded data shows up as soon as the input settles
- **Stateless Operation**: No internal state, nothing to reset

### Scalable Architecture

- **Parameterizable Width**: Any data width you like
- **Automatic Sizing**: The parity bit count is worked out for you
- **Efficient Layout**: Optimal bit positioning for the Hamming code

### Debug Support

Note that `DEBUG` is a **no-op** in this module: the RTL never references it outside its parameter declaration, so there's no debug output to be had. The parameter is reserved for future use.

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples

### Basic Encoding

```systemverilog
// 8-bit data encoder
dataint_ecc_hamming_encode_secded #(
    .WIDTH(8),
    .DEBUG(0)
) hamming_encoder (
    .data(input_data),
    .encoded_data(ecc_encoded_data)
);
```

### With Debug

```systemverilog
// Debug-enabled encoder for verification
dataint_ecc_hamming_encode_secded #(
    .WIDTH(4),
    .DEBUG(1)
) debug_encoder (
    .data(test_data),
    .encoded_data(encoded_output)
);
```

## Design Notes

### Applications

- Memory systems (ECC RAM)
- Communication protocols
- Storage systems
- Critical data processing
- Aerospace and automotive systems
- Any application requiring data integrity

## Related Modules

- **`dataint_ecc_hamming_decode_secded`**: Corresponding decoder module
- Used together for complete SECDED error correction system

## Testing

**No test coverage.** There is no
`val/**/test_dataint_ecc_hamming_encode_secded.py`, and no module that instantiates this one has a testbench either, so nothing in the repository exercises it.

Treat any behaviour described on this page as unverified by simulation.

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
