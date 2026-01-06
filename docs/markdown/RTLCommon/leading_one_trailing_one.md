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

# Leading One Trailing One Module

## Purpose
The `leading_one_trailing_one` module identifies the positions of the most significant bit (leading one) and least significant bit (trailing one) in an input data vector. It provides both index outputs and one-hot vector representations of these positions, along with status flags for edge cases.

## Key Features
- Finds the highest set bit position (leading one)
- Finds the lowest set bit position (trailing one) 
- Provides one-hot vector outputs for both positions
- Includes validity and edge case detection
- Parameterizable width with automatic index sizing

## Port Description

### Parameters
- **WIDTH**: Width of input data vector (default: 8)
- **INSTANCE_NAME**: String identifier for debugging (default: "")

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `data` | WIDTH | Input data vector to analyze |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `leadingone` | $clog2(WIDTH) | Index of the most significant set bit |
| `leadingone_vector` | WIDTH | One-hot vector with leading one position marked |
| `trailingone` | $clog2(WIDTH) | Index of the least significant set bit |
| `trailingone_vector` | WIDTH | One-hot vector with trailing one position marked |
| `all_zeroes` | 1 | High when input data is all zeros |
| `all_ones` | 1 | High when input data is all ones |
| `valid` | 1 | High when input data contains at least one set bit |

## Implementation Details

### Submodules
The module instantiates two specialized finder modules:

1. **find_last_set**: Locates the position of the most significant set bit
   - Connected to `leadingone` output
   - Implements priority encoding from MSB to LSB

2. **find_first_set**: Locates the position of the least significant set bit
   - Connected to `trailingone` output  
   - Implements priority encoding from LSB to MSB

### One-Hot Vector Generation
```systemverilog
always_comb begin
    leadingone_vector = '0;
    trailingone_vector = '0;

    // Only set vector bits if there is valid data
    if (|data) begin
        if (int'(leadingone) < WIDTH) begin
            leadingone_vector[leadingone] = 1'b1;
        end

        if (int'(trailingone) < WIDTH) begin
            trailingone_vector[trailingone] = 1'b1;
        end
    end
end
```

### Status Flag Logic
- **all_ones**: Uses reduction AND (`&data`) to detect when all bits are set
- **all_zeroes**: Uses reduction OR negation (`~(|data)`) to detect when no bits are set
- **valid**: Uses reduction OR (`|data`) to indicate presence of at least one set bit

## Special Implementation Notes

1. **Index Width Calculation**: Uses `$clog2(WIDTH)` to automatically size index outputs for any input width

2. **Bounds Checking**: Includes explicit bounds checking (`int'(leadingone) < WIDTH`) to prevent out-of-range indexing

3. **Zero Input Handling**: When input is all zeros:
   - One-hot vectors remain all zeros
   - Index values are undefined but bounded
   - `valid` flag indicates invalid state

4. **Type Casting**: Uses `int'()` casting for index comparisons to ensure proper integer arithmetic

## Usage Examples

### 8-bit Example
```
Input:  data = 8'b00101000
Output: leadingone = 3'd5
        leadingone_vector = 8'b00100000
        trailingone = 3'd3  
        trailingone_vector = 8'b00001000
        all_zeroes = 1'b0
        all_ones = 1'b0
        valid = 1'b1
```

### Edge Cases
```
Input:  data = 8'b00000000
Output: leadingone = undefined
        leadingone_vector = 8'b00000000
        trailingone = undefined
        trailingone_vector = 8'b00000000
        all_zeroes = 1'b1
        all_ones = 1'b0
        valid = 1'b0

Input:  data = 8'b11111111
Output: leadingone = 3'd7
        leadingone_vector = 8'b10000000
        trailingone = 3'd0
        trailingone_vector = 8'b00000001
        all_zeroes = 1'b0
        all_ones = 1'b1
        valid = 1'b1
```

## Applications
- Priority arbitration systems
- Bit manipulation operations
- Data compression algorithms
- Network packet processing
- Cache management systems

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
