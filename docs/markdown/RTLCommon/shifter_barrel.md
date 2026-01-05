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

# Barrel Shifter Module

## Purpose
The `shifter_barrel` module implements a combinational barrel shifter that can perform multiple types of shift operations in a single clock cycle. It supports logical left/right shifts with and without wrap-around, arithmetic right shifts, and no-shift operations, all controlled by a 3-bit control signal.

## Key Features
- Single-cycle shift operations for any shift amount
- Multiple shift modes: logical, arithmetic, and rotational
- Configurable shift amount up to data width
- Wrap-around (rotation) capabilities
- Purely combinational logic for maximum speed

## Port Description

### Parameters
- **WIDTH**: Width of the data bus (default: 8)

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `data` | WIDTH | Input data to be shifted |
| `ctrl` | 3 | Control signal for shift operation mode |
| `shift_amount` | $clog2(WIDTH)+1 | Number of positions to shift |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `data_out` | WIDTH | Shifted output data |

## Control Signal Encoding

The 3-bit `ctrl` signal determines the shift operation:

| ctrl | Operation | Description |
|------|-----------|-------------|
| 3'b000 | No shift | Output equals input |
| 3'b001 | Logical Right Shift (no wrap) | Fill with zeros from left |
| 3'b010 | Arithmetic Right Shift | Preserve sign bit (MSB) |
| 3'b011 | Logical Right Shift (wrap) | Rotate right |
| 3'b100 | Logical Left Shift (no wrap) | Fill with zeros from right |
| 3'b110 | Logical Left Shift (wrap) | Rotate left |
| Others | No shift | Default case |

## Implementation Details

### Shift Amount Modulation
```systemverilog
logic [$clog2(WIDTH)-1:0] shift_amount_mod;
assign shift_amount_mod = shift_amount[$clog2(WIDTH)-1:0];
```
The shift amount is automatically reduced modulo WIDTH to prevent out-of-bounds operations.

### Wrap-Around Implementation
```systemverilog
logic [WIDTH*2-1:0] w_data_double;
assign w_data_double = {data, data};

// Generate lookup values for rotating shifts
genvar i;
generate
    for (i = 0; i < WIDTH; i++) begin : gen_unrolled_shifts
        assign w_array_rs[i] = w_data_double[WIDTH-1+i:i];      // Right shift
        assign w_array_ls[i] = w_data_double[WIDTH*2-1-i:WIDTH-i]; // Left shift
    end
endgenerate
```

### Pre-computed Rotation Arrays
The module uses two lookup arrays for efficient rotation:
- **w_array_rs[WIDTH]**: Pre-computed right rotation results for all possible shift amounts
- **w_array_ls[WIDTH]**: Pre-computed left rotation results for all possible shift amounts

This approach eliminates the need for complex barrel shifting logic and provides constant-time access to any rotation amount.

### Main Shift Logic
```systemverilog
always_comb begin
    case (ctrl)
        3'b000: // No shift
            data_out = data;

        3'b001: // Logical Right Shift (no wrap)
            data_out = (shift_amount_mod == 0) ? data : data >> shift_amount;

        3'b010: // Arithmetic Right Shift (preserve sign)
            data_out = $signed(data) >>> shift_amount_mod;

        3'b011: // Logical Right Shift with wrap
            data_out = w_array_rs[shift_amount_mod];

        3'b100: // Logical Left Shift (no wrap)
            data_out = (shift_amount_mod == 0) ? data : data << shift_amount;

        3'b110: // Logical Left Shift with wrap
            data_out = w_array_ls[shift_amount_mod];

        default:
            data_out = data;
    endcase
end
```

## Special Implementation Notes

### 1. Combinational Design
- All operations complete in zero clock cycles
- No state machines or sequential logic
- Suitable for high-frequency operations

### 2. Arithmetic Right Shift
Uses SystemVerilog's `>>>` operator with `$signed()` casting to properly handle sign extension for two's complement numbers.

### 3. Zero Shift Optimization
Explicit checks for `shift_amount_mod == 0` optimize the common case of no shifting, avoiding unnecessary computation.

### 4. Double-Width Concatenation
The `{data, data}` concatenation creates a seamless circular buffer for rotation operations, enabling simple slice extraction for any rotation amount.

### 5. Generate Block Optimization
Pre-computing all possible rotation results at compile time eliminates runtime computation, trading minimal area for maximum speed.

## Timing Examples

### 8-bit Examples (WIDTH=8)

#### Logical Right Shift (no wrap)
```
Input:  data = 8'b11010110, shift_amount = 3, ctrl = 3'b001
Output: 8'b00011010
```

#### Arithmetic Right Shift
```
Input:  data = 8'b11010110, shift_amount = 3, ctrl = 3'b010
Output: 8'b11111010  (sign extended)
```

#### Right Rotation
```
Input:  data = 8'b11010110, shift_amount = 3, ctrl = 3'b011
Output: 8'b11011010  (bits wrap around)
```

#### Logical Left Shift (no wrap)
```
Input:  data = 8'b11010110, shift_amount = 3, ctrl = 3'b100
Output: 8'b10110000
```

#### Left Rotation
```
Input:  data = 8'b11010110, shift_amount = 3, ctrl = 3'b110
Output: 8'b10110110  (bits wrap around)
```

## Resource Utilization

### Area Considerations
- **Lookup Arrays**: Require WIDTH × WIDTH bits of combinational logic
- **Multiplexers**: Large mux structures for final output selection
- **Total**: Approximately O(WIDTH²) area complexity

### Speed Characteristics
- **Propagation Delay**: Constant regardless of shift amount
- **Critical Path**: Through lookup array and final output mux
- **Frequency**: Limited by combinational delay, not shift complexity

## Applications
- ALU implementations
- Cryptographic operations
- Signal processing
- Bit manipulation engines
- Network packet processing
- Data alignment circuits

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
