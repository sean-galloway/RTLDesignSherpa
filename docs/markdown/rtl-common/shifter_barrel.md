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
The `shifter_barrel` module is a combinational barrel shifter: any shift amount,
any supported mode, done in a single clock cycle. It covers logical left/right
shifts with and without wrap-around, arithmetic right shifts, and a no-shift
pass-through, all selected by a 3-bit control signal.

## Key Features
- Single-cycle shift operations for any shift amount
- Multiple shift modes: logical, arithmetic, and rotational
- Configurable shift amount up to data width
- Wrap-around (rotation) capabilities
- Purely combinational logic for maximum speed

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | — | 8 | Width of the data bus |

## Ports

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
`shift_amount_mod` reduces the amount modulo WIDTH — **only the wrap (rotate)
paths use it**. The three no-wrap paths take the RAW amount, with IEEE
saturation for amounts at or beyond the width: logical right/left by
`>= WIDTH` gives 0, arithmetic right gives all-sign-bits. (Before 2026-08-20
the no-wrap paths carried a `shift_amount_mod == 0` passthrough guard, so
shifting by exactly WIDTH returned the *input* — and the arithmetic path
shifted by the modded amount, wrong for every amount `>= WIDTH`. Found by a
doc review round, sim-confirmed, fixed with directed WIDTH-boundary tests and
an un-tautologized formal model that fails on the old RTL.)

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
Two lookup arrays do the heavy lifting for rotation:
- **w_array_rs[WIDTH]**: Pre-computed right rotation results for all possible shift amounts
- **w_array_ls[WIDTH]**: Pre-computed left rotation results for all possible shift amounts

Pre-computing means there's no barrel-shifting network to evaluate at runtime —
any rotation amount is a constant-time array lookup.

### Main Shift Logic
```systemverilog
always_comb begin
    case (ctrl)
        3'b000: // No shift
            data_out = data;

        3'b001: // Logical Right Shift (no wrap)
            data_out = data >> shift_amount;

        3'b010: // Arithmetic Right Shift (preserve sign)
            // if/else, NOT a ternary: a mixed-signedness ternary silently
            // degrades >>> to a logical shift
            if (shift_amount >= ($clog2(WIDTH)+1)'(WIDTH))
                data_out = {WIDTH{data[WIDTH-1]}};
            else
                data_out = $signed(data) >>> shift_amount;

        3'b011: // Logical Right Shift with wrap
            data_out = w_array_rs[shift_amount_mod];

        3'b100: // Logical Left Shift (no wrap)
            data_out = data << shift_amount;

        3'b110: // Logical Left Shift with wrap
            data_out = w_array_ls[shift_amount_mod];

        default:
            data_out = data;
    endcase
end
```

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

## Special Implementation Notes

### 1. Combinational Design
- All operations complete in zero clock cycles
- No state machines or sequential logic
- Suitable for high-frequency operations

### 2. Arithmetic Right Shift
The arithmetic shift uses SystemVerilog's `>>>` operator with a `$signed()` cast,
so sign extension behaves correctly for two's complement numbers.

### 3. Zero Shift Optimization
The explicit `shift_amount_mod == 0` checks short-circuit the most common case —
no shift at all — and skip the unnecessary computation.

### 4. Double-Width Concatenation
The `{data, data}` concatenation is the oldest trick in the book: paste the data
next to itself and a rotation becomes a plain slice out of a 2×-wide window. Any
rotation amount, same cost.

### 5. Generate Block Optimization
The generate block pre-computes every possible rotation at compile time, so
runtime is just a lookup. You spend a little area, you get back maximum speed.

## Applications
- ALU implementations
- Cryptographic operations
- Signal processing
- Bit manipulation engines
- Network packet processing
- Data alignment circuits

## Resource Utilization

### Area Considerations
- **Lookup Arrays**: Require WIDTH × WIDTH bits of combinational logic
- **Multiplexers**: Large mux structures for final output selection
- **Total**: Approximately O(WIDTH²) area complexity

### Speed Characteristics
- **Propagation Delay**: Constant regardless of shift amount
- **Critical Path**: Through lookup array and final output mux
- **Frequency**: Limited by combinational delay, not shift complexity

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
