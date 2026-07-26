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

# Universal Shifter Module

## Purpose
The `shifter_universal` module is the general-purpose shift register: left shift,
right shift, parallel load, and hold, with both serial and parallel data in and
out. If your design needs bits moved sideways in any direction, this is the part
you reach for.

## Key Features
- Four distinct operations: hold, right shift, left shift, parallel load
- Bidirectional serial data input/output
- Parallel data load capability
- Serial data capture during shift operations
- Synchronous operation with asynchronous reset
- Configurable width

## Port Description

### Parameters
- **WIDTH**: Width of the shift register (default: 4)

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock |
| `rst_n` | 1 | Active-low asynchronous reset |
| `select` | 2 | Operation select control |
| `i_pdata` | WIDTH | Parallel data input |
| `i_sdata_lt` | 1 | Serial data input (left side) |
| `i_sdata_rt` | 1 | Serial data input (right side) |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `o_pdata` | WIDTH | Parallel data output |
| `o_sdata_lt` | 1 | Serial data output (left side) |
| `o_sdata_rt` | 1 | Serial data output (right side) |

## Operation Control

The 2-bit `select` signal controls the shifter operation:

| select | Operation | Description |
|--------|-----------|-------------|
| 2'b00 | Hold | Maintain current state |
| 2'b01 | Right Shift | Shift data right; new bit enters from `i_sdata_rt` |
| 2'b10 | Left Shift | Shift data left; new bit enters from `i_sdata_lt` |
| 2'b11 | Parallel Load | Load parallel input data |

## Implementation Details

### Combinational Logic for Next State
```systemverilog
always_comb begin
    // Default values - hold current state
    w_pdata = o_pdata;
    w_sdata_lt = 1'b0;
    w_sdata_rt = 1'b0;
    
    casez (select)
        2'b00: begin  // Hold
            w_pdata = o_pdata;
            w_sdata_lt = 1'b0;
            w_sdata_rt = 1'b0;
        end
        
        2'b01: begin  // Right Shift
            w_pdata = {i_sdata_rt, o_pdata[WIDTH-1:1]};
            w_sdata_lt = 1'b0;
            w_sdata_rt = o_pdata[0];
        end
        
        2'b10: begin  // Left Shift
            w_pdata = {o_pdata[WIDTH-2:0], i_sdata_lt};
            w_sdata_lt = o_pdata[WIDTH-1];
            w_sdata_rt = 1'b0;
        end
        
        2'b11: begin  // Parallel Load
            w_pdata = i_pdata;
            w_sdata_lt = 1'b0;
            w_sdata_rt = 1'b0;
        end
    endcase
end
```

### Sequential Logic for State Update
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        o_pdata    <= '0;
        o_sdata_lt <= 1'b0;
        o_sdata_rt <= 1'b0;
    end else begin
        o_pdata    <= w_pdata;
        o_sdata_lt <= w_sdata_lt;
        o_sdata_rt <= w_sdata_rt;
    end
end
```

## Operation Details

### Hold Operation (select = 2'b00)
- **Function**: Maintains current register state
- **Data Flow**: No data movement
- **Serial Outputs**: Both remain low (no shift occurring)
- **Use Case**: Pause operation while maintaining data integrity

### Right Shift Operation (select = 2'b01)
- **Function**: Shifts data toward LSB
- **Data Flow**: `i_sdata_rt` → MSB, LSB → `o_sdata_rt`
- **Serial Input**: New data enters from `i_sdata_rt`
- **Serial Output**: Shifted-out data exits via `o_sdata_rt`
- **Use Case**: Serial-to-parallel conversion, delay lines

### Left Shift Operation (select = 2'b10)
- **Function**: Shifts data toward MSB  
- **Data Flow**: `i_sdata_lt` → LSB, MSB → `o_sdata_lt`
- **Serial Input**: New data enters from `i_sdata_lt`
- **Serial Output**: Shifted-out data exits via `o_sdata_lt`
- **Use Case**: Multiplication by 2, bit-serial processing

### Parallel Load Operation (select = 2'b11)
- **Function**: Loads entire parallel word
- **Data Flow**: `i_pdata` → `o_pdata`
- **Serial Outputs**: Both remain low (no shift occurring)
- **Use Case**: Initialization, data injection

## Special Implementation Notes

### 1. Bidirectional Serial Interface
The module provides separate serial inputs and outputs for both directions:
- **Left side**: `i_sdata_lt` (input), `o_sdata_lt` (output)
- **Right side**: `i_sdata_rt` (input), `o_sdata_rt` (output)

That's what lets you chain multiple shifters or hook into bidirectional serial systems.

### 2. Clean Serial Output Management
Serial outputs are explicitly driven to zero when not actively shifting in that
direction — no glitches, no ambiguous states.

### 3. Asynchronous Reset
Reset immediately clears all outputs to zero, providing deterministic startup conditions.

### 4. Combinational/Sequential Separation
The design cleanly separates:
- **Combinational logic**: Calculates next state
- **Sequential logic**: Registers the state on clock edge

That split improves timing predictability and synthesis results.

## Timing Diagrams

### Right Shift Operation Example (WIDTH=4)

The first column is the reset state, before any edge; every later column is the
value *after* that cycle's edge. `o_sdata_rt` is registered, so the bit it shows
in a column is the LSB that the *previous* column's `o_pdata` ejected.

```
Clock:      _╱‾╲__╱‾╲__╱‾╲__╱‾╲__╱‾╲__╱‾╲_
select:     ---- 01   01   01   01   01
i_sdata_rt: ---- 1    0    1    1    0
o_pdata:    0000 1000 0100 1010 1101 0110
o_sdata_rt: --   0    0    0    0    1
```

The single `1` on `o_sdata_rt` is the LSB of `1101`, ejected by the fifth shift
and visible in the column that shift produces -- not alongside `1101` itself.

### Parallel Load followed by Left Shift
```
Clock:     ___╱‾╲___╱‾╲___╱‾╲___╱‾╲___
select:    11   10   10   10
i_pdata:   1010 ---- ---- ----
i_sdata_lt:---- 1    0    1
o_pdata:   1010 0101 1010 0101
o_sdata_lt:---- 1    0    1
```

## Applications

### Serial Communication Interface
```systemverilog
// Receive shift register for UART
// Right shift to collect incoming serial data
select = 2'b01;
i_sdata_rt = uart_rx;
// When 8 bits received, parallel data available
received_byte = o_pdata;
```

### Multiplication/Division by Powers of 2
```systemverilog
// Multiply by 2: left shift
select = 2'b10;
i_sdata_lt = 1'b0;  // Fill with zeros

// Divide by 2: right shift  
select = 2'b01;
i_sdata_rt = 1'b0;  // Fill with zeros (unsigned)
// or i_sdata_rt = o_pdata[WIDTH-1] for arithmetic shift
```

### Data Delay Line
```systemverilog
// Create N-cycle delay using N shifters
// Right shift with data input
select = 2'b01;
i_sdata_rt = data_input;
delayed_data = o_sdata_rt;  // N cycles later
```

### Pattern Generator
```systemverilog
// Load pattern then circulate
// 1. Load initial pattern
select = 2'b11;
i_pdata = initial_pattern;

// 2. Circulate pattern
select = 2'b01;         // Right shift
i_sdata_rt = o_pdata[0];  // Combinational tap -- NOT o_sdata_rt
```

Feed back `o_pdata[0]`, not `o_sdata_rt`. Here's the trap: the serial outputs
are registered (`o_sdata_rt <= w_sdata_rt`), so routing `o_sdata_rt` back
returns the ejected bit one shift too late and the pattern does not rotate --
it runs a `WIDTH+1`-long cycle. With `WIDTH=4` loaded to `1011`, the registered
feedback gives `1011 -> 0101 -> 1010 -> 1101 -> 0110 -> 1011` (period 5, and
`1110` and `0111` never appear), whereas the combinational tap gives the true
rotation `1011 -> 1101 -> 1110 -> 0111 -> 1011`.

### Scan Chain for Testing
```systemverilog
// JTAG-style scan chain
// Load test data
select = 2'b11;
i_pdata = test_vector;

// Shift out for observation
select = 2'b01;
i_sdata_rt = next_scan_in;
scan_out = o_sdata_rt;
```

## Design Considerations

### Chaining Multiple Shifters
```systemverilog
// Connect shifters in series
shifter1.i_sdata_rt = serial_input;
shifter2.i_sdata_rt = shifter1.o_sdata_rt;
shifter3.i_sdata_rt = shifter2.o_sdata_rt;
```

### Bidirectional Operation
```systemverilog
// Support both shift directions
if (shift_direction == RIGHT) begin
    select = 2'b01;
    i_sdata_rt = serial_data;
end else begin
    select = 2'b10; 
    i_sdata_lt = serial_data;
end
```

### Control Logic Integration
```systemverilog
// State machine control
case (state)
    LOAD: select = 2'b11;
    SHIFT_RIGHT: select = 2'b01;
    SHIFT_LEFT: select = 2'b10;
    HOLD: select = 2'b00;
endcase
```

## Common Use Cases
- Serial-to-parallel conversion
- Parallel-to-serial conversion  
- Data delay and timing adjustment
- Arithmetic operations (×2, ÷2)
- Pattern generation and circulation
- Scan chain testing
- FIFO buffer implementation
- Digital signal processing pipelines

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
