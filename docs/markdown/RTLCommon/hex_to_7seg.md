# Hex to 7-Segment Display (`hex_to_7seg.sv`)

## Purpose
Converts 4-bit hexadecimal values (0-F) to 7-segment display patterns for common anode displays. Provides human-readable display of digital values for debugging, user interfaces, and embedded systems.

## Ports

### Input Ports
- **`hex[3:0]`** - 4-bit hexadecimal input (0x0 to 0xF)

### Output Ports
- **`seg[6:0]`** - 7-segment display pattern

### Parameters
None - fixed functionality for standard 7-segment displays.

## 7-Segment Display Layout

### Segment Naming Convention
```
     aaa
    f   b
    f   b  
     ggg
    e   c
    e   c
     ddd
```

### Bit Assignment
- **seg[6:0] = {g, f, e, d, c, b, a}**
- **Common Anode**: 0 = segment ON, 1 = segment OFF
- **Active Low**: LED segments illuminate when driven low

## Character Patterns

### Complete Truth Table
| Hex | Display | seg[6:0] | Segments ON | Pattern |
|-----|---------|----------|-------------|---------|
| 0x0 | **0** | 1000000 | abcdef | Classic 0 |
| 0x1 | **1** | 1111001 | bc | Right side |
| 0x2 | **2** | 0100100 | abged | Snake pattern |
| 0x3 | **3** | 0110000 | abgcd | Right-heavy |
| 0x4 | **4** | 0011001 | fgbc | Left + right |
| 0x5 | **5** | 0010010 | afgcd | S-curve |
| 0x6 | **6** | 0000010 | afgdce | Almost all |
| 0x7 | **7** | 1111000 | abc | Top + right |
| 0x8 | **8** | 0000000 | all | All segments |
| 0x9 | **9** | 0011000 | abgcdf | Top + middle + right |
| 0xA | **A** | 0001000 | abcefg | Letter A |
| 0xB | **b** | 0000011 | fgedc | Lowercase b |
| 0xC | **C** | 1000110 | afed | Letter C |
| 0xD | **d** | 0100001 | bgedc | Lowercase d |
| 0xE | **E** | 0000110 | afged | Letter E |
| 0xF | **F** | 0001110 | afge | Letter F |

### Visual Representation
```
 ###   #   ###  ###  # #  ###  ###  ###  ###  ### 
#   # # #     #    # # #  #    #      # #   # #   #
#   #   #   ###  ###  ###  ###  ###    #  ###  ###
#   #   #  #      #    #    # #   #    # #   #    #
 ###    #  ###  ###    #  ###  ###    #  ###    # 
  0     1    2    3    4    5    6    7    8    9

 ###  ###   ##  ###  ###  ### 
#   # #     #   #   # #    #   
###   ###   #   #   # ###  ### 
#   # #   # #   #   # #    #   
#   # ###   ##  ###  ###  #   
  A     b    C    d    E    F
```

## Implementation Details

### Case Statement Structure
```systemverilog
always_comb begin
    casez (hex)
        4'h0: seg = 7'b1000000;  // 0: abcdef (not g)
        4'h1: seg = 7'b1111001;  // 1: bc
        4'h2: seg = 7'b0100100;  // 2: abged
        4'h3: seg = 7'b0110000;  // 3: abgcd
        4'h4: seg = 7'b0011001;  // 4: fgbc
        4'h5: seg = 7'b0010010;  // 5: afgcd
        4'h6: seg = 7'b0000010;  // 6: afgdce
        4'h7: seg = 7'b1111000;  // 7: abc
        4'h8: seg = 7'b0000000;  // 8: all segments
        4'h9: seg = 7'b0011000;  // 9: abgcdf
        4'ha: seg = 7'b0001000;  // A: abcefg (not d)
        4'hb: seg = 7'b0000011;  // b: fgedc (not ab)
        4'hc: seg = 7'b1000110;  // C: afed (not bcg)
        4'hd: seg = 7'b0100001;  // d: bgedc (not af)
        4'he: seg = 7'b0000110;  // E: afged (not bc)
        4'hf: seg = 7'b0001110;  // F: afge (not bcd)
        default: seg = 7'bxxxxxxx;  // Invalid - undefined output
    endcase
end
```

### Design Choices

#### Lowercase vs. Uppercase
- **A**: Uppercase (more readable)
- **b, d**: Lowercase (distinguishable from 8, 0)
- **C**: Uppercase (standard representation)
- **E, F**: Uppercase (clear representation)

#### Common Anode Configuration
- **Active low outputs**: 0 = LED on, 1 = LED off
- **Current sourcing**: Display provides +V, controller sinks current
- **Logic inversion**: Many controllers expect active-high, requiring external inversion

## Display Technology Integration

### Common Anode Connection
```
    VCC
     │
   ┌─┴─┐
   │ a │ LED
   └─┬─┘
     │
   Output A (from controller)
```

### Common Cathode Alternative
For common cathode displays, invert all outputs:
```systemverilog
// For common cathode displays:
assign seg_common_cathode = ~seg;
```

### Current Limiting
```
Controller → [Resistor] → LED Segment → Common Anode (+V)
```
Typical resistor values: 220Ω - 1kΩ depending on LED specifications.

## Use Cases and Applications

### Debug Displays
```systemverilog
// Display processor status
hex_to_7seg status_display (
    .hex(processor_status[3:0]),
    .seg(status_segments)
);
```

### Multi-Digit Displays
```systemverilog
// 4-digit hex display
hex_to_7seg digit0 (.hex(value[3:0]),   .seg(seg0));
hex_to_7seg digit1 (.hex(value[7:4]),   .seg(seg1));
hex_to_7seg digit2 (.hex(value[11:8]),  .seg(seg2));
hex_to_7seg digit3 (.hex(value[15:12]), .seg(seg3));
```

### Memory/Register Viewers
```systemverilog
// Display memory contents
hex_to_7seg mem_display (
    .hex(memory_data[address]),
    .seg(memory_segments)
);
```

### Error Code Display
```systemverilog
// Show error codes
hex_to_7seg error_display (
    .hex(error_code),
    .seg(error_segments)
);
```

## Timing Characteristics

### Propagation Delay
- **Combinational logic**: Case statement maps to LUT
- **Typical delay**: 1 LUT delay (sub-nanosecond)
- **No clock dependency**: Immediate response to input changes

### Display Update Rate
- **Electronic response**: Immediate (propagation delay)
- **Visual response**: Limited by LED rise/fall times (~microseconds)
- **Human perception**: >30Hz refresh rate for flicker-free display

## Design Variations

### Extended Character Set
Some implementations add additional characters:
```systemverilog
// Extended characters (implementation dependent)
4'h10: seg = 7'b1111111;  // Blank/space
4'h11: seg = 7'b0111111;  // Dash/minus
4'h12: seg = 7'b1110111;  // Underscore
```

### Alternative Fonts
Different character representations for better readability:
```systemverilog
// Alternative 'b' (uppercase-like)
4'hb: seg = 7'b0000111;  // More symmetric b
```

### Brightness Control
```systemverilog
// PWM brightness control
logic [6:0] seg_raw;
hex_to_7seg decoder (.hex(hex_in), .seg(seg_raw));

// Apply PWM for brightness
assign seg_out = brightness_enable ? seg_raw : 7'b1111111;
```

## Multiplexed Display Support

### Time-Division Multiplexing
```systemverilog
// 4-digit multiplexed display
logic [1:0] digit_select;
logic [3:0] current_hex;

// Select current digit data
always_comb begin
    case (digit_select)
        2'b00: current_hex = value[3:0];    // Digit 0
        2'b01: current_hex = value[7:4];    // Digit 1
        2'b10: current_hex = value[11:8];   // Digit 2
        2'b11: current_hex = value[15:12];  // Digit 3
    endcase
end

hex_to_7seg display_decoder (
    .hex(current_hex),
    .seg(segments)
);

// Digit enable signals (one active at a time)
assign digit_enable = ~(4'b0001 << digit_select);
```

### Refresh Rate Calculation
```systemverilog
// For 4-digit display at 1kHz total refresh:
// Each digit displayed for 250μs
// Switching frequency: 4kHz

localparam REFRESH_DIVIDER = CLOCK_FREQ / 4000;
```

## Verification and Testing

### Exhaustive Testing
```systemverilog
// Test all 16 hex values
for (int i = 0; i < 16; i++) begin
    hex_input = i[3:0];
    #1;
    expected_segments = reference_table[i];
    assert(seg_output == expected_segments);
end
```

### Visual Verification
- **Physical testing**: Connect to actual 7-segment display
- **Simulation**: Use testbench with visual output
- **Reference comparison**: Compare with known-good implementations

### Pattern Validation
```systemverilog
// Verify no segments are permanently on/off
logic [6:0] all_segments_used = '0;
for (int i = 0; i < 16; i++) begin
    all_segments_used |= ~reference_table[i];  // Accumulate active segments
end
assert(all_segments_used == 7'b1111111);  // All segments used somewhere
```

## Common Issues and Debugging

### Segment Mapping Errors
- **Bit order**: Ensure {g,f,e,d,c,b,a} ordering matches hardware
- **Active level**: Verify common anode vs. common cathode
- **Pin assignment**: Check physical connections match bit assignments

### Display Quality Issues
- **Ghost segments**: Check current limiting and multiplexing timing
- **Dim display**: Verify current levels and refresh rates
- **Flicker**: Ensure adequate refresh rate (>30Hz visible, >60Hz preferred)

### Character Readability
- **Ambiguous characters**: 6 vs b, 8 vs B, 0 vs O
- **Context**: Use surrounding digits/letters for disambiguation
- **Alternative fonts**: Consider modified patterns for better distinction

## Related Modules
- **BCD to 7-segment**: For decimal-only displays
- **ASCII to 7-segment**: Extended character set support
- **Display multiplexer**: Time-division multiplexing controller
- **PWM brightness controller**: Dynamic brightness adjustment

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
