# Binary Counter for FIFOs

## Overview
The `counter_bin` module is a specialized binary counter designed specifically for FIFO (First-In-First-Out) buffer applications. Unlike traditional counters, it implements a unique wrap-around behavior where the MSB is inverted and lower bits are cleared when reaching the maximum value, creating a pattern suitable for circular buffer management.

## Module Declaration
```systemverilog
module counter_bin #(
    parameter int WIDTH = 5,
    parameter int MAX   = 10
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] counter_bin_curr,
    output logic [WIDTH-1:0] counter_bin_next
);
```

## Parameters

### WIDTH
- **Type**: `int`
- **Default**: `5`
- **Description**: Total width of the counter in bits
- **Range**: Must be ≥ 2 for proper MSB inversion operation
- **Usage**: Determines the counter's bit width and maximum representable value

### MAX
- **Type**: `int` 
- **Default**: `10`
- **Description**: Maximum count value before special wrap behavior
- **Range**: Should be < `2^(WIDTH-1)` for proper operation
- **Constraint**: Must fit within the lower `WIDTH-1` bits

## Ports

### Inputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `clk` | 1 | `logic` | System clock input |
| `rst_n` | 1 | `logic` | Active-low asynchronous reset |
| `enable` | 1 | `logic` | Counter enable control |

### Outputs
| Port | Width | Type | Description |
|------|-------|------|-------------|
| `counter_bin_curr` | WIDTH | `logic` | Current counter value (registered) |
| `counter_bin_next` | WIDTH | `logic` | Next counter value (combinational) |

## Architecture Details

### Internal Signals
```systemverilog
logic [WIDTH-2:0] w_max_val;
assign w_max_val = (WIDTH-1)'(MAX - 1);
```

### Special Wrap Logic
The counter implements a unique wrap-around behavior:

```systemverilog
always_comb begin
    if (enable) begin
        if (counter_bin_curr[WIDTH-2:0] == w_max_val)
            counter_bin_next = {~counter_bin_curr[WIDTH-1], {(WIDTH - 1){1'b0}}};
        else
            counter_bin_next = counter_bin_curr + 1;
    end else begin
        counter_bin_next = counter_bin_curr;
    end
end
```

## Operation Principles

### Normal Counting
When `counter_bin_curr[WIDTH-2:0] < MAX-1`:
- Counter increments normally by 1
- MSB remains unchanged
- Standard binary counting behavior

### Wrap Condition
When `counter_bin_curr[WIDTH-2:0] == MAX-1`:
- MSB is inverted: `~counter_bin_curr[WIDTH-1]`
- Lower bits are cleared: `{(WIDTH-1){1'b0}}`
- Creates a "folded" counting pattern

### Enable Control
- When `enable = 1`: Counter operates normally
- When `enable = 0`: Counter holds current value

## Counting Sequence Example

### Configuration: WIDTH=4, MAX=6
```
Initial:  0000 (MSB=0, lower=000)
         0001
         0010  
         0011
         0100
         0101  <- MAX-1 reached
Wrap:    1000  <- MSB inverted (0→1), lower bits cleared
         1001
         1010
         1011
         1100
         1101  <- MAX-1 reached again  
Wrap:    0000  <- MSB inverted (1→0), lower bits cleared
```

### Pattern Analysis
- **First Half**: MSB=0, counts 0 to MAX-1
- **Second Half**: MSB=1, counts 0 to MAX-1  
- **Full Cycle**: 2×MAX states total

## FIFO Application Context

### Address Generation
This counter pattern is ideal for FIFO addressing because:
1. **Circular Addressing**: Lower bits provide circular buffer addresses
2. **Overflow Detection**: MSB toggles indicate buffer wrap-around
3. **Full/Empty Logic**: Comparing MSBs between read/write pointers

### FIFO Pointer Comparison
```systemverilog
// FIFO empty when pointers exactly equal
assign fifo_empty = (rd_ptr == wr_ptr);

// FIFO full when addresses equal but MSBs differ
assign fifo_full = (rd_ptr[WIDTH-2:0] == wr_ptr[WIDTH-2:0]) && 
                   (rd_ptr[WIDTH-1] != wr_ptr[WIDTH-1]);
```

## Timing Characteristics

### Combinational Paths
- **Enable to Next**: Single logic level
- **Current to Next**: Increment/wrap logic depth
- **Critical Path**: Wrap detection and MSB inversion

### Sequential Behavior
- **Setup Time**: Standard flip-flop requirements
- **Clock-to-Q**: Standard flip-flop propagation
- **Reset Recovery**: One cycle after reset deassertion

## Design Examples

### 1. Small FIFO Buffer (8 entries)
```systemverilog
counter_bin #(
    .WIDTH(4),    // 4-bit counter
    .MAX(8)       // 8 entries (0-7)
) wr_ptr_counter (
    .clk(clk),
    .rst_n(rst_n),
    .enable(wr_enable),
    .counter_bin_curr(wr_ptr),
    .counter_bin_next(wr_ptr_next)
);
```

### 2. Large FIFO Buffer (1024 entries)
```systemverilog
counter_bin #(
    .WIDTH(11),   // 11-bit counter (10 bits address + 1 MSB)
    .MAX(1024)    // 1024 entries (0-1023)
) rd_ptr_counter (
    .clk(clk),
    .rst_n(rst_n), 
    .enable(rd_enable),
    .counter_bin_curr(rd_ptr),
    .counter_bin_next(rd_ptr_next)
);
```

### 3. Asymmetric FIFO
```systemverilog
// Write pointer - 16 entries
counter_bin #(.WIDTH(5), .MAX(16)) wr_cnt (...);

// Read pointer - different size for width conversion
counter_bin #(.WIDTH(6), .MAX(32)) rd_cnt (...);
```

## Advanced Usage

### Address Extraction
```systemverilog
// Extract memory address (lower bits only)
assign mem_addr = counter_bin_curr[WIDTH-2:0];

// Extract wrap flag (MSB only)  
assign wrap_flag = counter_bin_curr[WIDTH-1];
```

### Gray Code Conversion
For asynchronous FIFOs, convert to Gray code:
```systemverilog
logic [WIDTH-1:0] gray_ptr;
bin2gray #(.WIDTH(WIDTH)) b2g (
    .binary(counter_bin_curr),
    .gray(gray_ptr)
);
```

## Synthesis Considerations

### Resource Utilization
- **Flip-Flops**: WIDTH registers for current counter
- **LUTs**: Increment, wrap detection, and MSB inversion logic
- **Optimization**: Synthesis tools typically optimize the wrap logic efficiently

### Timing Optimization
```systemverilog
// Optional: Pipeline for high-frequency operation
logic [WIDTH-1:0] counter_bin_pipe;
always_ff @(posedge clk) begin
    counter_bin_pipe <= counter_bin_next;
end
```

### Parameter Validation
```systemverilog
initial begin
    assert (WIDTH >= 2) 
        else $error("WIDTH must be at least 2 for MSB operation");
    assert (MAX <= (2**(WIDTH-1))) 
        else $error("MAX too large for given WIDTH");
    assert (MAX > 0) 
        else $error("MAX must be positive");
end
```

## Verification Strategy

### Test Scenarios
1. **Basic Increment**: Verify normal counting behavior
2. **Wrap Boundary**: Test MSB inversion at MAX-1
3. **Enable Control**: Verify hold behavior when disabled
4. **Reset Operation**: Confirm proper reset to zero
5. **Full Sequence**: Complete cycle through all states

### Coverage Points
```systemverilog
covergroup counter_bin_cg @(posedge clk);
    cp_lower_bits: coverpoint counter_bin_curr[WIDTH-2:0] {
        bins all_values[] = {[0:MAX-1]};
    }
    cp_msb: coverpoint counter_bin_curr[WIDTH-1] {
        bins low = {0};
        bins high = {1};
    }
    cp_wrap: coverpoint (counter_bin_curr[WIDTH-2:0] == w_max_val);
    cp_enable: coverpoint enable;
endgroup
```

## Common Issues and Solutions

### Issue 1: Incorrect FIFO Size
**Problem**: MAX parameter doesn't match actual FIFO depth
**Solution**: Ensure MAX equals the number of FIFO entries

### Issue 2: Width Mismatch  
**Problem**: WIDTH too small for MAX value
**Solution**: Set WIDTH ≥ `$clog2(2*MAX)` for full range

### Issue 3: Timing Violations
**Problem**: Wrap logic creates long combinational paths
**Solution**: Pipeline the next value calculation or reduce MAX

## Performance Characteristics

### Maximum Frequency
- **Limiting Factor**: Wrap detection and MSB inversion logic
- **Typical Performance**: 300-500 MHz in modern FPGAs
- **Optimization**: Consider registering intermediate signals for high speed

### Power Consumption
- **Dynamic Power**: Proportional to toggle rate
- **Optimization**: Use enable signal to reduce unnecessary toggles
- **Clock Gating**: Gate clock when FIFO operations are idle

## Related Modules
- `counter_bingray`: Provides both binary and Gray code outputs
- `counter`: Basic counter without wrap behavior
- `counter_load_clear`: Loadable counter with different wrap behavior
- Standard FIFO controllers that use this addressing scheme

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
