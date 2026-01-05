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

# Find Last Set (`find_last_set.sv`)

## Purpose
Finds the index of the most significant bit (MSB) that is set to '1' in the input vector. Implements a priority encoder that favors higher-indexed bits.

## Ports

### Input Ports
- **`data[WIDTH-1:0]`** - Input data vector to search

### Output Ports
- **`index[$clog2(WIDTH)-1:0]`** - Index of the last (highest) set bit

### Parameters
- **`WIDTH`** - Width of input data vector (default: 32)
- **`INSTANCE_NAME`** - String identifier for debug (default: "FLS")

## Implementation Details

### Core Algorithm
```systemverilog
localparam int N = $clog2(WIDTH);
logic w_found;

always_comb begin
    index = {N{1'b0}}; // Default value if no bit is set
    w_found = 1'b0;

    for (int i = WIDTH - 1; i >= 0; i--) begin
        if (data[i] && !w_found) begin
            index = i[N-1:0]; // Ensure correct bit width
            w_found = 1'b1;
        end
    end
end
```

### Search Strategy
- **Direction**: MSB to LSB (right to left, descending index)
- **Priority**: Higher indices have higher priority
- **First match**: Stops at first '1' bit encountered from MSB
- **Found flag**: Prevents multiple assignments

## Functional Behavior

### Truth Table Examples (WIDTH=8)

| data[7:0] | index[2:0] | Description |
|-----------|------------|-------------|
| 10000000  | 111        | Bit 7 is last set |
| 01000000  | 110        | Bit 6 is last set |
| 00100000  | 101        | Bit 5 is last set |
| 00010000  | 100        | Bit 4 is last set |
| 00001000  | 011        | Bit 3 is last set |
| 00000100  | 010        | Bit 2 is last set |
| 00000010  | 001        | Bit 1 is last set |
| 00000001  | 000        | Bit 0 is last set |
| 00000000  | 000        | No bits set - default |
| 10000001  | 111        | Multiple bits - MSB wins |
| 11111111  | 111        | All bits set - bit 7 wins |

### Key Characteristics
- **MSB priority**: Always returns highest index when multiple bits set
- **Zero default**: Returns 0 when no bits are set (same as find_first_set)
- **Deterministic**: Same input always produces same output
- **Combinational**: Immediate response to input changes

## Design Features

### Reverse Loop Implementation
```systemverilog
for (int i = WIDTH - 1; i >= 0; i--) begin
```
- **MSB-first**: Starts from highest bit index
- **Decrementing**: Moves toward LSB
- **Early termination**: Stops at first match found

### Width Parameterization
Same auto-sizing as `find_first_set`:
- **Output width**: `$clog2(WIDTH)` bits
- **Examples**:
  - WIDTH=8 → index[2:0] (3 bits)
  - WIDTH=16 → index[3:0] (4 bits)  
  - WIDTH=32 → index[4:0] (5 bits)

### Found Flag Logic
```systemverilog
if (data[i] && !w_found) begin
    index = i[N-1:0];
    w_found = 1'b1;
end
```
- **Single assignment**: Prevents overwriting the highest found bit
- **Priority enforcement**: Only the first match (highest index) is captured

## Use Cases

### Interrupt Priority Handling
```systemverilog
find_last_set #(.WIDTH(8)) irq_priority (
    .data(interrupt_pending),
    .index(highest_priority_irq)
);
```
- Service highest-priority interrupt first
- Preemptive interrupt handling

### Leading Zero Count
```systemverilog
// Find position of leading 1, then calculate leading zeros
find_last_set #(.WIDTH(32)) leading_one (
    .data(input_value),
    .index(msb_position)
);

assign leading_zero_count = (input_value == 0) ? 32 : (31 - msb_position);
```

### Bit Width Calculation
```systemverilog
find_last_set #(.WIDTH(64)) width_calc (
    .data(value),
    .index(msb_pos)
);

assign required_bits = msb_pos + 1; // Minimum bits needed to represent value
```

### Cache Line Selection
```systemverilog
find_last_set #(.WIDTH(16)) cache_priority (
    .data(cache_line_priorities),
    .index(selected_cache_line)
);
```
- Select highest priority cache line for replacement
- LRU policy implementation

## Timing Characteristics

### Propagation Delay
- **Best case**: 1 LUT delay (MSB set)
- **Worst case**: Multiple LUT delays (LSB only set)
- **Average case**: Depends on typical bit patterns

### Critical Path Analysis
```
MSB check → MSB-1 check → ... → LSB check → Output
```
- **Path length**: Linear with WIDTH in worst case
- **Typical case**: Shorter path when higher bits are set
- **Optimization**: Synthesis tools create efficient implementations

## Algorithm Comparison

### Find Last Set vs. Find First Set

| Aspect | Find Last Set | Find First Set |
|--------|---------------|----------------|
| **Search Direction** | MSB → LSB | LSB → MSB |
| **Priority** | Higher index wins | Lower index wins |
| **Loop Direction** | `i--` (decrementing) | `i++` (incrementing) |
| **Use Case** | Priority systems | Fair allocation |
| **Default Output** | 0 (same) | 0 (same) |

### Typical Use Case Patterns

| Application Type | Preferred Algorithm |
|------------------|-------------------|
| **Interrupt Controllers** | Find Last Set (priority) |
| **Round-Robin Arbiters** | Find First Set (fairness) |
| **Error Reporting** | Find Last Set (severity) |
| **Resource Allocation** | Find First Set (efficiency) |
| **Bit Manipulation** | Either (depends on need) |

## Design Considerations

### Zero Input Handling
Both modules return 0 for zero input:
```systemverilog
// data = 8'b00000000
// Both find_first_set and find_last_set return 3'b000
```
**Application consideration**: May need explicit zero detection:
```systemverilog
assign valid_result = |data;  // OR-reduce to detect any bits set
assign result_index = valid_result ? index : INVALID_INDEX;
```

### Performance Scaling
- **Small WIDTH (<16)**: Excellent performance
- **Medium WIDTH (16-64)**: Good performance, may need pipelining
- **Large WIDTH (>64)**: Consider hierarchical implementation

### Synthesis Optimization
Modern synthesis tools recognize these patterns:
- **Priority encoder primitives**: Often map to dedicated hardware
- **LUT optimization**: Efficient resource utilization
- **Timing optimization**: Automatic critical path optimization

## Advanced Usage Patterns

### Hierarchical Priority Encoding
```systemverilog
// For very wide inputs, use hierarchical approach
find_last_set #(.WIDTH(8)) level0_fls [7:0] (
    .data(data_chunks),  // 8 chunks of 8 bits each
    .index(chunk_indices)
);

find_last_set #(.WIDTH(8)) level1_fls (
    .data(chunk_valid),  // Which chunks have set bits
    .index(active_chunk)
);

// Combine results
assign final_index = {active_chunk, chunk_indices[active_chunk]};
```

### Conditional Priority Selection
```systemverilog
// Select between different priority schemes
assign priority_vector = use_high_priority ? high_pri_requests : 
                        use_fair_mode ? fair_requests : 
                        normal_requests;

find_last_set #(.WIDTH(N)) flexible_priority (
    .data(priority_vector),
    .index(selected_request)
);
```

### Dynamic Width Processing
```systemverilog
// Process variable-width data
logic [MAX_WIDTH-1:0] padded_data;
assign padded_data = {{(MAX_WIDTH-actual_width){1'b0}}, input_data};

find_last_set #(.WIDTH(MAX_WIDTH)) variable_fls (
    .data(padded_data),
    .index(raw_index)
);

// Adjust result for actual width
assign adjusted_index = (raw_index >= actual_width) ? 0 : raw_index;
```

## Verification Strategies

### Comprehensive Test Coverage
```systemverilog
// Test single bit at each position
for (int i = 0; i < WIDTH; i++) begin
    test_vector = 1 << i;
    expected_result = i;
    // Verify find_last_set returns i
end

// Test multiple bits with known MSB
test_vector = 8'b10101010;
expected_result = 7;  // MSB position

// Test edge cases
test_vector = 8'b00000000;  // All zeros
expected_result = 0;        // Default
```

### Random Testing
```systemverilog
// Random bit patterns
repeat (1000) begin
    random_vector = $random();
    expected = calculate_msb_position(random_vector);
    // Verify against reference function
end
```

## Related Modules
- **find_first_set**: LSB-priority search
- **encoder_priority_enable**: Enhanced priority encoder
- **leading_one_trailing_one**: Position detection for Johnson counters

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
