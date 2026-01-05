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

# Find First Set (`find_first_set.sv`)

## Purpose
Finds the index of the least significant bit (LSB) that is set to '1' in the input vector. Implements a priority encoder that favors lower-indexed bits.

## Ports

### Input Ports
- **`data[WIDTH-1:0]`** - Input data vector to search

### Output Ports
- **`index[$clog2(WIDTH)-1:0]`** - Index of the first (lowest) set bit

### Parameters
- **`WIDTH`** - Width of input data vector (default: 32)
- **`INSTANCE_NAME`** - String identifier for debug (default: "FFS")

## Implementation Details

### Core Algorithm
```systemverilog
localparam int N = $clog2(WIDTH);
logic w_found;

always_comb begin
    index = {N{1'b0}}; // Default value if no bit is set
    w_found = 1'b0;

    for (int i = 0; i < WIDTH; i++) begin
        if (data[i] && !w_found) begin
            index = i[N-1:0]; // Ensure correct bit width
            w_found = 1'b1;
        end
    end
end
```

### Search Strategy
- **Direction**: LSB to MSB (left to right, ascending index)
- **Priority**: Lower indices have higher priority
- **First match**: Stops at first '1' bit encountered
- **Found flag**: Prevents multiple assignments

## Functional Behavior

### Truth Table Examples (WIDTH=8)

| data[7:0] | index[2:0] | Description |
|-----------|------------|-------------|
| 00000001  | 000        | Bit 0 is first set |
| 00000010  | 001        | Bit 1 is first set |
| 00000100  | 010        | Bit 2 is first set |
| 00001000  | 011        | Bit 3 is first set |
| 00010000  | 100        | Bit 4 is first set |
| 00100000  | 101        | Bit 5 is first set |
| 01000000  | 110        | Bit 6 is first set |
| 10000000  | 111        | Bit 7 is first set |
| 00000000  | 000        | No bits set - default |
| 10000001  | 000        | Multiple bits - LSB wins |
| 11111111  | 000        | All bits set - bit 0 wins |

### Key Characteristics
- **LSB priority**: Always returns lowest index when multiple bits set
- **Zero default**: Returns 0 when no bits are set
- **Deterministic**: Same input always produces same output
- **Combinational**: Immediate response to input changes

## Design Features

### Width Parameterization
- **Automatic sizing**: Output width calculated as `$clog2(WIDTH)`
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
- **Purpose**: Prevents overwriting the first found result
- **Mechanism**: Once `w_found` is set, no further assignments occur
- **Result**: Only the lowest index is captured

### Bit Width Handling
```systemverilog
index = i[N-1:0]; // Ensure correct bit width
```
- **Type safety**: Explicit width matching prevents synthesis warnings
- **Truncation**: Safely handles loop variable width vs. output width

## Use Cases

### Interrupt Processing
```systemverilog
find_first_set #(.WIDTH(8)) irq_ffs (
    .data(interrupt_pending),
    .index(lowest_priority_irq)
);
```
- Process lowest-numbered interrupt first
- Fair servicing of interrupt sources

### Resource Allocation
```systemverilog
find_first_set #(.WIDTH(16)) resource_ffs (
    .data(available_resources),
    .index(allocated_resource_id)
);
```
- Allocate lowest-numbered available resource
- Round-robin allocation when combined with masking

### Error Detection
```systemverilog
find_first_set #(.WIDTH(4)) error_ffs (
    .data(error_status),
    .index(first_error_type)
);
```
- Report first error condition detected
- Prioritize error handling by position

### Bit Manipulation
```systemverilog
find_first_set #(.WIDTH(32)) bit_scan (
    .data(search_pattern),
    .index(first_set_position)
);
```
- Bit scanning operations
- Pattern analysis and parsing

## Timing Characteristics

### Propagation Delay
- **Best case**: 1 LUT delay (bit 0 set)
- **Worst case**: Multiple LUT delays (higher bits set)
- **Average case**: Depends on typical input patterns

### Critical Path
- **Path length**: Increases with WIDTH
- **Optimization**: Modern synthesizers create efficient priority encoders
- **Scaling**: Generally logarithmic complexity in hardware

## Algorithm Comparison

### vs. Find Last Set
| Aspect | Find First Set | Find Last Set |
|--------|----------------|---------------|
| **Search direction** | LSB → MSB | MSB → LSB |
| **Priority** | Lower index wins | Higher index wins |
| **Use case** | Fair allocation | Priority allocation |

### vs. Priority Encoder
| Aspect | Find First Set | Priority Encoder |
|--------|----------------|------------------|
| **Priority direction** | LSB has priority | MSB has priority |
| **Application** | Round-robin systems | Hierarchical systems |

## Design Considerations

### Input Validation
- **All zeros**: Returns 0 (may need validation in application)
- **Valid range**: All input patterns handled gracefully
- **No error conditions**: Always produces a result

### Performance Optimization
- **Synthesis**: Let tools optimize the priority encoding
- **Pipelining**: Consider registering for high-speed applications
- **Parallel**: Can process multiple vectors simultaneously

### Width Selection
- **Power of 2**: Often most efficient for synthesis
- **Arbitrary width**: Supported but may have overhead
- **Large widths**: Consider hierarchical implementation

## Common Usage Patterns

### Round-Robin Arbitration
```systemverilog
// Mask off already-serviced requests
assign masked_requests = pending_requests & ~service_mask;

find_first_set #(.WIDTH(N)) arbiter_ffs (
    .data(masked_requests),
    .index(next_grant)
);

// Update mask to exclude granted request
assign next_mask = service_mask | (1 << next_grant);
```

### Free List Management
```systemverilog
find_first_set #(.WIDTH(POOL_SIZE)) free_finder (
    .data(free_pool_bitmap),
    .index(allocated_entry)
);

// Mark entry as allocated
assign updated_bitmap = free_pool_bitmap & ~(1 << allocated_entry);
```

### Packet Classification
```systemverilog
find_first_set #(.WIDTH(NUM_RULES)) rule_matcher (
    .data(rule_match_vector),
    .index(matched_rule_id)
);
```

## Synthesis Considerations

### Resource Utilization
- **LUT usage**: Typically maps to priority encoder primitives
- **Efficiency**: Good utilization for most FPGA architectures
- **Scaling**: Linear increase in resources with WIDTH

### Timing Optimization
- **Critical paths**: May need pipeline registers for large WIDTH
- **Clock frequency**: Generally achieves high fmax
- **Constraints**: Standard combinational timing constraints apply

## Verification Considerations

### Test Scenarios
- **Single bit**: Each bit position individually
- **Multiple bits**: Various combinations
- **All zeros**: Edge case handling
- **All ones**: Maximum case behavior

### Coverage Metrics
- **Bit coverage**: Each input bit position
- **Pattern coverage**: Representative bit combinations
- **Boundary cases**: Min/max index values

## Related Modules
- **find_last_set**: MSB-first search variant
- **encoder**: Basic priority encoder
- **encoder_priority_enable**: Enhanced priority encoder with enable

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
