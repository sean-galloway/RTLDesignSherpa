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

# Priority Encoder with Enable (`encoder_priority_enable.sv`)

## Purpose
Encodes the highest priority (highest index) asserted bit in the input vector, with an enable control signal. Unlike the basic encoder, this module explicitly searches from MSB to LSB for true priority encoding.

## Ports

### Input Ports
- **`priority_in[WIDTH-1:0]`** - Priority input vector (higher index = higher priority)
- **`enable`** - Enable signal (active high)

### Output Ports
- **`encode[$clog2(WIDTH)-1:0]`** - Binary encoded output of highest priority bit position

### Parameters
- **`WIDTH`** - Input vector width (default: 8)

## Implementation Details

### Core Algorithm
```systemverilog
logic found;

always_comb begin
    // Default assignments to prevent latches
    encode = '0;
    found = 1'b0;

    if (enable == 1'b1) begin
        // Find the highest priority bit using found flag to prevent overwrites
        for (int i = WIDTH-1; i >= 0; i--) begin
            if (priority_in[i] == 1'b1 && !found) begin
                encode = $clog2(WIDTH)'(i);
                found = 1'b1;
            end
        end
    end
end
```

### Operation Principle
- **True priority encoding**: Searches from MSB (highest priority) to LSB
- **Enable control**: Only operates when enable is asserted
- **Found flag**: Prevents multiple assignments, ensuring highest priority wins
- **Clean disable**: Outputs zero when disabled

## Functional Behavior

### Priority Resolution Example (WIDTH=8)
| priority_in[7:0] | enable | encode[2:0] | Notes |
|------------------|--------|-------------|-------|
| 00000001         | 1      | 000         | Only bit 0 set |
| 10000001         | 1      | 111         | Bit 7 has highest priority |
| 01010101         | 1      | 110         | Bit 6 is highest set |
| 11111111         | 1      | 111         | Bit 7 wins among all |
| 10000001         | 0      | 000         | Disabled - output zero |
| 00000000         | 1      | 000         | No bits set |

### Key Differences from Basic Encoder
| Feature | Basic Encoder | Priority Encoder with Enable |
|---------|---------------|------------------------------|
| **Search Direction** | LSB to MSB | MSB to LSB |
| **Priority** | Higher index overwrites | True highest priority |
| **Enable Control** | None | Enable signal required |
| **Found Flag** | Implicit | Explicit prevention of overwrites |

## Design Features

### True Priority Encoding
- **MSB-first search**: `for (int i = WIDTH-1; i >= 0; i--)`
- **Single assignment**: Found flag prevents multiple writes
- **Highest wins**: First match (highest index) determines output

### Enable Control
- **Conditional operation**: Only active when `enable = 1`
- **Clean disable**: Output forced to zero when disabled
- **Power savings**: Can gate operation when not needed

### Latch Prevention
```systemverilog
// Default assignments to prevent latches
encode = '0;
found = 1'b0;
```
- Ensures all signal paths have defined values
- Prevents synthesis warnings about incomplete assignments

## Use Cases

### Interrupt Controllers
```systemverilog
encoder_priority_enable #(.WIDTH(8)) irq_encoder (
    .priority_in(interrupt_requests),
    .enable(interrupt_enable),
    .encode(highest_priority_irq)
);
```

### Resource Arbitration
```systemverilog
encoder_priority_enable #(.WIDTH(16)) arbiter (
    .priority_in(request_vector),
    .enable(arbitration_enable),
    .encode(granted_requestor)
);
```

### Error Reporting
```systemverilog
encoder_priority_enable #(.WIDTH(4)) error_encoder (
    .priority_in({fatal_error, severe_error, warning, info}),
    .enable(error_reporting_on),
    .encode(error_level)
);
```

## Timing Characteristics
- **Propagation delay**: Depends on WIDTH and synthesis optimization
- **Critical path**: Through the priority resolution loop
- **Enable response**: Immediate when enable changes
- **Setup/hold**: None (purely combinational)

## Design Considerations

### Priority Assignment
- **Bit assignment**: Higher index = higher priority
- **Planning**: Assign critical functions to higher-indexed bits
- **Documentation**: Clear priority hierarchy essential

### Performance Scaling
- **Linear complexity**: Search time increases with WIDTH
- **Synthesis optimization**: Modern tools optimize priority encoding well
- **Resource usage**: Typically maps to priority encoder primitives

### Enable Usage Patterns
- **Power management**: Disable when priority encoding not needed
- **Conditional operation**: Enable based on system state
- **Test/debug**: Disable during certain test modes

## Common Applications

### Multi-Level Interrupt Controllers
- CPU interrupt prioritization
- Nested interrupt handling
- Real-time system scheduling

### Bus Arbitration
- Multi-master bus systems
- DMA channel arbitration
- Memory access prioritization

### Error and Exception Handling
- Exception priority resolution
- Multi-source error reporting
- Diagnostic priority encoding

## Synthesis Considerations
- **Resource efficient**: Maps well to FPGA priority encoder resources
- **Timing closure**: Generally meets timing with proper constraints
- **Area scaling**: Grows approximately linearly with WIDTH

## Related Modules
- **Basic Encoder**: Simpler version without enable or true priority
- **Find Last Set**: Similar MSB-first search functionality
- **Arbiter**: Often uses priority encoders for grant generation

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
