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

# Encoder Module (`encoder.sv`)

## Purpose
Converts a one-hot N-bit input to a binary encoded output. Performs the inverse operation of a decoder, encoding the position of the asserted bit into binary format.

## Ports

### Input Ports
- **`decoded[N-1:0]`** - One-hot input vector

### Output Ports
- **`data[$clog2(N)-1:0]`** - Binary encoded output representing the position of the set bit

### Parameters
- **`N`** - Width of one-hot input vector (default: 8)

## Implementation Details

### Core Algorithm
The encoder uses a combinational always block with a priority search:

```systemverilog
always_comb begin
    data = 0;  // Default output when no bits set
    for (int i = 0; i < N; i++) begin
        if (decoded[i]) data = $clog2(N)'(i);
    end
end
```

### Operation Principle
- Searches through input vector from LSB to MSB
- Outputs the binary representation of the highest indexed set bit
- Acts as a **priority encoder** when multiple bits are set (higher index wins)

## Functional Behavior

### Truth Table Example (N=8, output width=3)
| decoded[7:0] | data[2:0] | Notes |
|--------------|-----------|-------|
| 00000001     | 000       | Bit 0 set |
| 00000010     | 001       | Bit 1 set |
| 00000100     | 010       | Bit 2 set |
| 00001000     | 011       | Bit 3 set |
| 00010000     | 100       | Bit 4 set |
| 00100000     | 101       | Bit 5 set |
| 01000000     | 110       | Bit 6 set |
| 10000000     | 111       | Bit 7 set |
| 00000000     | 000       | No bits set |
| 10000001     | 111       | Multiple bits - highest wins |

### Key Characteristics
- **Priority encoding**: Higher-indexed bits take precedence
- **Zero default**: Outputs 0 when no input bits are set
- **Combinational**: Immediate response to input changes
- **Self-sizing**: Output width automatically calculated using `$clog2(N)`

## Design Features

### Automatic Width Calculation
- **Output width**: `$clog2(N)` bits
- **Example**: N=8 → 3-bit output, N=16 → 4-bit output
- **Optimal sizing**: No wasted bits in output

### Priority Behavior
The for-loop structure creates implicit priority:
- Later iterations overwrite earlier results
- Highest-indexed set bit determines final output
- Behaves as priority encoder for invalid one-hot inputs

## Use Cases

### Valid One-Hot Inputs
- **Interrupt acknowledgment**: Convert interrupt vector to binary ID
- **Resource arbitration**: Encode granted request to requester ID  
- **State machine encoding**: Convert one-hot state to binary
- **Position encoding**: Find position of active element

### Priority Encoding Applications
- **Multiple interrupt handling**: Encode highest priority interrupt
- **Error reporting**: Report highest severity error condition
- **Resource allocation**: Grant to highest priority requester

## Timing Characteristics
- **Propagation delay**: Depends on input width and synthesis
- **Critical path**: Through the for-loop comparisons
- **Setup/hold**: None (purely combinational)

## Design Considerations

### Input Validation
- **Assumes one-hot input** for standard encoder behavior
- **Handles multiple bits** gracefully (acts as priority encoder)
- **Zero input** produces zero output (may or may not be desired)

### Synthesis Implications
- **Resource usage**: Typically synthesizes to multiplexer logic
- **Optimization**: Modern synthesizers optimize the for-loop efficiently
- **Scalability**: Performance degrades gradually with increasing N

## Common Usage Patterns

### Interrupt Controller
```systemverilog
encoder #(.N(8)) int_encoder (
    .decoded(interrupt_pending),
    .data(interrupt_id)
);
```

### Arbiter Output Encoding
```systemverilog
encoder #(.N(16)) grant_encoder (
    .decoded(grant_vector),
    .data(granted_id)
);
```

## Related Modules
- **Decoder**: Performs inverse operation (binary to one-hot)
- **Priority Encoder with Enable**: Enhanced version with enable control
- **Find First Set**: Similar functionality with different search order

## Behavioral Notes
- **For-loop order**: Creates LSB-to-MSB priority (higher index wins)
- **Default assignment**: Ensures output has known value for all inputs
- **Type casting**: `$clog2(N)'(i)` ensures proper bit width matching

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
