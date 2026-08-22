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

# encoder

## Overview

Converts a one-hot N-bit input back into its binary index — the inverse of a decoder. Feed it a one-hot vector, get out the position of the asserted bit in binary.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `N` | 8 | Width of one-hot input vector |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `decoded` | Input | N | One-hot input vector |
| `data` | Output | $clog2(N) | Binary encoded output representing the position of the set bit |

## Functional Description

### Operation Principle

- Scans the input vector from LSB to MSB
- Outputs the binary representation of the highest indexed set bit
- Which makes it a **priority encoder** when multiple bits are set (higher index wins)

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
- **Self-sizing**: Output width comes from `$clog2(N)`

### Core Algorithm

A combinational always block runs the priority search:

```systemverilog
always_comb begin
    data = 0;  // Default output when no bits set
    for (int i = 0; i < N; i++) begin
        if (decoded[i]) data = $clog2(N)'(i);
    end
end
```

### Automatic Width Calculation

- **Output width**: `$clog2(N)` bits
- **Example**: N=8 → 3-bit output, N=16 → 4-bit output
- **Optimal sizing**: No wasted bits in the output

### Priority Behavior

The for-loop gives you priority for free:
- Later iterations overwrite earlier results
- So the highest-indexed set bit decides the final output
- For invalid one-hot inputs, it quietly behaves as a priority encoder

### Behavioral Notes

- **For-loop order**: Creates LSB-to-MSB priority (higher index wins)
- **Default assignment**: Ensures output has known value for all inputs
- **Type casting**: `$clog2(N)'(i)` ensures proper bit width matching

## Timing

- **Propagation delay**: Depends on input width and synthesis
- **Critical path**: Runs through the for-loop comparisons
- **Setup/hold**: None (purely combinational)

## Usage Example

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

## Design Notes

### Applications

For valid one-hot inputs:
- **Interrupt acknowledgment**: Convert interrupt vector to binary ID
- **Resource arbitration**: Encode granted request to requester ID  
- **State machine encoding**: Convert one-hot state to binary
- **Position encoding**: Find position of active element

For priority encoding:
- **Multiple interrupt handling**: Encode highest priority interrupt
- **Error reporting**: Report highest severity error condition
- **Resource allocation**: Grant to highest priority requester

### Input Validation

- **Assumes one-hot input** for standard encoder behavior
- **Handles multiple bits** gracefully (acts as priority encoder)
- **Zero input** produces zero output (whether that's what you want is up to you)

### Synthesis Implications

- **Resource usage**: Typically synthesizes to multiplexer logic
- **Optimization**: Modern synthesizers chew through the for-loop just fine
- **Scalability**: Performance degrades gradually as N grows

## Related Modules

- **Decoder**: Performs inverse operation (binary to one-hot)
- **Priority Encoder with Enable**: Enhanced version with enable control
- **Find First Set**: Similar functionality with different search order

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
