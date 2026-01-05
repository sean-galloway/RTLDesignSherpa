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

# Galois LFSR Module

## Purpose
The `shifter_lfsr_galois` module implements a Galois Linear Feedback Shift Register, which features distributed XOR gates at tap positions rather than a single feedback point. This architecture offers better timing characteristics and higher operating frequencies compared to Fibonacci LFSRs.

## Key Features
- Galois (internal XOR) LFSR architecture
- Distributed feedback XOR gates at tap positions
- Right-shift operation with LSB feedback
- Superior timing characteristics for high-speed operation
- Configurable tap positions and polynomial
- Seed loading and cycle detection

## Port Description

### Parameters
- **WIDTH**: Width of the LFSR register (default: 8)
- **TAP_INDEX_WIDTH**: Width of each tap index (default: 12)
- **TAP_COUNT**: Number of feedback taps (default: 4)
- **TIW**: Shorthand for TAP_INDEX_WIDTH

### Inputs
| Port | Width | Description |
|------|-------|-------------|
| `clk` | 1 | System clock |
| `rst_n` | 1 | Active-low asynchronous reset |
| `enable` | 1 | Enable LFSR operation |
| `seed_load` | 1 | Load seed value into LFSR |
| `seed_data` | WIDTH | Seed value for LFSR initialization |
| `taps` | TAP_COUNT*TIW | Concatenated tap positions |

### Outputs
| Port | Width | Description |
|------|-------|-------------|
| `lfsr_out` | WIDTH | Current LFSR value |
| `lfsr_done` | 1 | High when LFSR returns to seed value |

## Galois LFSR Architecture

### Key Architectural Differences
```
Fibonacci LFSR:                    Galois LFSR:
                                  
MSB ← [XOR of all taps] ← LSB     MSB → [XOR] → [XOR] → [XOR] → LSB
 ↓                                      ↑       ↑       ↑       ↓
Shift Right                           tap1    tap2    tap3   feedback
 ↓                                                              ↑
LSB                                                             └─────┘
```

### Advantages of Galois Architecture
- **Distributed Logic**: XOR gates spread throughout the shift register
- **Better Timing**: Shorter critical paths between flip-flops
- **Higher Frequency**: Can operate at higher clock speeds
- **Localized Routing**: Reduced interconnect complexity

## Implementation Details

### Tap Position Processing
```systemverilog
// Split concatenated tap positions
always_comb begin
    for (int i = 0; i < TAP_COUNT; i++) begin
        w_tap_positions[i] = taps[i*TIW+:TIW];
    end
end
```

### LSB Feedback Generation
```systemverilog
assign w_feedback = r_lfsr[0];
```
The feedback signal comes directly from the LSB (bit 0) of the current LFSR state.

### Galois Next State Calculation
```systemverilog
always_comb begin
    // Start with right shift (include 0 in MSB)
    next_lfsr = {1'b0, r_lfsr[WIDTH-1:1]};

    // Apply Galois feedback taps if LSB is 1
    if (w_feedback) begin
        for (int j = 0; j < TAP_COUNT; j++) begin
            if (w_tap_positions[j] > 0 && w_tap_positions[j] <= WIDTH) begin
                // Apply XOR to the tap positions
                next_lfsr[w_tap_positions[j]-1] = next_lfsr[w_tap_positions[j]-1] ^ 1'b1;
            end
        end
    end
end
```

### Sequential Update
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        r_lfsr <= {WIDTH{1'b1}};  // initialization to all 1's
    end else if (enable) begin
        if (seed_load) begin
            r_lfsr <= seed_data;
        end else begin
            r_lfsr <= next_lfsr;
        end
    end
end
```

## Special Implementation Notes

### 1. Reset to All Ones
```systemverilog
r_lfsr <= {WIDTH{1'b1}};  // initialization to all 1's
```
Unlike the Fibonacci version, this module resets to all ones, which is a valid non-zero state for immediate operation.

### 2. Combinational Next State Logic
The next LFSR state is calculated combinationally in the `always_comb` block, then registered in the `always_ff` block. This separates timing concerns from logic complexity.

### 3. Conditional XOR Application
```systemverilog
if (w_feedback) begin
    // Only apply tap XORs when LSB is 1
```
XOR operations at tap positions only occur when the LSB feedback bit is 1, implementing the proper Galois LFSR behavior.

### 4. Bounds Checking
```systemverilog
if (w_tap_positions[j] > 0 && w_tap_positions[j] <= WIDTH) begin
```
Explicit bounds checking prevents out-of-range array access and handles unused tap positions (value 0).

### 5. Right-Shift with Distributed Feedback
The basic operation is a right shift, but with XOR gates inserted at tap positions that conditionally invert bits based on the LSB feedback.

## Timing Example (4-bit Galois LFSR)

### Configuration
- WIDTH = 4
- Polynomial: x⁴ + x³ + 1 (taps at positions 4,3)
- Seed: 4'b1001

### Sequence Generation
```
Cycle | LFSR | LSB | Shift | XOR@pos4 | XOR@pos3 | Next LFSR
------|------|-----|-------|----------|----------|----------
0     | 1001 | 1   | 0100  | 0100^1   | 0000^1   | 1110
1     | 1110 | 0   | 0111  | no XOR   | no XOR   | 0111
2     | 0111 | 1   | 0011  | 0011^1   | 0001^1   | 1010
3     | 1010 | 0   | 0101  | no XOR   | no XOR   | 0101
4     | 0101 | 1   | 0010  | 0010^1   | 0000^1   | 1011
...
```

## Performance Characteristics

### Critical Path Analysis
```
Fibonacci LFSR Critical Path:
All tapped bits → Multi-input XOR → MSB flip-flop

Galois LFSR Critical Path:
Previous bit → XOR gate → Current bit flip-flop
```

### Timing Advantages
- **Shorter Logic Depth**: Each bit only sees local XOR gate
- **Parallel Processing**: All XOR operations occur simultaneously
- **Reduced Fan-out**: No single XOR gate with multiple inputs
- **Better Scaling**: Critical path doesn't grow with tap count

## Polynomial Considerations

### Tap Position Mapping
For a polynomial P(x) = x^n + x^a + x^b + ... + 1:
- Galois LFSR taps: [n, a, b, ...]
- Same polynomial works for both Fibonacci and Galois
- Different sequences produced but same mathematical properties

### Example Polynomials
| Width | Polynomial | Galois Taps | Max Period |
|-------|------------|-------------|------------|
| 4 | x⁴+x³+1 | [4,3] | 15 |
| 8 | x⁸+x⁶+x⁵+x⁴+1 | [8,6,5,4] | 255 |
| 16 | x¹⁶+x¹⁵+x¹³+x⁴+1 | [16,15,13,4] | 65535 |
| 32 | x³²+x²²+x²+x+1 | [32,22,2,1] | 2³²-1 |

## Design Trade-offs

### Galois LFSR Advantages
- **Speed**: Higher maximum clock frequency
- **Timing**: Better setup/hold characteristics
- **Scalability**: Performance doesn't degrade with tap count
- **Power**: Potentially lower dynamic power

### Galois LFSR Disadvantages
- **Complexity**: More complex combinational logic
- **Area**: May require more logic gates for many taps
- **Debug**: Harder to trace intermediate states
- **Understanding**: Less intuitive than classical Fibonacci

## Applications

### High-Speed Systems
```systemverilog
// Use Galois LFSR for high-frequency applications
// Clock rates > 500MHz where timing is critical
```

### Communications
```systemverilog
// Spread spectrum systems requiring fast sequence generation
// Real-time scrambling/descrambling applications
```

### Cryptography
```systemverilog
// Stream cipher implementations
// Key sequence generation
```

### Testing
```systemverilog
// High-speed BIST pattern generation
// Fast pseudo-random test vectors
```

## When to Choose Galois over Fibonacci

### Use Galois LFSR When:
- High clock frequency is required (>100MHz)
- Timing closure is challenging
- Multiple taps are needed (>3 taps)
- Power consumption is critical
- Synthesis tools favor distributed logic

### Use Fibonacci LFSR When:
- Educational/demonstration purposes
- Legacy system compatibility required
- Very few taps (2 taps or less)
- Area is more critical than speed
- Debugging capabilities are important

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
