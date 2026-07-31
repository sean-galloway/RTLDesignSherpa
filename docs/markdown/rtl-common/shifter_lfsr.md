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

# LFSR (Linear Feedback Shift Register) Module

## Purpose
The `shifter_lfsr` module is the generic Linear Feedback Shift Register:
configurable tap positions for pseudo-random number generation, support for
various LFSR polynomials, and cycle completion detection so you know exactly
when the deterministic sequence has wrapped.

## Key Features
- Configurable tap positions for different polynomial implementations
- Seed loading capability for sequence initialization
- Cycle completion detection (sequence wrap-around)
- Enable control for conditional operation
- Support for various LFSR widths and tap configurations

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `WIDTH` | — | 8 | Width of the LFSR register |
| `TAP_INDEX_WIDTH` | — | 12 | Width of each tap index |
| `TAP_COUNT` | — | 4 | Number of feedback taps |
| `TIW` | — | — | Shorthand for TAP_INDEX_WIDTH |

## Ports

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

## LFSR Theory and Implementation

### Feedback Polynomial
The LFSR implements a linear feedback shift register based on a primitive
polynomial. The feedback is calculated by XORing bits at specified tap positions.

### Tap Position Processing
```systemverilog
// Split concatenated tap positions into separate groups
always_comb begin
    for (int i = 0; i < TAP_COUNT; i++) 
        w_tap_positions[i] = taps[i*TIW+:TIW];
end

// Convert tap positions to bit mask
always_comb begin
    w_taps = 'b0;
    for (int i = 0; i < TAP_COUNT; i++)
        if (w_tap_positions[i] > 0) 
            w_taps[w_tap_positions[i]-1'b1] = 1'b1;
end
```

### Feedback Calculation
```systemverilog
assign w_feedback = ~^(r_lfsr[WIDTH-1:0] & w_taps[WIDTH-1:0]);
```
The feedback uses XNOR reduction (inverted XOR) of tapped bits, which is characteristic of maximal-length LFSR sequences.

### Shift Register Operation
```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        r_lfsr <= 'b0;
    end else begin
        if (enable) begin
            if (seed_load) 
                r_lfsr <= seed_data;
            else 
                r_lfsr <= {r_lfsr[WIDTH-2:0], w_feedback};
        end
    end
end
```

## Timing Diagrams

### Seed Loading and Operation
```
Clock:     ____╱‾╲____╱‾╲____╱‾╲____╱‾╲____╱‾╲____
enable:    ‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾
seed_load: ________╱‾‾‾‾╲________________________
seed_data: ========< SEED >========================
lfsr_out:  00000000  SEED   VAL1   VAL2   VAL3
lfsr_done: ________       __________________╱‾‾‾╲_
```

### Sequence Example (3-bit LFSR, taps=[3,2])
Feedback is `~^(lfsr & taps)` (XNOR reduction) with `taps = 3'b110`, and the
next state is `{lfsr[1:0], feedback}`. Full period is 7 (all states except the
all-ones lockout):
```
Step | LFSR | lfsr & 110 | Feedback | Next
-----|------|------------|----------|------
0    | 001  | 000        | 1        | 011
1    | 011  | 010        | 0        | 110
2    | 110  | 110        | 1        | 101
3    | 101  | 100        | 0        | 010
4    | 010  | 010        | 0        | 100
5    | 100  | 100        | 0        | 000
6    | 000  | 000        | 1        | 001  (wraps to start; period 7)
```

## Special Implementation Notes

### 1. Tap Position Encoding
- Tap positions are 1-indexed (position 1 = bit 0)
- Zero tap position is ignored (allows unused taps)
- Multiple tap positions concatenated into single bus

### 2. XNOR Feedback
- Uses XNOR (`~^`) instead of XOR for feedback
- Produces maximal-length sequences for primitive polynomials
- Different from some LFSR implementations that use XOR

### 3. Cycle Detection
```systemverilog
assign lfsr_done = (lfsr_out == seed_data) ? 1'b1 : 1'b0;
```
Detects when LFSR returns to its initial seed value, indicating completion of full pseudo-random sequence.

### 4. Left-Shift Architecture
The implementation uses left-shift with feedback to LSB, which is equivalent to
traditional right-shift LFSRs but with different bit ordering.

### 5. Zero State Handling
- Reset initializes LFSR to all zeros
- All-zeros is a **normal** state for this module, not a lockout. Feedback is
  XNOR (`~^(r_lfsr & w_taps)`), so an all-zeros register produces `~^0 = 1` and
  advances on its own -- the 3-bit example in this page shows exactly that
  (`000` follows `100`, then wraps to `001`)
- The lockout state for XNOR feedback is **all-ones**, as stated elsewhere on
  this page. The all-zeros-avoidance rule belongs to XOR LFSRs such as
  `shifter_lfsr_fibonacci`, which carries an explicit `|r_lfsr` guard
- Seed loading is therefore optional: it selects where in the sequence you
  start, but the reset state runs correctly without it

## Applications

### Pseudo-Random Number Generation
```systemverilog
// Initialize with non-zero seed
seed_data = 8'hA5;
seed_load = 1'b1;  // Load seed
// Then enable normal operation
enable = 1'b1;
seed_load = 1'b0;
// lfsr_out provides pseudo-random sequence
```

### Built-In Self-Test (BIST)
```systemverilog
// Use lfsr_done to detect test completion
if (lfsr_done) begin
    // Full test sequence completed
    test_complete = 1'b1;
end
```

### Scrambling/Descrambling
```systemverilog
// XOR data with LFSR output for scrambling
scrambled_data = input_data ^ lfsr_out;
```

## Common Use Cases
- Pseudo-random number generation
- Data scrambling and encryption
- Built-in self-test pattern generation
- CRC calculation
- Spread spectrum communications
- Test vector generation
- Noise generation for audio applications

## LFSR Polynomial Reference

The module supports various standard LFSR polynomials. Here are some common configurations:

### Popular LFSR Polynomials (XNOR taps)
| Width | Tap Positions | Max Period |
|-------|---------------|------------|
| 3 | [3,2] | 7 |
| 4 | [4,3] | 15 |
| 5 | [5,3] | 31 |
| 8 | [8,6,5,4] | 255 |
| 16 | [16,15,13,4] | 65535 |
| 32 | [32,22,2,1] | 2³²-1 |

### Example Tap Configuration for 8-bit LFSR
```systemverilog
// For WIDTH=8, polynomial x^8 + x^6 + x^5 + x^4 + 1
// Taps at positions 8,6,5,4 (1-indexed)
parameter TAP_COUNT = 4;
parameter TIW = 4;  // 4 bits enough for tap positions up to 8

// Concatenated tap positions: {8,6,5,4}
wire [TAP_COUNT*TIW-1:0] taps = {4'd8, 4'd6, 4'd5, 4'd4};
```

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
