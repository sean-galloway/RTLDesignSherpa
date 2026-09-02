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

# Johnson-to-binary converter (`johnson2bin.sv`)

## Overview

`johnson2bin` converts Johnson counter codes to binary -- the piece that makes
asynchronous FIFOs with non-power-of-2 depths possible. Standard Gray-to-binary
conversion won't do the job here; the Johnson sequence has its own structure,
and decoding it takes position detection rather than XOR reduction.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `JCW` | 10 | Johnson Counter Width (equals FIFO DEPTH) |
| `WIDTH` | 4 | Binary output width (typically `$clog2(DEPTH) + 1`) |

: johnson2bin parameters

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` | input | 1 | Clock input. Declared but unused; the module is combinational. |
| `rst_n` | input | 1 | Active-low reset. Declared but unused; the module is combinational. |
| `gray` | input | JCW | Johnson counter input (misleadingly named "gray") |
| `binary` | output | WIDTH | Binary output representing position in sequence |

: johnson2bin ports

## Functional Description

### The Johnson sequence

Johnson counters are **shift registers with inverted feedback**:

```
For JCW=6 (DEPTH=6):
State 0:  000000  ← Initial state
State 1:  000001  ← Shift left, insert ~MSB (1)
State 2:  000011
State 3:  000111
State 4:  001111
State 5:  011111
State 6:  111111  ← All 1s (fill complete)
State 7:  111110  ← Shift left, insert ~MSB (0)
State 8:  111100
State 9:  111000
State 10: 110000
State 11: 100000
State 0:  000000  ← Cycle complete (12 states total)
```

> **Fill direction.** This library shifts in at the LSB. `counter_johnson.sv`
> implements `counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]}`,
> so ones enter at bit 0 and march upward. An earlier revision of this page showed
> the mirror image (ones entering at the MSB), which is also a valid Johnson
> counter but is *not* the one this library builds -- and both worked conversion
> examples inherited the error. Note that external references frequently use the
> MSB-fill convention, so check against `counter_johnson.sv` rather than against
> a textbook.

The properties that matter for decoding:

- **Single bit transitions**: only one bit changes per state
- **Two phases**:
  - **First half** (0 to DEPTH-1): filling with 1s from the **right** (ones
    enter at bit 0 and march upward: 000000 → 000001 → 000011 → ...)
  - **Second half** (DEPTH to 2×DEPTH-1): emptying 1s from the **right**
    (111111 → 111110 → 111100 → ...)
- **Wrap indicator**: the MSB says which half of the cycle you're in

### The algorithm

The conversion works by **position detection** -- finding the transition between
the 1s and the 0s:

```systemverilog
if (w_all_zeroes || w_all_ones) begin
    w_binary = {WIDTH{1'b0}};
end else if (gray[JCW-1]) begin
    // Second half: use trailing one position directly
    w_binary = {{(WIDTH-N){1'b0}}, w_trailing_one};
end else begin
    // First half: use leading one + 1
    w_binary = {{(WIDTH-N){1'b0}}, (w_leading_one + 1'b1)};
end
```

Position detection itself is farmed out to a helper:

```systemverilog
leading_one_trailing_one #(
    .WIDTH(JCW)
) u_leading_one_trailing_one (
    .data(gray),
    .leadingone(w_leading_one),
    .trailingone(w_trailing_one),
    .all_zeroes(w_all_zeroes),
    .all_ones(w_all_ones),
    .valid(w_valid)
);
```

### Three-part binary construction

```systemverilog
assign binary[WIDTH-1]   = gray[JCW-1];                 // MSB = wrap indicator
assign binary[WIDTH-2:0] = w_binary[WIDTH-2:0];         // Lower bits = position
```

### Width calculations

```systemverilog
localparam int N = $clog2(JCW);                         // Address bits needed
localparam int PAD_WIDTH = (WIDTH > N+1) ? WIDTH-N-1 : 0; // Padding if needed
```

### Why this algorithm works

**First half (MSB = 0).** The pattern is `000...0111...1` -- zeros followed by
ones. The leading-one position tells you how far the fill has progressed:
position = leading_one + 1, because we've filled (leading_one + 1) positions
with 1s.

**Second half (MSB = 1).** The pattern flips to `111...1000...0` -- ones
followed by zeros. We're emptying from the right, and the trailing-one position
shows how far: position = trailing_one.

### Worked conversions

#### First Half Conversion (MSB = 0)
```
JCW=6, WIDTH=$clog2(6)+1=4 -- the legal pairing, and what both FIFOs instantiate.

Johnson: 001111 (set bits {0,1,2,3}: w_leading_one = 3, w_trailing_one = 0)
Logic: gray[5]=0 → first half, position = w_leading_one + 1 = 3 + 1 = 4
Binary: 4'b0100 = {wrap=0, addr=4} -- Johnson state 4
```

#### Second Half Conversion (MSB = 1)
```
Johnson: 111000 (set bits {3,4,5}: w_leading_one = 5, w_trailing_one = 3)
Logic: gray[5]=1 → second half, position = w_trailing_one = 3
Binary: 4'b1011 = {wrap=1, addr=3} -- Johnson state 9 of 12

The output is not the number 9. It is the FIFO pointer {wrap, addr}: the ninth
state of the sequence is address 3 on the second lap. Reading `4'b1011` as the
decimal 11 and expecting 9 is the usual first confusion with this module.
```

#### Special Cases
```
Johnson: 000000 → Binary: 4'b0000 (all zeros case)
Johnson: 111111 → Binary: 4'b1000 (all ones: lower bits forced to 0, but the RTL
         unconditionally sets binary[WIDTH-1] = gray[JCW-1] = 1, so the wrap
         bit is SET -- this is {wrap=1, addr=0}, NOT the same as all-zeros.
         FIFO full detection depends on this.)
```

### Comparison with standard gray2bin

| Aspect | Standard Gray2Bin | Johnson2Bin (johnson2bin) |
|--------|-------------------|--------------------------|
| **Input type** | Traditional Gray code | Johnson counter sequence |
| **Algorithm** | XOR reduction | Position detection |
| **Complexity** | Simple combinational | Complex position logic |
| **Clock requirement** | None | None (clk/rst_n ports exist but are unused) |
| **Width scaling** | Logarithmic | Linear with JCW |
| **Use case** | Power-of-2 sequences | Any sequence length |

## Timing Characteristics
The critical path runs through the position detection logic: leading/trailing
one detection, a binary addition, and the output mux. Synthesis complexity is
higher than a standard Gray conversion, and resources scale with JCW -- the
Johnson width, not its log:

```
Resources scale with JCW (Johnson Counter Width):
- Small FIFOs (JCW ≤ 16): Reasonable overhead
- Medium FIFOs (JCW = 32-64): Significant resources
- Large FIFOs (JCW > 64): May become limiting factor
```

## Usage Examples
This is where the module actually lives -- decoding the crossed pointer in
`fifo_async.sv` (`USE_JOHNSON=1`):

```systemverilog
// fifo_async.sv (USE_JOHNSON=1) usage:
johnson2bin #(
    .JCW(JCW),                    // = DEPTH
    .WIDTH(AW + 1)                // Address width + wrap bit
) rd_ptr_gray2bin_inst(
    .binary(w_wdom_rd_ptr_bin),   // Binary for arithmetic
    .gray(r_wdom_rd_ptr_gray),    // Johnson counter from CDC
    .clk(wr_clk),
    .rst_n(wr_rst_n)
);
```

## Design Notes

### The clock and reset ports are unused

`johnson2bin` declares `clk` and `rst_n` but **never uses them**. The conversion
is entirely combinational: a single `always_comb` block driven by
`leading_one_trailing_one`, which is itself combinational (one `always_comb` plus
continuous assignments, no `always_ff` anywhere).

The ports are retained so the module can be dropped into a clocked context
without an interface change, and so a future revision could register the output
without breaking callers. Tie them off to whatever the surrounding domain uses;
nothing in this module samples them. Do not expect a cycle of latency -- the
output follows `gray` combinationally, and long conversion paths must be
registered by the caller.

### When to use Johnson vs. Gray
```systemverilog
// Use Johnson counter approach when:
parameter int DEPTH = 10;  // Non-power-of-2 required
parameter int DEPTH = 6;   // Specific size needed
parameter int DEPTH = 14;  // Standard Gray won't work

// Use standard Gray approach when:
parameter int DEPTH = 8;   // Power-of-2 is acceptable
parameter int DEPTH = 16;  // Efficiency more important
parameter int DEPTH = 64;  // Large depth, resource conscious
```

### Resource planning
```systemverilog
// Resource overhead estimation:
// Standard Gray: ~log2(DEPTH) XOR gates
// Johnson: ~DEPTH comparators + position logic

// Break-even point typically around DEPTH = 16-32
```

### Verification challenges
```systemverilog
// More complex verification due to:
// 1. Two-phase sequence behavior
// 2. Position detection correctness
// 3. Special case handling (all 0s, all 1s)
// 4. Wraparound boundary conditions
```

### Invalid Johnson sequences

**Nothing checks them.** It is worth being blunt, because the `.valid(w_valid)`
port on the helper reads like it does:

```systemverilog
.valid(w_valid)  // NOT a Johnson-pattern check -- see below
```

`leading_one_trailing_one` computes `assign valid = |data`, so `valid` means
"input is nonzero" and nothing more. A pattern such as `6'b010101`, which is not
a Johnson sequence at all, drives it high. And in `johnson2bin.sv` `w_valid` is
declared, connected, and then never read -- no output carries it, no assertion
consumes it. A malformed sequence is decoded into a wrong pointer silently.

A valid Johnson pattern is one with a single 1-to-0 transition (or its mirror).
If you need that enforced, it has to come from somewhere else: the upstream
`counter_johnson` produces only legal patterns by construction, which is why the
decoder can assume them.

### Debug visibility

```systemverilog
// Monitor internal state for debugging:
// - w_leading_one: Position of leftmost 1
// - w_trailing_one: Position of rightmost 1
// - w_all_zeroes: Special case flag
// - w_all_ones: Special case flag
// - w_valid: nonzero-input flag ONLY -- not a Johnson-pattern check
```

### Common issues

1. **Invalid sequences**: non-Johnson input decodes silently to a wrong pointer
2. **Width mismatches**: JCW vs. actual Johnson counter width
3. **Phase confusion**: misunderstanding first vs. second half logic
4. **Boundary conditions**: all-zeros and all-ones handling

### Advanced topics

**Hierarchical Johnson counters.** For very large depths, a hierarchical
approach is worth considering:

```systemverilog
// Break large Johnson counter into smaller segments
// Use multiple johnson2bin instances with higher-level arbitration
```

**Alternative position detection.** Other implementations detect position
differently:

- **Priority encoders**: find first/last set bit
- **Thermometer decoders**: convert 1-hot positions
- **LUT-based**: for small, fixed widths

## Related Modules

- **counter_johnson**: Generates Johnson counter sequences
- **leading_one_trailing_one**: Position detection helper
- **fifo_async / gaxi_fifo_async (USE_JOHNSON=1)**: Primary users of this conversion
- **gray2bin**: Standard Gray-to-binary for comparison
- **fifo_control**: Uses converted binary values for status generation

## Testing

From the test suite (`val/cdc/test_johnson2bin.py`):

- **Key test scenarios**:
  - Gray Johnson Counter to Binary Converter Test
  - This test verifies the Gray Johnson counter to binary conversion functionality:
  - CONFIGURATION:
  - JCW: Johnson Counter Width (10, 12, 16, 20)
  - WIDTH: Binary output width (4, 5, 6, 8)

Run levels come from the standard grid: `REG_LEVEL=GATE|FUNC|FULL` selects the
parameter set, `TEST_LEVEL` the per-test depth. Run the whole area with
`make -C val/cdc run-all-func-parallel`, never bare pytest for suites.

## Navigation

- [← Back to CDC Index](index.md)
- [← Back to Main Documentation Index](../index.md)
