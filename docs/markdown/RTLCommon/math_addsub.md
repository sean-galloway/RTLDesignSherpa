# Add/Subtract Unit

A unified N-bit add/subtract unit using two's complement arithmetic, efficiently implementing both addition and subtraction with a single control signal and shared hardware.

## Overview

The `math_addsub_full_nbit` module implements a combined adder/subtractor that performs either A + B or A - B based on a control signal. It uses two's complement arithmetic for subtraction (A - B = A + (~B) + 1), efficiently sharing the adder hardware for both operations.

**Key Feature:** Single arithmetic unit handles both operations using XOR gates and a control signal, minimizing hardware compared to separate adder and subtractor modules.

## Module Declaration

```systemverilog
module math_addsub_full_nbit #(
    parameter int N = 4      // Bit width
) (
    input  logic [N-1:0] i_a,       // Operand A
    input  logic [N-1:0] i_b,       // Operand B
    input  logic         i_c,       // Control: 0=add, 1=subtract
    output logic [N-1:0] ow_sum,    // Result output
    output logic         ow_carry   // Carry/borrow output
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int | 4 | Bit width (range: 1-64, typical: 8-32) |

## Ports

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| i_a | Input | N | Operand A |
| i_b | Input | N | Operand B |
| i_c | Input | 1 | Control signal (0=add, 1=subtract) |
| ow_sum | Output | N | Result (A+B or A-B) |
| ow_carry | Output | 1 | Carry (add) or inverted borrow (subtract) |

**Control Signal (i_c):**
- **i_c = 0**: Addition mode → Result = A + B
- **i_c = 1**: Subtraction mode → Result = A - B

**Carry Output Interpretation:**
- **Add mode (i_c=0)**: ow_carry = carry output (overflow for unsigned)
- **Subtract mode (i_c=1)**: ow_carry = ~borrow (1 if A≥B, 0 if A<B)

## Functionality

### Two's Complement Subtraction

The module implements subtraction using two's complement arithmetic:

```
A - B = A + (~B) + 1
```

**Implementation Strategy:**
1. **XOR B with control signal**: `w_ip[i] = i_b[i] ^ i_c`
   - If i_c = 0 (add): w_ip = B (unchanged)
   - If i_c = 1 (sub): w_ip = ~B (one's complement)
2. **Feed i_c as carry input**: Completes two's complement (+1)
3. **Use standard adder**: A + w_ip + i_c

### Logic Diagram

```
i_c (control) ──┬─────────────────────────────┐
                │                             │
                │  ┌───┐                      ├──> carry_in
i_b[i] ────────>│──┤XOR├──> w_ip[i] ────┐    │
                └──┴───┘                 │    │
                                     ┌───▼────▼───┐
i_a[i] ──────────────────────────────┤            │
                                     │ Full Adder ├──> ow_sum[i]
                                     │            │
carry[i-1] ──────────────────────────┤            ├──> carry[i]
                                     └────────────┘
```

### Implementation

```systemverilog
// XOR B with control signal (inverts B for subtraction)
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_xor
        assign w_ip[i] = i_b[i] ^ i_c;
    end
endgenerate

// Carry chain initialization
assign w_c[0] = i_c;  // i_c = 0 for add, 1 for subtract

// Full adder chain
generate
    for (i = 0; i < N; i++) begin : gen_full_adders
        math_adder_full fa (
            .i_a(i_a[i]),
            .i_b(w_ip[i]),      // XORed B
            .i_c(w_c[i]),
            .ow_sum(ow_sum[i]),
            .ow_carry(w_c[i+1])
        );
    end
endgenerate

assign ow_carry = w_c[N];
```

### Operation Modes

#### Addition Mode (i_c = 0)

```
w_ip[i] = i_b[i] ^ 0 = i_b[i]  (B unchanged)
w_c[0] = 0                      (no initial carry)
Result = A + B + 0 = A + B
```

#### Subtraction Mode (i_c = 1)

```
w_ip[i] = i_b[i] ^ 1 = ~i_b[i]  (B inverted = one's complement)
w_c[0] = 1                       (carry in = 1)
Result = A + (~B) + 1 = A - B   (two's complement)
```

## Usage Examples

### Simple Add/Subtract ALU

```systemverilog
logic [7:0] a, b, result;
logic sub;  // 0=add, 1=subtract
logic carry_borrow;

math_addsub_full_nbit #(.N(8)) u_alu (
    .i_a(a),
    .i_b(b),
    .i_c(sub),
    .ow_sum(result),
    .ow_carry(carry_borrow)
);

// Example: Addition
initial begin
    a = 8'd100;
    b = 8'd50;
    sub = 1'b0;  // Add mode
    #1;
    assert(result == 8'd150);
    assert(carry_borrow == 1'b0);  // No overflow
end

// Example: Subtraction
initial begin
    a = 8'd100;
    b = 8'd50;
    sub = 1'b1;  // Subtract mode
    #1;
    assert(result == 8'd50);
    assert(carry_borrow == 1'b1);  // A >= B (no borrow)
end
```

### Detecting Underflow in Subtraction

```systemverilog
logic [7:0] a, b, result;
logic underflow;

math_addsub_full_nbit #(.N(8)) u_alu (
    .i_a(a),
    .i_b(b),
    .i_c(1'b1),  // Subtract mode
    .ow_sum(result),
    .ow_carry(carry_out)
);

// For subtraction, borrow = ~carry_out
// Underflow (A < B) when carry_out = 0
assign underflow = ~carry_out;

// Example: Underflow case
initial begin
    a = 8'd50;
    b = 8'd100;
    #1;
    assert(underflow == 1'b1);  // A < B
    assert(result == 8'd206);   // Wraps: 50 - 100 + 256 = 206
end
```

### Simple Calculator

```systemverilog
module calculator (
    input  logic [7:0] operand_a,
    input  logic [7:0] operand_b,
    input  logic       operation,  // 0=add, 1=subtract
    output logic [7:0] result,
    output logic       overflow,   // Overflow (add) or underflow (sub)
    output logic       zero        // Result is zero
);

    logic carry_borrow;

    math_addsub_full_nbit #(.N(8)) u_alu (
        .i_a(operand_a),
        .i_b(operand_b),
        .i_c(operation),
        .ow_sum(result),
        .ow_carry(carry_borrow)
    );

    // Overflow/underflow detection
    assign overflow = operation ? ~carry_borrow : carry_borrow;

    // Zero flag
    assign zero = ~|result;

endmodule
```

### Multi-Function ALU

```systemverilog
typedef enum logic [1:0] {
    ALU_ADD = 2'b00,
    ALU_SUB = 2'b01,
    ALU_INC = 2'b10,
    ALU_DEC = 2'b11
} alu_op_t;

module multi_alu (
    input  logic [7:0] a, b,
    input  alu_op_t    op,
    output logic [7:0] result,
    output logic       carry_flag
);

    logic [7:0] b_mux;
    logic       ctrl;

    // Operand and control selection
    always_comb begin
        case (op)
            ALU_ADD: begin
                b_mux = b;
                ctrl = 1'b0;      // Add mode
            end
            ALU_SUB: begin
                b_mux = b;
                ctrl = 1'b1;      // Subtract mode
            end
            ALU_INC: begin
                b_mux = 8'b0;
                ctrl = 1'b1;      // A + 0 + 1 = A + 1
            end
            ALU_DEC: begin
                b_mux = 8'b1;
                ctrl = 1'b1;      // A - 1 = A + (~1) + 1
            end
        endcase
    end

    math_addsub_full_nbit #(.N(8)) u_alu (
        .i_a(a),
        .i_b(b_mux),
        .i_c(ctrl),
        .ow_sum(result),
        .ow_carry(carry_flag)
    );

endmodule
```

## Timing Characteristics

| Metric | Value |
|--------|-------|
| **Logic Depth** | 2N + 2 levels (XOR + ripple carry chain) |
| **Typical Delay (8-bit)** | ~3.2 ns @ 1.0V |
| **Max Frequency (8-bit)** | ~300 MHz |

**Logic Level Breakdown (8-bit):**
1. XOR stage: 1 level (B ^ control)
2. Carry chain: 16 levels (8 full adders × 2)
3. **Total**: 17 levels

**Critical Path:**
```
i_b[0] → XOR → FA[0] → FA[1] → ... → FA[7] → ow_carry
```

## Performance Characteristics

### Resource Utilization

| Width | LUTs (Est.) | Description |
|-------|-------------|-------------|
| 8-bit | ~18 | N XORs + N full adders |
| 16-bit | ~34 | Linear scaling |
| 32-bit | ~66 | Linear scaling |

**Area Breakdown (8-bit):**
- XOR gates: 8 LUTs
- Full adders: 8 × 2 = 16 LUTs (optimized)
- **Total**: ~18 LUTs

**Comparison:**
| Architecture | Area (relative) | Operations |
|--------------|-----------------|-----------|
| Separate Add + Sub | 2.0× | Add or Sub |
| **Add/Sub Unit** | **1.1×** | **Add and Sub** |
| Adder only (manual control) | 1.0× | Add and Sub (external invert) |

**Advantage:** ~10% area overhead vs adder-only, but integrated control simplifies system design.

## Design Considerations

### Advantages

✅ **Hardware efficiency**: Single unit for both operations
✅ **Simple control**: One bit selects operation
✅ **Standard practice**: Common in ALU designs
✅ **No separate subtractor**: Reuses adder logic

### When to Use This Module

**Appropriate Use Cases:**
- ALU designs requiring add/subtract
- Arithmetic units with mode control
- Simple calculators
- Control logic needing both operations

**Alternative Approaches:**
- **Manual control**: Use standard adder with external XOR and control (saves one XOR level if control is early)
- **Behavioral**: `assign result = sub ? (a - b) : (a + b);` (synthesis tool optimizes)

### Synthesis Considerations

**Optimization Tips:**

1. **Let synthesis infer fast carry chains** (FPGAs):
   ```tcl
   set_dont_touch false
   ```

2. **XOR placement**: XOR gates before adder may allow optimization

3. **Consider pipelining** for high frequency:
   ```systemverilog
   logic [N-1:0] r_b_conditioned;
   always_ff @(posedge clk) begin
       r_b_conditioned <= i_b ^ {N{i_c}};
   end
   ```

## Common Pitfalls

❌ **Anti-Pattern 1**: Misinterpreting carry output

```systemverilog
// WRONG: Carry means different things for add vs subtract!
if (carry) begin
    // overflow? underflow? Depends on operation!
end

// RIGHT: Interpret based on operation
logic overflow_underflow;
assign overflow_underflow = (i_c == 0) ? carry :  // overflow (add)
                                         ~carry;  // underflow (sub)
```

❌ **Anti-Pattern 2**: Using for signed arithmetic without overflow detection

```systemverilog
// WRONG: Missing signed overflow detection
logic [7:0] result_signed;
math_addsub_full_nbit u_alu (.i_c(1'b0), ...);  // Add mode
// Result may overflow for signed!

// RIGHT: Check signed overflow
logic signed_overflow;
assign signed_overflow = (i_a[N-1] == i_b[N-1]) &&
                         (ow_sum[N-1] != i_a[N-1]);
```

❌ **Anti-Pattern 3**: Forgetting XOR overhead

```systemverilog
// Be aware: XOR stage adds one logic level
// If timing is critical, consider pipelining the XOR stage
```

## Related Modules

- **math_adder_ripple_carry.sv** - Add-only (no XOR overhead)
- **math_subtractor_ripple_carry.sv** - Subtract-only (rarely used)
- **math_adder_carry_lookahead.sv** - Faster alternative for adder stage

## References

- Mano, M.M. "Digital Design." Prentice Hall, 2002.
- Hennessy, J.L., Patterson, D.A. "Computer Architecture: A Quantitative Approach." Morgan Kaufmann, 2011.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
