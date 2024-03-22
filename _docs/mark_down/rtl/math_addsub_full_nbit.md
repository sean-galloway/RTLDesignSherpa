---
title: Math Adder full NBIT
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog module performs either addition or subtraction on two N-bit binary operands. The operation (addition or subtraction) depends on the mode signal `i_c`.

## Parameters

- `N`: An integer parameter defining the input operands' bit width and the output sum. The default width is 4 bits.

## Ports

- **Inputs:**

- `i_a[N-1:0]`: The first N-bit input operand.

- `i_b[N-1:0]`: The second N-bit input operand.

- `i_c`: Mode control input. A logic value of 0 selects addition and a value of 1 selects subtraction.

- **Outputs:**

- `ow_sum[N-1:0]`: The N-bit output representing the result of the addition or subtraction.

- `ow_carry`: The final carry-out signal for addition or the borrow for subtraction.

## Internal Implementation Details

- `w_c[N:0]`: An internal array of carries which is N+1 bits wide to accommodate the final carry-out or borrow.

- `w_ip[N-1:0]`: An array that holds the result of the XOR operation between `i_b` and `i_c`. This effectively performs a bitwise not on `i_b` when subtracting.

## Generators

- `gen_xor`: XORs each bit of `i_b` with `i_c` to potentially invert `i_b` when performing subtraction and assigns the result to `w_ip`.

- `gen_full_adders`: Instantiates a full adder for each bit of the inputs, where:

- The bit `i` of `i_a` and `w_ip` are the inputs to the adder.

- The input carry (`i_c`) for the 0th bit comes from the mode control input; other bits come from the lower bit's carry output.

- Each bit's sum and carry output are connected to `ow_sum` and the carry signal for the next bit, respectively.

- The final carry/borrow (`ow_carry`) is taken from the carry-out of the most significant bit's full adder.

---

[Return to Index](/docs/mark_down/rtl/)

---
