---
title: Math Adder Ripple Carry
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog module implements an `N`-bit ripple carry adder. This digital circuit takes two `N`-bit binary numbers and an input carry (if any) and provides their `N`-bit sum along with an output carry. Ripple carry adders are widely used due to their simplicity, although they are not the fastest in operations that require large bit-widths due to the carry having to propagate through each bit of the adder.

## Parameters

- `N`: An integer specifying the width of the adder in bits. The default value is 4.

## Inputs

- `i_a[N-1:0]`: A binary number representing one of the operands of the addition.

- `i_b[N-1:0]`: A binary number representing the other operand of the addition.

- `i_c`: A single-bit binary number representing the input carried from a previous addition stage (if any).

## Outputs

- `ow_sum[N-1:0]`: The `N`-bit sum resulting from the addition of `i_a`, `i_b`, and `i_c`.

- `ow_carry`: A single bit representing the carry out of the MSB of the adder. If this bit is high, it indicates an overflow of the addition for `N`-bit numbers.

## Internal Functionality

- Internally, the ripple carry adder consists of a chain of full adders, with the carry output of each feeding into the carry input of the next.

- The first full adder (`math_adder_full fa0`) takes `i_a[0]`, `i_b[0]`, and `i_c` as inputs and provides the least significant bit of the sum (`ow_sum[0]`) and the first carry (`w_c[0]`).

- Subsequent full adders are generated through a `generate for` loop, which creates a full adder for each bit i (running from 1 to N-1), with the input carry of each being the carry output of the previous stage.

## Dependencies

- `math_adder_full`: A module that represents a single-bit full adder used in each stage of this ripple carry adder construction. This module should define inputs `i_a`, `i_b`, `i_c` and outputs `ow_sum` and `ow_carry`.

---

[Return to Index](/docs/mark_down/rtl/)

---
