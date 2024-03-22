---
title: Math Adder Brent Kung pg
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog module is part of the arithmetic adder design that implements a Brent-Kung prefix gate (PG). The Brent-Kung adder is a parallel prefix form of carry look-ahead adder, which provides a good compromise between area and speed, making it suitable for VLSI implementation.

The module `math_adder_brent_kung_pg` generates the propagate (P) and generate (G) signals used in the adder logic. The propagate signal indicates if a carry will propagate through a pair of bits, and the generate signal indicates if adding the two bits generates a carry.

## Inputs/Outputs

- **Inputs:**

- `i_a` (logic): First input bit of the addition, part of the input operand pair.

- `i_b` (logic): The second input bit of the addition is part of the input operand pair.

- **Outputs:**

- `ow_g` (logic): The generated signal indicates that the two input bits will generate a carry.

- `ow_p` (logic): The propagate signal indicates that a carry into the pair of bits will be carried out.

## Internal Functionality

- The generate (`ow_g`) output is high only if both inputs (`i_a` and `i_b`) are high.

- The propagate (`ow_p`) output is high if either of the inputs is high.

---

[Return to Index](/docs/mark_down/rtl/)

---
