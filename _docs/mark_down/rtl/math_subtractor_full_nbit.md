---
title: Math Subtractor full nbit
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_subtractor_full_nbit` module is a parameterized Verilog module that implements an N-bit subtractor with borrow-in and borrow-out functionality. This module is typically used in applications that require precise arithmetic operations, such as ALUs (Arithmetic Logic Units) or custom math processors.

## Parameters

- `N`: An integer parameter that defines the width of the operands and the result. It defaults to 4 bits if not specified during instantiation.

## Ports

- `i_a [N-1:0]`: First operand of the subtraction, where N is the bit width as defined by the module's parameter.

- `i_b [N-1:0]`: Second operand of the subtraction.

- `i_b_in`: Borrow-in flag, considered in the subtraction operation.

- `ow_d [N-1:0]`: Output port for the N-bit difference result of `i_a` and `i_b` subtraction.

- `ow_b`: Borrow-out flag indicating if the result required a borrow from a higher significant bit.

## Internal Functionality

- The subtractor uses a generate loop to create N instances of a basic full subtractor module (assumed to be `math_subtractor_full`).

- Each instance calculates the result for one bit of the operands considering the borrow input.

- Borrows are chained across instances: the borrow-out of one instance serves as the borrow-in for the next significant bit.

- The very first borrow-in is connected to the `i_b_in` input.

- The last borrow-out becomes the output `ow_b` of this module.

## Notes

This code assumes the existence of a `math_subtractor_full` module, which should be defined elsewhere, and performs the single-bit subtraction with borrow. This block doesn't show the implementation of `math_subtractor_full` and how it is included or referenced.

The code block uses the `generate for` loop to create a subtractor for each bit, where each subtractor is connected in series to enable borrow chaining.

---

[Return to Index](/docs/mark_down/rtl/)

---
