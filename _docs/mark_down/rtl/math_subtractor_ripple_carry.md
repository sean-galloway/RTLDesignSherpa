---
title: Math Subtractor ripple carry
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog module describes a ripple carry subtractor, a combinatorial circuit for subtracting two binary numbers. It's called "ripple carry" because the borrow signal "ripples" from each full subtractor stage to the next. The implementation is parameterized, allowing binary numbers of arbitrary width subtraction.

## Inputs & Outputs

- **i_a**: Input port (logic array of size `N-1:0`). This is the `a` input of the subtraction operation (the number from which `b` is subtracted).

- **i_b**: Input port (logic array of size `N-1:0`). This is the `b` input of the subtraction operation.

- **i_borrow_in**: Input port (logic). This represents the initial borrow-in for the subtraction.

- **ow_difference**: Output port (logic array of size `N-1:0`). This results from the subtraction `(a - b)`.

- **ow_carry_out**: Output port (logic). This is the final borrow-out signal, which can also be viewed as the carry-out in an additional operation.

## Parameters

- **N**: Integer parameter for the width of the inputs/outputs. It is set to a default value of 4 but can be modified to handle different word sizes.

## Internal Signals

- **w_borrow**: Logic array (of size `N-1:0`). This wire array carries the borrowed bits from each full subtractor stage to the next.

## Submodule

- **math_subtractor_full**: This module represents a full subtractor that handles the subtraction for a single bit, including borrowing. This submodule is instantiated repeatedly for each bit of the input numbers.

## Behavior and Implementation

- The first bit of a subtraction uses the external `i_borrow_in`.

- Subsequent bits of the subtraction are handled in a loop generated with `genvar i` and the `generate` construct. This loop creates an instance of the `math_subtractor_full` submodule for each bit of the input numbers, starting from the least significant bit and moving to the most significant bit.

- The borrow out of each stage is connected to the borrow in of the next stage (`w_borrow` wires).

- After all bits have been processed, the `ow_carry_out` output is assigned the final borrow-out signal.

## Note

The `math_subtractor_full` module referenced in this build should exist and be compatible with the interface expected in this code (`i_a`, `i_b`, `i_b_in`, `ow_d`, `ow_b` ports).

---

[Return to Index](/docs/mark_down/rtl/)

---
