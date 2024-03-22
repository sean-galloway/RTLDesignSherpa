---
title: Math Multiplier dadda tree 008
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

A Dadda Tree multiplier is an algorithm used in digital electronics to multiply binary numbers quickly. It optimizes the number of partial products generated, reducing the computational complexity compared to traditional methods.

## Module Parameters

- **N**: An integer parameter that sets the multiplier's bit-width and multiplicand. By default, N is set to 8.

## Ports

- **i_multiplier [`N-1:0`]**: An N-bit input representing the multiplier.

- **i_multiplicand [`N-1:0`]**: An N-bit input representing the multiplicand.

- **ow_product [`2*N-1:0`]**: A 2\*N-bit output representing the calculated product of the multiplier and multiplicand.

## Internal Functionality

The module first generates the partial products for each multiplier and multiplicand bit pair. Then, it employs half-adders (HA) and carry-save adders (CSA) to iteratively reduce the partial product matrix row count until two rows remain. These rows are then summed to produce the final product. This reduction technique is known as the Dadda reduction tree.

For each stage in Dadda reduction:

- A half-adder (HA) reduces two-bit inputs to a sum and a carry.

- A carry-save adder (CSA) reduces three-bit inputs to a sum and a carry.

## Final Addition Stage

- The final addition stage consolidates the sum and carry from the last reduction stage into a single binary number as the product.

## Design Notes

- This multiplier module is a parameterized design, allowing it to be used for different bit-widths by changing the parameter N.

- The module assumes that both inputs are unsigned.

This module requires several instances of `math_adder_half` and `math_adder_carry_save`, which are not defined within this block. As such, implementing these blocks is assumed to be available elsewhere in the project.

---

[Return to Index](/docs/mark_down/rtl/)

---
