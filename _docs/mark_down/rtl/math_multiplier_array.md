---
title: Math Multiplier Array
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The module uses a series of full adders parameterized by `math_adder_full_nbit` to construct the multiplier array. It performs bitwise AND operations between the multiplier and each bit of the multiplicand, shifting and adding these intermediate results to produce the final product.

## Parameters

- `N`: This parameter defines the width of the multiplicand and multiplier inputs and is used to scale the architecture of the multiplier array. The default value, if not specified, is 4.

## Inputs

- `i_multiplier [N-1:0]` is the N-bit wide multiplier input.

- `i_multiplicand [N-1:0]` is the N-bit wide multiplicand input.

## Outputs

- `ow_product [2*N-1:0]`: This output holds the product of the multiplication, which is 2\*N bits wide to accommodate the full range of possible products.

## Internal Functionality

- `w_sum [N*(N-1)-1:0]`: Wire used to hold intermediate sum results from the full adders.

- `w_and [N-1:0]`: Wire calculated bitwise AND between the multiplier and each bit-scaled multiplicand.

- `w_o_c [N-1:0]`: Wire holds each full adder's carry output.

The multiplication is performed by iteratively processing each bit of the multiplicand with a series of full adders implemented using the `math_adder_full_nbit` module. The first full adder's output is assigned to the two least significant bits of the final product (`ow_product`), and the iterative full adders process the remaining bits through a `generate` loop to scale with the size of the inputs.

Note that this module assumes the existence of the `math_adder_full_nbit` module, which would be another SystemVerilog file/module not provided here. It is also assumed that this module is synthesizable and follows best practices for Verilog coding.

---

[Return to Index](/docs/mark_down/rtl/)

---
