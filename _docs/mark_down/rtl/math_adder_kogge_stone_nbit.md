---
title: Math Adder Kogge Stone NBIT
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_adder_kogge_stone_nbit` module implements an N-bit Kogge-Stone adder, which is a parallel prefix form of carry look-ahead adder, providing faster addition than the classical ripple carry adder due to reduced propagation delay in calculating carries.

## Parameters

- `N`: An integer parameter that defines the width of the adder (i.e., the number of bits it can add).

## Inputs

- `i_a [N-1:0]`: A logic vector representing the first N-bit operand of the adder.

- `i_b [N-1:0]`: A logic vector representing the second N-bit operand of the adder.

## Outputs

- `ow_sum [N-1:0]`: A logic vector representing the sum of the operands.

- `ow_carry`: A logic signal representing the carry-out of the most significant bit.

## Functionality

1\. **Generate and Propagate terms (`gen_g_p`)**:

- The adder computes "generate" (`w_G`) and "propagate" (`w_P`) terms for each bit pair of the inputs, which are essential for determining the carries in a parallel manner.

2\. **Parallel Prefix Computation (`gen_kogge_stone`)**:

- Using the Kogge-Stone algorithm, the adder performs parallel prefix computation to determine all carries simultaneously quickly.

3\. **Sum Calculation (`gen_sum`)**:

- Another loop constructs the sum of the operands, considering the input bits and the previously calculated carry bits.

4\. **Final Carry Out (`ow_carry`)**:

- The carry output of the addition is given by the last computed carry, which is derived from the most significant position's operation.

---

[Return to Index](/docs/mark_down/rtl/)

---
