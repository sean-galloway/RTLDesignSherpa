---
title: Math Adder Half
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_adder_half` module is a simple half-adder implemented in SystemVerilog. A half-adder is a combinatorial circuit that adds two binary digits and outputs a sum and a carry bit.

## Inputs

- **i_a**: Single-bit input representing the first addend.

- **i_b**: Single-bit input representing the second addend.

## Outputs

- **ow_sum**: Single-bit output representing the sum of the two inputs.

- **ow_cary**: Single-bit output representing the carry bit.

## Functionality

The half-adder performs the following logical operations:

- It XORs input `i_a` with `i_b` to produce the sum (`ow_sum`). XOR is chosen because, in binary addition, a sum bit is one only when one of the inputs is 1, not both (which is precisely the XOR operation).

- It ANDs input `i_a` with `i_b` to produce the carry-out (`ow_carry`). A carry-out bit is generated in binary addition when both inputs are 1.

## Usage

This half-adder can be instantiated within a larger design to perform bit-wise addition of binary numbers. It can be used as a building block in constructing full-adders, adder-subtraction, and arithmetic logic units (ALUs).

---

[Return to Index](/docs/mark_down/rtl/)

---
