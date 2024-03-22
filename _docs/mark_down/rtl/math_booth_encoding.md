---
title: Math Adder Encoding
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_booth_encoding` module takes in a 3-bit `i_sel` signal representing a value to encode and an `N`-bit multiplicand `i_multiplicand`. It then computes a multiple of the `i_multiplicand` based on the Booth encoding of the `i_sel` value and assigns the computed value to an `N`-bit output `ow_result`. Booth encoding is a technique used in multiplication to handle positive and negative multiplicands and reduce the number of required addition operations.

Booth encoding allows recognizing -1 as 0 since subtracting one and adding 0 yields the same result in 2's complement representation used for signed number operations.

## Inputs

- `input logic [2:0] i_sel` - A 3-bit wide selection signal determining the Booth-encoded value.

- `input logic [N-1:0] i_multiplicand` - An N-bit wide multiplicand.

## Outputs

- `output logic [N-1:0] ow_result` - An N-bit wide output representing the result of applying Booth encoding to the multiplicand.

## Parameters

- `parameter int N = 4` - The default number of bits for the multiplicand and result.

## Internal Logic

The `always_comb` block implements the Booth encoding selection logic, which calculates a multiple of `i_multiplicand` corresponding to the value represented by `i_sel`. This encoding results in the following operations:

- `3'b000` and `3'b111` result in zero since multiplying by zero and negative one gives the same result in Booth encoding.

- `3'b001` transfers the multiplicand as it is, meaning a multiplication by 1.

- `3'b010` shifts the multiplicand one bit left, multiplying it by 2.

- `3'b011` computes three times the multiplicand.

- `3'b100` and `3'b110` generate the negative of twice the multiplicand.

- `3'b101` results in the negative of the multiplicand.

- For any other value of `i_sel`, it defaults to zero, though this condition should not occur under regular operation.

---

[Return to Index](/docs/mark_down/rtl/)

---
