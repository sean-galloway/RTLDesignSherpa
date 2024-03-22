---
title: Math Multiplier carry Lookhead
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_multiplier_carry_lookahead` module implements a binary multiplier using the carry lookahead technique to improve speed. It is parameterized by `N`, representing the number of bits for each input.

## Parameters

- `N`: The number of bits of the multiplier and multiplicand, default is 4.

## Inputs

- `i_multiplier[N-1:0]`: The N-bit multiplier input.

- `i_multiplicand[N-1:0]`: The N-bit multiplicand input.

## Output

- `ow_product[2*N-1:0]`: The 2N-bit output product resulting from multiplying the multiplier and multiplicand.

## Internal Functionality

1\. The module generates partial products between individual bits of `i_multiplier` and `i_multiplicand`.

2\. It computes carry generate (`w_generate`) and propagate (`w_propagate`) signals for each bit pair of the inputs.

3\. Utilizes carry lookahead logic to compute intermediate carries (`w_carry`) for adding partial products.

4\. Computes the final product bits and assigns them to `w_sum`.

5\. The sum (`w_sum`) represents the final product, output on `ow_product`.

## Computational Details

- The partial products are computed as bitwise ANDs of the multiplier and multiplicand.

- The generated signals are calculated as the bitwise AND of corresponding bits from the inputs.

- The propagate signals are calculated as the bitwise XOR of corresponding bits from the inputs.

- Carries are computed using a lookahead strategy to reduce the typical propagation delay in a ripple-carry adder.

- The higher bits of the product are derived from the carry outputs `w_carry[N]` downwards.

---

[Return to Index](/docs/mark_down/rtl/)

---
