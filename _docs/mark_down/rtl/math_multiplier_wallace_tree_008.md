---
title: Math Multiplier wallace dadda tree 008
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

A Wallace Tree multiplier is a hardware implementation that multiplies binary numbers quickly. It speeds up the process by overlapping the addition of partial products, reducing the overall number of sequential adding stages.

## Inputs

- `i_multiplier`: A logic vector of size `N` (defaulting to 8 bits) representing the multiplier.

- `i_multiplicand`: A logic vector of size `N` (defaulting to 8 bits) representing the multiplicand.

## Outputs

- `ow_product`: A logic vector of double the size of the inputs (`2*N`, defaulting to 16 bits) that holds the product of the two input numbers.

## Parameters

- `N`: An integer parameter that sets the width of the input operands (default is 8).

## Internal Functionality

The internal workings of the module involve the following steps:

1\. **Partial Product Generation**: Each bit of `i_multiplier` is ANDed with each bit of `i_multiplicand` to generate the partial products.

2\. **Partial Product Reduction**: The partial products are then reduced using a series of half and full adders arranged as a Wallace tree. This involves adding pairs of bits and propagating carry bits to successively higher bit positions.

3\. **Final Addition Stage**: The reduced partial products are combined to generate the final product. The sum and carry out of each addition are used in subsequent additions until all partial products are combined into the final product, which is the multiplication result.

4\. **Product Assignment**: The final product is assigned to the output vector `ow_product`.

**Note**: The module also requires working `math_adder_half` and `math_adder_full` sub-modules, which implement a half and full adder.

---

[Return to Index](/docs/mark_down/rtl/)

---
