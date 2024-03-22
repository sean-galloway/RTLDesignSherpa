---
title: Math Multiplier Booth's
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

Booth's multiplier algorithm is used in computer architecture to multiply binary numbers efficiently. It reduces the number of arithmetic operations by encoding runs of zeros and ones in the binary representation of the numbers.

## Inputs and Outputs

- `i_multiplier`: A signed input representing the multiplier of `N` bits.

- `i_multiplicand`: A signed input representing the multiplicand of `N` bits.

- `ow_product`: A signed output providing the multiplication result of `2*N` bits.

## Parameters

- `N`: The width in bits of the multiplier and multiplicand. The default is 16 bits.

- `Nd2`: Half the width of `N` used for intermediate calculations.

## Internal Logic

- Booth's algorithm is computed through encoding and selecting operations. These steps are performed with packed arrays `w_select` for selection encoding, `w_MxS` for the encoded value, and `w_shift_MxS` for the shifted partial products.

- `inv_i_multiplier` computes the two's complement of `i_multiplier` for subtraction cases in Booth's algorithm.

- The encoded multiplier selections are computed for individual bits and pairs, adjusting for the algorithm's specifics and corner cases.

## Booth's Algorithm Implementation

1\. Encoding the selection by examining the adjacent bits of `i_multiplicand` and an appended zero.

2\. Execution of the encoded multiplier according to Booth's algorithm rules.

- Cases where the selection is `001` or `010` lead to adding the multiplier.

- A `011` selection corresponds to the original multiplier shifted left by one bit.

- A `100` selection signifies subtracting the multiplier (two's complement used) shifted left by one bit.

- The two's complement of the multiplier is used for selections `101` and `110`.

- All other cases result in a zero addition.

3\. Shifting of the encoded and selected multiplier according to its position.

4\. Computation of the final product using a hierarchical adder `math_adder_hierarchical` with the shifted partial products as inputs.

## Command Line Debugging (Optional)

- A `ifdef DEBUG` block is included to allow optional debugging information to be printed to the console. This block outputs the bits of `i_multiplier`, `i_multiplicand`, and the product for analysis and is triggered in simulation only if the `DEBUG` macro is defined.

---

[Return to Index](/docs/mark_down/rtl/)

---
