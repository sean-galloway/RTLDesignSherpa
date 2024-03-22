---
title: Grayj 2 bin
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `grayj2bin` module is a Verilog module designed to convert a Johnson Counter code input to its corresponding binary value. This module is parameterized and can be instantiated with different bit widths.

## Parameters

- `JCW`: The number of bits in the input Johnson code, specific to the size of the input Johnson code.

- `WIDTH`: The desired width of the output binary code. It should be large enough to represent the full range of the Johnson code values.

- `INSTANCE_NAME`: An optional parameter that can distinguish this module's multiple instances.

## Ports

- `i_clk` (input): The clock signal for the module (although not used in the provided code, it is here for potential future use).

- `i_rst_n` (input): Active-low reset signal (again not utilized in the provided code, but present for completeness and future use).

- `i_gray` (input): The input Johnson code of width `JCW`.

- `ow_binary` (output): The output binary code with the most significant bit as the "wrap bit" and the rest representing the binary value of the input Johnson code of width `WIDTH`.

## Internal Logic

Under the `always_comb` block, the conversion logic handles exceptional cases where the input Johnson code is all zeros or all ones. For standard Johnson codes, the conversion depends on whether the most significant bit is a one or a zero.

- If the input Johnson code is all zeros or all ones, `w_binary` is set to zero.

- If the most significant bit of `i_gray` is one, the leading position is the binary value.

- Otherwise, the binary value is one more than the position of the trailing one.

## Helper Module Instantiation

This block includes the instantiation of a helper module named `leading_one_trailing_one`. This module presumably calculates the leading and trailing one position, along with additional flags indicating all-zeroes or all-ones conditions.

### Ports of Helper Module `leading_one_trailing_one`

- `i_data` (input): The input Johnson code, connected to the `i_gray` input of the `grayj2bin` module.

- `ow_leadingone` (output): The leading position in the input Johnson code.

- `ow_leadingone_vector` (output): Not connected in this instantiation.

- `ow_trailingone` (output): The trailing one position in the input Johnson code.

- `ow_trailingone_vector` (output): Not connected in this instantiation.

- `ow_all_zeroes` (output): Flag indicating if the input Johnson code is all zeroes.

- `ow_all_ones` (output): Flag indicating if the input Johnson code is all ones.

- `ow_valid` (output): Flag indicating if the input is valid.

### Output Assignment

Lastly, the separated signals from `w_binary` are concatenated with the "wrap bit" to form the final output binary value, where `ow_binary[WIDTH-1]` is the "wrap bit", directly taken from the most significant bit of `i_gray`.

---

[Return to Index](/docs/mark_down/rtl/)

---
