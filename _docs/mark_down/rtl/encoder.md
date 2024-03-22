---
title: Encoder
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `encoder` module is a SystemVerilog block designed for encoding a binary input into a one-hot encoding format. This block is typically used for converting binary numbers to an index form where the bit position is indicated as 'hot' (logic high) in a one-hot encoded output.

## Parameters

- `N`: The binary input's width, configurable through the parameter. The default value is set to 8.

## Ports

- `input logic [N-1:0] i_in`: This is the binary encoded input signal with a width defined by the parameter `N`.

- `output logic [\$clog2(N)-1:0] o_out` : This is the one-hot encoded output signal. Its width is determined by the ceiling log base 2 of `N`, which corresponds to the minimum number of bits needed to encode the input width `N` into a one-hot representation.

## Functionality

The module uses a combinatorial always block to iterate over each bit of the input signal. It initializes the output signal `o_out` to 0, and then for each bit in the input `i_in`, if the current bit is high (logic 1), it assigns the bit position `i` to the output signal `o_out`. Thus, the module produces a one-hot encoded output where the index of the first bit high in the input is represented.

The code describes an encoder that converts an N-bit input signal to an index value indicating the first '1' position in the input. This is commonly used in scenarios where binary-to-priority encoding is required.

## Additional Notes

- The encoder module would assert zero to the output if no bit is set in the input.

- The encoder does not handle multiple high bits; it will give the least significant high bit position.

---

[Return to Index](/docs/mark_down/rtl/)

---
