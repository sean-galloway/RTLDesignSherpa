---
title: Math Multiplier Booth Radix 4 Encoder
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The Verilog module `math_multiplier_booth_radix_4_encoder` is designed to implement a Booth radix-4 encoder for a multiplier based on a given Booth encoding group. This encoder facilitates partial product generation in a multiplier implementing a Booth multiplication algorithm.

## Parameters

- `N`: An integer parameter that represents the width of the operands (`i_multiplier` and `i_neg_multiplier`). It defaults to 8 bits.

## Inputs

- `i_booth_group` (3 bits): The input group of bits to be encoded using the Booth radix-4 algorithm. This typically consists of three bits from the multiplicand: two bits of sequential significance and one previous bit needed to determine the correct encoding for the group.

- `i_multiplier` (N bits): The multiplier operand is supposed to be the multiplicand in a typical multiplication scenario.

- `i_neg_multiplier` (N bits): This represents the negated value of the multiplier operand and is also needed for Booth encoding to determine the output based on the group pattern.

## Outputs

- `ow_booth_out` (N+1 bits): The output of the Booth encoder is the encoded value of the `i_booth_group` combined with the necessary sign extension.

## Functionality

The functionality of the module is implemented within an `always_comb` block that uses a `case` statement to map the different Booth encoding groups to the correct output:

- `3'b001` or `3'b010`: Represents the case where the encoded value will be the multiplier itself (`i_multiplier`) with a sign extension of its last bit.

- `3'b011`: The encoded value will be twice the `i_multiplier`. This is represented by a left shift, effectively appending a '0' at the right.

- `3'b100`: Signifies that the negation of the multiplier (twice `i_neg_multiplier`) is desired, again represented by appending a '0' to `i_neg_multiplier`.

- `3'b101` or `3'b110`: The encoded value is the negated multiplier (`i_neg_multiplier`) with a sign extension of its last bit.

- For all other cases not explicitly mentioned, the output will be set to zero (`'0`), which encodes both `3'b000` and `3'b111` according to the Booth encoding rules or any invalid input.

## Command Line Options

This module has no command line options since it's a hardware description that will be synthesized onto an FPGA or be part of an ASIC design process. The parameters and options are set during the instantiation in the hardware design.

## Conclusion

This module provides a table-based approach to encoding a group of three bits for Booth multiplication, essential for high-speed, efficient multiplication operations in hardware designs.

---

[Return to Index](/docs/mark_down/rtl/)

---
