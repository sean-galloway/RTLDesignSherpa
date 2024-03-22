---
title: Hex to 7 seg
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `hex_to_7seg` module is a Verilog code snippet that converts a 4-bit hexadecimal input into a 7-segment display output. Generally used in digital electronics to display hexadecimal numbers on 7-segment LED or LCDs. Below is the fully documented markdown for `hex_to_7seg` at `rtl/common/hex_to_7seg.sv`.

## Inputs

- `i_hex [3:0]`: A 4-bit input representing the hexadecimal value to be displayed on the seven-segment display. The valid input range is from `0x0` to `0xF`.

## Outputs

- `ow_seg [6:0]`: A 7-bit output representing the state of each segment (a-g) in the seven-segment display where a '0' bit turns the segment on and a '1' bit turns it off.

## Functionality

- The `always_comb` block contains a `case` statement that matches the input hexadecimal value to its corresponding 7-bit output configuration for the seven-segment display to visualize the correct digit.

## Usage

- To use the `hex_to_7seg` module, instantiating and connecting it to the rest of the digital system is required, ensuring the `i_hex` input is driven with the hexadecimal value to be displayed, and the `ow_seg` output is connected to a seven-segment display unit or further processing logic.

---

[Return to Index](/docs/mark_down/rtl/)

---
