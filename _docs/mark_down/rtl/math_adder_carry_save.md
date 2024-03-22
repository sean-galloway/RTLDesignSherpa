---
title: Math Adder Carry save
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog code describes a Carry Save Adder (CSA), a digital circuit capable of adding three binary numbers simultaneously and providing the output in a carry-save form.

## Inputs

- `i_a`: This is a binary input signal representing one of the numbers to be added by the carry save adder.

- `i_b`: Similar to `i_a`, this is the second binary input signal.

- `i_c`: This binary input is the incoming carry from a previous addition stage or can be part of a three-number addition.

## Outputs

- `ow_sum`: The binary sum output of the CSA without carry propagation.

- `ow_carry`: The binary carry output of the CSA, which would be used in further stages of addition or saved for a final carry-propagate addition step.

## Functionality

The Carry Save Adder inputs three binary values and computes their sum and carry. These values are computed so the carry isn't immediately propagated to the next bit. Hence, the term "carry save." The `ow_sum` is the bitwise XOR of the inputs, which gives the correct sum in binary addition, except when a carry is generated. The detailed condition for a carry is represented by the `ow_carry`, which is an OR of all pairwise ANDs of the inputs, accounting for carries between any two of the three input bits.

---

[Return to Index](/docs/mark_down/rtl/)

---
