---
title: Math Adder Full nbit
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_adder_full_nbit` module is a parameterized n-bit full adder implemented in SystemVerilog. It adds two n-bit binary numbers along with an initial carry-in if provided. It outputs an n-bit sum and a final carry-out. This module is often used in arithmetic circuits and processors for performing binary addition operations.

## Parameters

- `N`: Integer specifying the number of bits for the inputs and output sum. The default value is 4.

## Ports

- `i_a`: Input [`N-1:0`] - First n-bit binary number to add.

- `i_b`: Input [`N-1:0`] - Second n-bit binary number to add.

- `i_c`: Input - Initial carry-in for the addition (a single bit).

- `ow_sum`: Output [`N-1:0`] - n-bit result of the addition of `i_a` and `i_b` with the carry-in `i_c`.

- `ow_carry`: Output - Final carry-out bit of the addition operation.

## Internal Signals

- `w_c`: Logic array [`N:0`] - Internal wire used to hold the carries between individual full adders.

### Implementation Details

- The module initializes the first element of the carry array `w_c[0]` with the provided initial carry input `i_c`.

- It uses a `generate` block to instantiate `N` instances of a `math_adder_full` block in a loop. Each instance corresponds to a single-bit full adder block responsible for adding corresponding bits of `i_a` and `i_b` with the carry-in for that stage.

- The intermediate carry `w_c[i]` for each `gen_full_adders` instance is chained to the next, providing a ripple carry adder architecture.

- The final carry `w_c[N]` is assigned to the `ow_carry` output, indicating if there was an overflow from the most significant bit of the addition.

### Dependencies

The module instantiates `math_adder_full` within the generate block which suggests that there is another module/component by this name which must be defined elsewhere, typically handling the addition of individual bits.

---

[Return to Index](/docs/mark_down/rtl/)

---
