---
title: Glitch Free N Dff Arn
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog code defines a module named `glitch_free_n_dff_arn`, a parameterized synchronizer to provide a glitch-free output across its flip-flops. The full details are documented below:

## Parameters

- `FLOP_COUNT`: An integer representing the number of flip-flops to be cascaded, providing synchronization capabilities. The default value is 3.

- `WIDTH`: The width of the input and output buses specifies the bit-width to be synchronized. The default value is 4.

## Ports

- `i_clk`: The input clock signal to which the flip-flops are synchronized.

- `i_rst_n`: Active low (negative logic) reset signal. Resets all the flip-flop states to zero when asserted.

- `i_d`: Input data signal width specified by the `WIDTH` parameter.

- `o_q`: Registered and synchronized output signal with the same width as `i_d`.

## Array of Registers

- `r_q_array` is a packed array of logic elements used to hold the intermediate states in the chain of registers.

## Synchronous Reset Logic

- Utilizes an `always_ff` block to establish behavior on either the clock's rising edge or the reset signal's falling edge.

- Upon active low reset, set all elements of `r_q_array` to zero.

- In the absence of reset, the input data `i_d` is stored at the first position, and the current states are cascaded through the array.

## Delayed Output Assignment

- The last state in the chain (`r_q_array[FC-1]`) is assigned to the output `o_q` after a delay of 1 time unit.

## Flattening r_q_array Storage

- A flat array `flat_r_q` is created to represent the content of `r_q_array` in a single-dimensional array form.

- The `generate` block iterates over each row in the `r_q_array` and assigns to the corresponding segment in `flat_r_q`.

This module does not require additional command line options for synthesis or simulation since its behavior is entirely defined by the Verilog HDL code and its parameters.

The `glitch_free_n_dff_arn` suits digital designs requiring clean, glitch-free signals, especially when crossing clock domains or capturing inputs susceptible to metastability or glitches.

---

[Return to Index](/docs/mark_down/rtl/)

---
