---
title: Counter Bin
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `counter_bin` module is a binary counter designed explicitly for FIFO implementations. The counter increases by one upon each clock cycle, provided that the counter is enabled by `i_enable`. When the counter reaches the pre-configured maximum value (`MAX`), it returns the lower bits to zero and inverts the most significant bit (MSB). This behavior allows the counter to flag when it has hit its maximum count by toggling the MSB.

## Usage

When instantiating the `counter_bin` module in a higher-level Verilog file, the desired `WIDTH` and `MAX` parameters must be passed according to the FIFO requirements. For example, if a more extensive range is required, one would increase `WIDTH` and adjust `MAX` accordingly.

## Inputs/Outputs

- `i_clk`: A clock signal that synchronizes the counting.

- `i_rst_n`: An active-low asynchronous reset signal. When asserted (driven low), it resets the counter regardless of the clock.

- `i_enable`: When high, the counter will count up. When low, the counter will halt.

- `o_counter_bin`: The output of the counter, with a specific width defined by the `WIDTH` parameter.

## Internal Functionality

The counter logic is contained within an `always_ff` block to denote flip-flop behavior, suitable for synthesis and following good coding practices for hardware description. If the enable signal is high and the count has reached `MAX - 1`, the counter checks to toggle the MSB and reset the rest. If not at the maximum value, the counter simply increments by one.

## Command Line Options

There are no specific command line options for this module. It is intended to be synthesized and included in a larger Verilog project.

---

[Return to Index](/docs/mark_down/rtl/)

---
