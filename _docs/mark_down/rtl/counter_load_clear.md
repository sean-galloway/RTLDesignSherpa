---
title: Counter Load Clear
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog code defines a module named `counter_load_clear` that functions as a counter capable of loading a specified value, clearing itself, and indicating when a matching value has been reached.

## Module Parameters

- `MAX`: An integer parameter with a default value of 32 that sets the maximum range of the counter.

## Ports

Inputs:

- `i_clk`: The input clock signal.

- `i_rst_n`: The active-low reset signal.

- `i_clear`: The input signal to clear the counter to zero.

- `i_increment`: The input signal (unused) indicating the increment action for the counter.

- `i_load`: The input signal to load the match value in the counter.

- `i_loadval`: The input value to be loaded into the counter when `i_load` is asserted. Its width is determined by the logarithm (base 2) of `MAX`.

Outputs:

- `o_count`: The current count value of the counter. Its width is as computed for `i_loadval`.

- `ow_done`: A boolean output signal that indicates the counter has reached the match value.

## Functionality

1\. **Initialization**:

- Upon reset (i.e., if `i_rst_n` is low), the `o_count` and `r_match_val` are set to zero.

2\. **Counting Logic**:

- The `r_next_count` logic computes the next count value.

- If `i_clear` is high, the counter resets to `0`.

- If `o_count` equals `r_match_val`, the counter resets to `0`.

- Otherwise, the counter increments by 1.

3\. **Value Loading**:

- When the `i_load` signal is high, the value on `i_loadval` is loaded into `r_match_val`.

4\. **Counter Update**:

- On the positive edge of `i_clk`, if not reset, the `o_count` is updated with the value of `r_next_count`.

5\. **Match Detection**:

- The `ow_done` signal is asserted (set to high) when the `o_count` equals `r_match_val`, indicating that the match value has been reached.

**Note**: The `i_increment` input is declared but not used within the module. Design intent should be clarified, and if not required, this signal should be removed for clarity and to avoid potential confusion.

---

[Return to Index](/docs/mark_down/rtl/)

---
