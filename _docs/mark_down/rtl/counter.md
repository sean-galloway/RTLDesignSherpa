---
title: Counter
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

## Module Name

`counter`

## Description

The counter module is a simple up-counter that increments on each positive edge of the clock and resets to 0 when a predefined maximum value (`MAX`) is reached. This module can be used in various applications requiring periodic counting or timing functionality.

## Parameter

- `MAX`: The maximum count value, after which the counter resets. The default is 32767.

## Inputs

- `i_clk`: Clock signal. Drives the counting operation.
- `i_rst_n`: Active low reset signal. Resets the counter to 0 when asserted.

## Output

- `ow_tick`: A high signal for one clock cycle when the counter reaches the `MAX` value, indicating a tick or completion of a count cycle.

## Functionality

- The counter operates on the rising edge of the `i_clk` signal.
- When `i_rst_n` is low, the counter resets to 0.
  If the reset remains de-asserted on each positive edge of `i_clk`, the counter increments by 1.
- If the counter value equals `MAX`, it resets to 0 in the next cycle.
- `ow_tick` asserts high for a single clock cycle when the counter reaches the `MAX` value, providing a periodic tick signal.

## Implementation Details

- The counter `r_count` has a bit width calculated using `$clog2(MAX)`, ensuring it can represent all values up to `MAX`.
- The module is suitable for applications requiring a periodic signal or count-based events, with an easy-to-configure maximum count limit.

---

[Return to Index](/docs/mark_down/rtl/)

---
