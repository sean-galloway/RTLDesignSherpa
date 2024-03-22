---
title: Math Divider SRT
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The Math Divider SRT is a synthesized Verilog module that handles division using the SRT (Sweeney-Robertson-Tocher) division algorithm. This module divides a dividend by a divisor, providing a quotient and remainder upon completion.

## Parameters

- `DATA_WIDTH`: Defines the width of the data (dividend, divisor, quotient, and remainder). The default is 16.

## Inputs

- `i_clk`: The system clock.

- `i_rst_b`: Active low reset signal.

- `i_start`: Start signal for beginning the division operation.

- `i_dividend`: Input dividend (numerator).

- `i_divisor`: Input divisor (denominator).

## Outputs

- `o_busy`: Indicates whether the divider is currently performing division.

- `o_done`: Signals completion of division.

- `o_valid`: Indicates a valid output (invalid if divide-by-zero).

- `o_dbz`: Divide-By-Zero error flag.

- `o_quotient`: Output quotient from the division.

- `o_remainder`: Output remainder from the division.

## Internal Functionality

- Implements the division using the non-restoring method.

- Provides reset state, start conditions, divide-by-zero handling, and computation across multiple clock cycles.

---

[Return to Index](/docs/mark_down/rtl/)

---
