---
title: Math Adder Brent Kung black
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This module performs a single stage of the Brent-Kung adder logic in constructing a parallel prefix adder. Brent-Kung adders are known for their logarithmic depth in terms of gates, significantly improving the speed for addition in VLSI design.

## Time Scale

```verilog

`timescale 1ns / 1ps

```

The time scale directive specifies that the simulation time unit is one nanosecond, and the simulation time precision is one picosecond. This is especially important for synthesis and timing analysis in digital designs.

### Ports

The module consists of the following ports:

- **Inputs:**

- `i_g`: The generated value from the previous stage.

- `i_p`: The propagate value from the previous stage.

- `i_g_km1`: The generated value from the previous group or stage (k minus 1).

- `i_p_km1`: The propagate value from the previous group or stage (k minus 1).

- **Outputs:**

- `ow_g`: The output generates value.

- `ow_p`: The output propagate value.

### Functionality

The module performs the following logical operations:

- `ow_g = i_g | (i_p & i_g_km1);`: This expression computes the output carry generation. It will generate a carry if the current stage generates a carry (`i_g`) or if the current stage propagates a carry (`i_p`) and the previous stage generates a carry (`i_g_km1`).

- `ow_p = i_p & i_p_km1;`: This expression computes the output propagation. It indicates that both the current and the previous stages propagate the carry.

This module is usually instantiated within a larger Brent-Kung adder circuit where multiple such stages are cascaded to implement a fast adder.

**Note:** It is essential to ensure that the module's signals (`i_g`, `i_p`, `i_g_km1`, `i_p_km1`) are driven correctly by the instantiating module, as these signals play a crucial role in the accurate computation of the addition result.

---

[Return to Index](/docs/mark_down/rtl/)

---
