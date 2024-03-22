---
title: Counter Johnson
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `counter_johnson` module defined in `rtl/common/counter_johnson.sv` is a Verilog implementation of a Johnson counter with a configurable width. The Johnson counter is a modified ring counter where the inverted output from the last flip-flop is fed back to the input of the first flip-flop. This results in a sequence of bit patterns useful in specific digital circuits.

## Parameters

- `WIDTH`: Integer parameter that sets the width of the counter. This determines how many stages the Johnson counter will have. The default width is set to 4.

## Ports

- `i_clk`: Input wire (clock) - Connects to the system clock to drive the counter.

- `i_rst_n`: Input wire (reset, active low) - Resets the counter to zero when asserted low.

- `i_enable`: Input wire (enable) - Allows the counter to increment when high.

- `o_counter_gray`: Output register [WIDTH - 1:0] - The output register that holds the current state of the Johnson counter.

## Functionality

- **Reset**: On the negative edge of `i_rst_n`, the output register `o_counter_gray` is reset to 0. This initializes the state of the counter.

- **Counter progression**: On the positive edge of `i_clk` and when `i_enable` is high, the counter advances to the next state. It does this by shifting the bits of `o_counter_gray` left by one position, with the leftmost bit being the inverse of the rightmost bit before the shift.

## Usage

Instantiate the module in the Verilog design and connect the `i_clk`, `i_rst_n`, and `i_enable` ports to the appropriate signals. Then, connect the `o_counter_gray` port to the circuit that requires the Johnson counter output.

## Example Instantiation

```verilog

counter_johnson #(

.WIDTH(4)

) u_counter_johnson (

.i_clk(clk),

.i_rst_n(rst_n),

.i_enable(enable),

.o_counter_gray(counter_output)

);

```

---

[Return to Index](/docs/mark_down/rtl/)

---
