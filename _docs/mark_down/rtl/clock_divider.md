---
title: Clock Divider
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog module serves as a clock divider, a common utility in digital design for creating multiple slower clocks from a single faster clock input. The divider allows us to downscale the clock frequency to suit various timing requirements within a digital system.

## Parameters

- `N` (default: 4): The number of output clocks to generate. This value determines the size of the output vector `o_divided_clk`.

- `PO_WIDTH` (default: 8): The width of the pickoff bit registers.

- `COUNTER_WIDTH` (default: 64): This is the width of the internal counter `r_divider_counters` used to generate the divided clocks.

## Ports

- `i_clk` (input): The input clock signal will be divided.

- `i_rst_n` (input): An active-low asynchronous reset signal. When this is low, the internal counters will reset.

- `i_pickoff_points` (input): A single vector that holds all of the pickoff point registers.

- `o_divided_clk` (output): An output vector of clock signals, each divided down from the input clock according to the corresponding `PICKOFF_BITS`.

## Internal Logic

```verilog

logic [COUNTER_WIDTH-1:0] r_divider_counters; // Counter for all input clocks

```

A register `r_divider_counters` is defined to keep the current count. Its size is `COUNTER_WIDTH - 1` to `0`, making it wide enough to count up and create divided clocks.

### Reset and Counter Logic

```verilog

always_ff @(posedge i_clk or negedge i_rst_n) begin

if (!i_rst_n) r_divider_counters \<= 0;

else r_divider_counters \<= r_divider_counters + 1;

end

```

An always_ff block to increment the counter `r_divider_counters` at every positive edge of the input clock (`i_clk`) or to reset it to 0 when the reset signal (`i_rst_n`) is active low.

### Generation of Divided Clock Outputs

```verilog

always_comb begin

for (int i = 0; i \< N; i++)

o_divided_clk[i] = (r_divider_counters[\$unsigned(PICKOFF_BITS[16*i +: 16])]);

end

```

Another always_comb block to loop through each bit in the output vector `o_divided_clk`. Each output clock picks off the appropriate bit from the counter `r_divider_counters` based on the indexes specified in `PICKOFF_BITS`. This bit becomes the divided clock signal for that output. The slicing bit `\$unsigned(PICKOFF_BITS[16*i +: 16])` dynamically selects a 16-bit segment from `PICKOFF_BITS` to use as the index into `r_divider_counters`.

## Usage

Instantiate this module in your design whenever you need multiple clock domains derived from a single clock source. Customize the `PICKOFF_BITS` to control the divide factor of each output clock relative to the input clock. Use the `COUNTER_WIDTH` to handle a wide range of divide factors.

## Design Notes

- Be mindful of choosing the divide values in `PICKOFF_BITS` to ensure they are within the counter range determined by `COUNTER_WIDTH`.

- Increasing `COUNTER_WIDTH` leads to larger divide factors but also increases hardware usage.

- Asynchronous reset is used; however, synchronous reset preference might be warranted in some designs.

- Be aware of clock domain crossing issues when using multiple clocks in your design.

---

[Return to Index](/docs/mark_down/rtl/)

---
