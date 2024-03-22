---
title: Sort
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This Verilog module implements a bubble sort algorithm for sorting `NUM_VALS` values of `SIZE` bits each. The module is implemented as a generic template that can be configured for different sizes and lengths of data vectors. The sorting operation is combinatorial, meaning it completes in one clock cycle. Given an array of values at `i_data`, the `o_data` will hold the sorted array after the rising edge of `i_clk`.

## Inputs/Outputs

- **i_clk**: Input clock signal to synchronize the output data transfer.

- **i_rst_n**: Active low reset input initializes the output data to zero.

- **i_data**: Flat input data signal representing an array of `NUM_VALS` values, each `SIZE` bits wide.

- **o_data**: Flat output data signal that provides the sorted results of `i_data`.

## Functionality

- The module initializes the output to zero upon reset.

- Data input is unpacked from a single flat signal into an array (`w_array`) for easy manipulation.

- A bubble sort algorithm is combinatorial to sort the data elements in `w_array`.

- The sorted array elements are then packed back into a flat signal (`w_sorted_bus`), which is then registered to the output on a clock edge.

- An initial block is included for dumping simulation data to a file using `\$dumpfile` and `\$dumpvars`, which is ignored during synthesis.

## Important Considerations

- The sorting algorithm works in one clock cycle for the input data size specified by `NUM_VALS`.

- The active low reset (`i_rst_n`) ensures the sorted data is reset to zero on startup or after reset.

- The module may consume significant resources and have long combinatorial paths if `NUM_VALS` is large, potentially leading to timing issues.

---

[Return to Index](/docs/mark_down/rtl/)

---
