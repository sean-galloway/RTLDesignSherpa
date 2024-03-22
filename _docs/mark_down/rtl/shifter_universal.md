---
title: Shifter Universal
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `shifter_universal` module is a parameterized shift register capable of performing right shifts, left shifts, and parallel data loading. It uses the SystemVerilog syntax and can be configured to operate with different data widths.

## Inputs

- `i_clk`: Clock input signal for synchronizing the shifts.

- `i_rst_n`: Asynchronous active low reset to reset the output data.

- `i_select`: 2-bit select input determining the operation:

- `00`: No operation, `o_pdata` remains unchanged.

- `01`: Right shift operation.

- `10`: Left shift operation.

- `11`: Parallel load operation, `o_pdata` is loaded with `i_pdata`.

- `i_pdata`: Parallel data input of `WIDTH` size.

- `i_sdata_lt`: Serial left data input for left shifts.

- `i_sdata_rt`: Serial right data input for right shifts.

## Outputs

- `o_pdata`: Parallel data output of `WIDTH` size.

- `o_sdata_lt`: Serial left data output, reflecting the least significant bit.

- `o_sdata_rt`: Serial right data output, reflecting the most significant bit.

## Parameters

- `WIDTH`: A parameter specifying the data path's bit-width, defaulting to 4.

## Functionality

- On every positive edge of the `i_clk` clock signal, and if `i_rst_n` is not asserted, the output data `o_pdata` is updated.

- If the reset (`i_rst_n`) is asserted, `o_pdata` is cleared to zero.

- The `i_select` signal controls the data shift or load operation:

- `2'h1` for performing a right shift, where the most significant bit (MSB) is obtained from `i_sdata_rt`.

- `2'h2` for a left shift, where the least significant bit (LSB) is obtained from `i_sdata_lt`.

- `2'h3` for parallel data load, transferring `i_pdata` to `o_pdata`.

- Any other value on `i_select` results in no change to `o_pdata`.

- After the data manipulation, `o_sdata_lt` and `o_sdata_rt` provide the LSB and MSB of the `o_pdata`, respectively, for interfacing with serial data streams or further chaining of shift registers.

---

[Return to Index](/docs/mark_down/rtl/)

---
