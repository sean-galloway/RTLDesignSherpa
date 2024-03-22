---
title: Leading One Trailing One
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog module is designed to analyze a binary input and identify the positions of the leading and trailing ones. It is suitable for use within a larger digital signal processing system or any application where identifying the most significant or least significant set of bits within a binary word is important.

## Inputs and Outputs

- **i_data**: (Input) A binary word of configurable width `WIDTH`.

- **ow_leadingone**: (Output) The position of the first set bit (1) from the most significant bit.

- **ow_leadingone_vector**: (Output) A binary vector with only the leading one set.

- **ow_trailingone**: (Output) The position of the first set bit (1) from the least significant bit.

- **ow_trailingone_vector**: (Output) A binary vector with only the trailing one set.

- **ow_all_zeroes**: (Output) Indicates if all bits of `i_data` are 0.

- **ow_all_ones**: (Output) Indicates if all bits of `i_data` are 1.

- **ow_valid**: (Output) Indicates if there is at least one set bit in `i_data`.

## Parameters

- **WIDTH**: The width of the input data `i_data`.

- **INSTANCE_NAME**: A string instance name for the block instantiation.

## Details

The module calculates the indices of the leading and trailing ones using submodules `find_first_set` and `find_last_set`, respectively. A parameterizable width allows the module to handle different sizes of binary words.

### Leading and Trailing One Vectors

The submodules determine the positions of the leading and trailing ones. These positions create one-hot encoded vectors `ow_leadingone_vector` and `ow_trailingone_vector`, with only the leading and trailing bits set in a binary word of width `WIDTH`.

### Zeroes and Ones

The module also indicates whether all the bits in the input data are set (`ow_all_ones`) or cleared (`ow_all_zeroes`) and whether the input data has at least one set bit (`ow_valid`).

### Debugging Provisions

There are commented-out lines for waveform dumping when performing simulations. These lines are wrapped in directives to exclude them during synthesis `// synopsys translate_off` ... `// synopsys translate_on`.

---

[Return to Index](/docs/mark_down/rtl/)

---
