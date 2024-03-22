---
title: Find First Set
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `find_first_set` module is a hardware implementation in SystemVerilog designed to find the index of the first set bit (the least significant bit that is '1') in a given input vector. It is included in the path `rtl/common/find_first_set.sv`.

## Inputs/Outputs

- `i_data` (Input): A bit vector whose width is parameterized by the `WIDTH` parameter. It represents the data in which the module is to find the first set (non-zero) bit.

- `ow_index` (Output): The zero-based index of the first set bit in the `i_data` vector. Its width is calculated as one more than the base-2 logarithm of `WIDTH` to accommodate the index of the widest possible vector.

## Parameters

- `WIDTH` (Parameter - Default: 32): Defines the width of the input vector `i_data`. It is set to 32 by default and can be overridden to accommodate different vector sizes.

- `INSTANCE_NAME` (Parameter - Default: "FFS"): A user-specified string used to identify the module instance, primarily for debugging purposes.

## Internal Functionality

- `find_set_index` (Function): A function that takes a bit vector as input and iteratively checks each bit from LSB to MSB to find the first set bit. The function utilizes a for-loop and a flag (`found`) to break early when the first set bit is found. If no set bit is present in the input, the function returns an index filled with zeros.

## Command Line Options

No specific command-line option is documented in this code block since it is a hardware description intended to be synthesized or used in hardware simulation rather than executed on the command line.

However, during simulation, the commented-out `\$display` statement in the always_comb block could be uncommented to display values for debugging when simulated.

---

[Return to Index](/docs/mark_down/rtl/)

---
