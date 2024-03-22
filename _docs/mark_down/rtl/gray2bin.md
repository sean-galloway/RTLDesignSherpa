---
title: Gray 2 Bin
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

Converts a Gray code input to its binary equivalent.

## Overview

The `gray2bin` module is a parameterized SystemVerilog module for converting a binary number in Gray code representation to its binary equivalent.

## Parameters

- `WIDTH`: An integer parameter that defines the bit width of the input Gray code and the output binary number. The default value is set to 4.

## Ports

- `i_gray`: An input wire of logic vector with the size of `WIDTH` represents the Gray code number to be converted.

- `ow_binary`: An output wire of logic vector with the size of `WIDTH` that will hold the binary equivalent of the input Gray code.

## Functionality

The module works by iterating over `WIDTH` bits of the Gray code input, where each bit of the binary output is computed using an XOR reduction operator. This is achieved through an exclusive OR on progressively shifted versions of the Gray code input. This is because, in Gray code, each bit is exclusive OR'd with all higher significant bits to derive the equivalent binary value.

- `gen_gray_to_bin` is a generate-for block used to loop over the number of bits in the Gray code. For each bit `i`, the `ow_binary[i]` output is calculated by applying an XOR operation (`\^`) on all higher bits inclusive of the current bit position, which is practically done by shifting the Gray code `i_gray` right `i` times and then applying the XOR reduction.

The code utilizes the generate construct (`generate`-`endgenerate`), which allows for creating multiple instances or configurations of hardware based on the loop variable `i`. This makes the module flexible and easily synthesizable for different bit-widths as specified by the `WIDTH` parameter.

## Usage

No command-line options are necessary for this SystemVerilog module. To use this module, instantiate it within another RTL module or testbench with the desired `WIDTH` parameter, ensuring to connect the `i_gray` and `ow_binary` ports appropriately.

The `gray2bin` module does not rely on any external files or modules, assuming that the required files are located in the provided file path (`rtl/common/gray2bin.sv`) and the SystemVerilog file is appropriately included in the project.

---

[Return to Index](/docs/mark_down/rtl/)

---
