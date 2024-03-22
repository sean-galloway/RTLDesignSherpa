---
title: Reverse Vector
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

It defines a simple utility for bit-reversing vectors.

## Functionality

The `reverse_vector` module takes an input vector `i_vector` and outputs `o_vector`, which is the bit-reversed version of the input. The number of bits in the vectors can be specified via the parameter `WIDTH`, with a default of 32 bits.

## Parameters

- `WIDTH` (int): The input and output vector width. It defines how many bits are to be reversed. It has a default value of 32, which means the vectors will, by default, be 32-bit wide.

## Inputs

- `i_vector` (WIDTH-1:0): This input bit vector must be reversed. The `WIDTH` parameter defines its size.

## Outputs

- `o_vector` (logic [WIDTH-1:0]): The output bit vector holding the reversed bits from `i_vector`. The bit with the lowest index of the input vector becomes the bit with the highest index of the output vector and vice versa.

## Internal Logic

The module contains an `always_comb` block that implements the bit-reversing logic using a `for` loop. This loop iterates over each bit of the input vector and assigns it to the corresponding position in the output vector such that:

```verilog

o_vector[(WIDTH-1)-i] = i_vector[i];

```

This effectively reverses the order of the bits in the vector, with index 0 becoming the last index (WIDTH-1).

---

[Return to Index](/docs/mark_down/rtl/)

---
