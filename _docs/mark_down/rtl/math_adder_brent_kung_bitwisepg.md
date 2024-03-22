---
title: Math Adder Brent Kung bitwisepg
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

This SystemVerilog module, `math_adder_brent_kung_bitwisepg`, generates propagate and signals for each bit in a Brent-Kung adder, a parallel prefix form of carry lookahead adder. It takes two input bit vectors and an input carry bit to produce respective generate and propagate signals for use in the carry computation stages of the adder.

## Module Parameters

- `N`: The input operands `i_a` and `i_b` width. This parameter is an integer value and defaults to 8.

## Inputs

- `i_a`: Input bit vector representing the first operand of size N.

- `i_b`: Input bit vector representing the second operand of size N.

- `i_c`: Input carry bit considered a starting carry for the addition.

## Outputs

- `ow_g`: Output bit vector representing the generated signals of size N+1.

- `ow_p`: Output bit vector representing the propagate signals of size N+1.

## Detailed Description

The module instantiates a bitwise propagate and generates block `math_adder_brent_kung_pg` within a loop for each bit of the inputs. The generate (`ow_g`) and propagate (`ow_p`) signals are constructed bit by bit. The brent_kung_pg sub-block likely contains logic to determine the propagate and generate values for a single bit.

- The loop instantiates `N` bitwise PG (propagate-generate) blocks, each handling a bit from the input vectors.

- The lowest bit of the propagate signal `ow_p[0]` is set to 0, as there is nothing to propagate from a non-existent lower bit.

- The lowest bit of the generate signal `ow_g[0]` is set to the input carry `i_c`, considering that for the LSB, the incoming carry acts as a generated signal. This is essential for the parallel carry computation.

The module's primary functionality is to enable parallel carry computation for an N-bit binary adder by preparing the propagate and generate signals, which are crucial to reducing the adder's critical path and overall latency.

**Note**: This module assumes that `math_adder_brent_kung_pg` is defined elsewhere and transforms the bit-wise generate and propagate signals from individual bits to a format more suited to parallel computation. The detailed functionality of `math_adder_brent_kung_pg` is not provided, but it must define inputs `i_a`, `i_b` and outputs `ow_p`, `ow_g`.

## Usage Example

When using the `math_adder_brent_kung_bitwisepg` in a project, the module should be instantiated within a parent module, and the inputs provided with the operand vectors. The generated propagate and generate signals can then be utilized in subsequent stages of a Brent-Kung adder to calculate carries quickly.

---

[Return to Index](/docs/mark_down/rtl/)

---
