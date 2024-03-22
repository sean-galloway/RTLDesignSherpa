---
title: Math Adder Full
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `math_adder_full` module is a simple digital full adder implemented in Verilog. A full adder is a combinatorial circuit that adds three binary digits, producing a sum and a carry-out. It is typically used in arithmetic logic units (ALUs) and digital adders for computing binary addition.

## Inputs

- `i_a` (1-bit): First input operand bit.

- `i_b` (1-bit): Second input operand bit.

- `i_c` (1-bit): Input carry bit from the previous less significant stage.

## Outputs

- `ow_sum` (1-bit): Output sum bit.

- `ow_carry` (1-bit): Output carry bit for the next more significant stage.

## Functionality

- The `ow_sum` output is calculated by performing an XOR operation on all three inputs. In binary addition, the sum bit results from XORing the input bits.

- The `ow_carry` output is calculated by an OR operation between the AND of inputs `i_a` and `i_b`, and the AND of input `i_c` with the XOR of `i_a` and `i_b`. This logic determines if there is a carry-out based on the input conditions.

## Usage

This module can be instantiated within a larger design to perform binary addition of single-bit operands. No specific command line options are necessary for this module, as it is a hardware description for synthesis and not a software program.

This full adder can be used as a building block in constructing multi-bit adders like ripple-carry adders or more sophisticated adders like look-ahead adders by chaining multiple instances and providing the carry-out of one as the carry-in to the next.

## Simulation and Synthesis

The `timescale` directive is set to 1 nanosecond for the time unit and one picosecond for the precision. This means that the simulation time steps should be in increments of nanoseconds, and the simulator will allow for timing details to the level of picoseconds.

---

[Return to Index](/docs/mark_down/rtl/)

---
