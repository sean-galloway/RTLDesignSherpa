---
title: CRC XOR Shift Module
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The CRC XOR Shift Module is a critical component in the hardware implementation of Cyclic Redundancy Check (CRC) algorithms. It performs CRC calculations on a single bit, applying XOR and shift operations based on a given CRC polynomial. This module is designed to process data bit-by-bit, making it an essential part of a CRC calculation pipeline.

## Overview

The module takes a bit of input data along with the current state of the CRC calculation and the CRC polynomial. It computes the next state of the CRC by applying XOR operations between the input bit, the most significant bit (MSB) of the current CRC state, and parts of the CRC polynomial, depending on the input bit's value.

## Inputs and Outputs

- **i_stage_input**: Current state of the CRC calculation, width defined by `CRC_WIDTH`.
- **i_poly**: The CRC polynomial, width defined by `CRC_WIDTH`.
- **i_new_bit**: The new input bit to be processed.
- **ow_stage_output**: The updated CRC state after processing the input bit, width defined by `CRC_WIDTH`.

## Parameters

- **CRC_WIDTH**: The width of the CRC polynomial and the CRC calculation, allowing this module to be adapted to various CRC standards by adjusting this parameter.

## Inner Workings

1. **Feedback Bit Calculation**: The module calculates the feedback bit by performing an XOR operation between the input bit and the MSB of the current CRC state.
2. **Shift and Conditional XOR**: The CRC state is shifted left by one bit, and a conditional XOR operation is applied. The conditional XOR operation involves the newly calculated feedback bit and the CRC polynomial, where the polynomial is applied only if the feedback bit is 1.
3. **Output Generation**: The result of these operations forms the new CRC state, which is output from the module.

## Usage

This module is utilized in CRC calculation processes where data needs to be processed bit by bit. It is especially useful in serial data transmission systems or any application requiring bit-level CRC calculations. By chaining multiple instances of this module or integrating it within a loop structure, a complete CRC calculation for arbitrary data lengths can be performed.

## Example Application

In a scenario requiring CRC checks for serial data transmission, this module can be instantiated to process each bit as it is received. By continuously updating the CRC calculation with each new bit and comparing the final CRC value against a known good CRC, the integrity of the transmitted data can be verified.

## Conclusion

The CRC XOR Shift Module provides a flexible and efficient means of performing CRC calculations at the bit level. Its parameterized design allows it to be adapted to various CRC standards, making it a valuable tool for hardware implementations of CRC algorithms.

---

## Block Hierarchy and Links

- [CRC](fifo_async_div2)
- [XOR shift cascade](dataint_crc_xor_shift_cascade)
- [XOR Shift](dataint_crc_xor_shift)

---

[Return to Index](/docs/mark_down/rtl/)

---
