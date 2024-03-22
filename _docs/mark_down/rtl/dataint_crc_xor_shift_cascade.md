---
title: CRC XOR Shift Cascade Module
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The CRC XOR Shift Cascade Module performs bit-wise operations on 8 bits of data, specifically designed to support the computation of Cyclic Redundancy Check (CRC) through cascaded XOR and shift operations. This module is a fundamental building block in CRC calculations, especially in hardware implementations that require efficient and modular designs.

## Overview

This module takes an initial CRC block input and a single byte of data, applying a series of XOR and shift operations defined by the CRC polynomial. It outputs the result of these operations, which can then be used as input for subsequent stages in a CRC calculation pipeline.

## Inputs and Outputs

- **i_block_input**: The initial input for the CRC calculation of width `CRC_WIDTH`.
- **i_poly**: The CRC polynomial of width `CRC_WIDTH`.
- **i_data_input**: The 8-bit data input for the current stage.
- **ow_block_output**: The output of the CRC calculation after processing the 8-bit data input, of width `CRC_WIDTH`.

## Parameters

- **CRC_WIDTH**: The width of the CRC calculation, allows for different CRC standards to be implemented by adjusting this parameter.

## Inner Workings

1. **Initialization**: The module initializes with parameters defining the width of the CRC calculation.
2. **Cascaded XOR-Shift Operations**: The module performs a series of XOR and shift operations across each bit of the 8-bit data input. Each bit influences the CRC calculation through a specific operation that combines the current stage's input, the CRC polynomial, and the bit value.
3. **Chaining Operations**: The operations are cascaded, where the output of one operation becomes the input for the next, iterating through all 8 bits of the data input.
4. **Output Generation**: The final output after processing all 8 bits is provided as `ow_block_output`, representing the CRC value after incorporating the current byte of data.

## Usage

This module is intended for use in larger CRC calculation systems where multiple bytes of data are processed in sequence. It enables the modular construction of CRC computation pipelines, where each byte of data can be processed independently and efficiently, leveraging hardware parallelism.

## Example Application

In a CRC calculation for a data packet, this module could be instantiated multiple times, each time processing a byte of the packet and passing the result to the next stage. This approach allows for flexible and efficient hardware implementations of CRC algorithms, accommodating various data widths and CRC standards.

---

## Block Hierarchy and Links

- [CRC](fifo_async_div2)
- [XOR shift cascade](dataint_crc_xor_shift_cascade)
- [XOR Shift](dataint_crc_xor_shift)

---

[Return to Index](/docs/mark_down/rtl/)

---
