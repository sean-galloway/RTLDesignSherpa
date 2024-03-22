---
title: Hamming Decode SECDED Module
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

Generic CRC Block

## Module Description

The `dataint_ecc_hamming_decode_secded` module implements a Hamming code decoder with Single Error Correction and Double Error Detection (SECDED) capability. It is designed to identify and correct single-bit errors and detect double-bit errors in a block of data.

## Parameters

- `WIDTH`: Specifies the width of the input data block.
- `DEBUG`: Enables debug mode if set to 1, which provides additional console output for diagnostic purposes.

## Inputs

- `i_clk`: Clock input.
- `i_rst_n`: Active low reset.
- `i_enable`: Enables the module when high.
- `i_hamming_data`: The input data block, including data, parity bits, and an overall parity bit, with a total width of `WIDTH + ParityBits + 1`.

## Outputs

- `o_data`: The corrected data output, with a width of `WIDTH`.
- `o_error_detected`: Asserted high if any single or double-bit error is detected.
- `o_double_error_detected`: Asserted high if a double-bit error is detected.

## Functionality

- At each active clock edge, if the module is enabled and `i_enable` is high:
  - The module calculates parity check values based on the received `i_hamming_data`.
  - It determines if there are any errors based on the computed parity and the received parity bits.
  - For single-bit errors (including errors in the parity bits themselves), the module corrects the error and outputs the corrected data on `o_data`.
  - If a single-bit error is detected and corrected, `o_error_detected` is asserted.
  - If a double-bit error is detected (indicated by a specific syndrome pattern and overall parity check), `o_double_error_detected` and `o_error_detected` are asserted, but no correction is applied as double-bit errors are not correctable.
  - The module outputs the processed data on `o_data`, correcting any single-bit error if detected.
- If `DEBUG` is set to 1, the module provides additional information via console outputs, including detected error positions and syndrome values.

## Local Parameters

- `ParityBits`: The number of parity bits required for the given `WIDTH`, calculated as `$clog2(WIDTH + $clog2(WIDTH) + 1)`.
- `TotalWidth`: The total width of the input data including data, parity bits, and overall parity bit, calculated as `WIDTH + ParityBits + 1`.

## Usage

This module is typically used in communication systems or memory interfaces where data integrity is crucial and where single-bit errors can be corrected and double-bit errors need to be detected for reliable operation.

---

## Related Modules

- [Hamming Encode](dataint_ecc_hamming_encode)
- [Hamming Decode](dataint_ecc_hamming_decode)

---

[Return to Index](/docs/mark_down/rtl/)

---
