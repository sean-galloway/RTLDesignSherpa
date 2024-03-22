---
title: Generic Parity Generator Module
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

Hamming Encode SECDED Module

This module, `dataint_parity`, is designed to generate or check parity for data divided into chunks. It is highly configurable, allowing for varying data widths and chunk sizes.

## Overview

The `dataint_parity` module calculates parity for each chunk of input data (`i_data`) based on the specified parity type (`i_parity_type`). It supports both even and odd parity types. The module can also compare the generated parity against input parity bits (`i_parity`) for error checking, outputting any detected errors in `ow_error`.

## Parameters

- **CHUNKS**: The number of chunks the input data is divided into for parity checking or generation.
- **WIDTH**: The total width of the input data.

## Ports

- **i_data**: Input data for which parity is generated or checked.
- **i_parity**: Input parity for each chunk, used when checking parity.
- **i_parity_type**: Specifies the type of parity (1 for even, 0 for odd).
- **ow_parity**: Output parity calculated for each chunk.
- **ow_error**: Output flags for each chunk indicating a parity error (valid only when checking parity).

## Functionality

- The data width is dynamically divided into the specified number of chunks.
- For each chunk, the module calculates the parity based on the `i_parity_type`.
- If used for parity checking, the module compares the calculated parity against `i_parity` and flags any discrepancies in `ow_error`.

## Implementation Details

- **Chunk Size Calculation**: The module computes the size of each chunk based on the total data width and the number of chunks.
- **Parity Calculation**: For each chunk, parity is calculated either as even or odd, dictated by `i_parity_type`.
- **Error Detection**: When checking parity, discrepancies between calculated and input parity bits are flagged in `ow_error`.

---

[Return to Index](/docs/mark_down/rtl/)

---
