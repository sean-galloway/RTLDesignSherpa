---
title: Generic CRC Block
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The Generic CRC Block is a highly configurable module designed for generating Cyclic Redundancy Check (CRC) codes, which are widely used for error detection in digital networks and storage devices. This module supports a variety of CRC algorithms with different widths, polynomials, and configurations, making it suitable for diverse applications.

## Overview

CRC algorithms are used to detect changes to raw data, ensuring the integrity of data during transmission or storage. The Generic CRC Block module leverages parameterization to support various CRC standards, including CRC-8, CRC-16, CRC-32, and others, with customizable parameters for each algorithm.

## Inputs and Outputs

- **i_clk**: Input clock signal.
- **i_rst_n**: Active low reset signal.
- **i_load_crc_start**: Signal to start loading the initial CRC value.
- **i_load_from_cascade**: Signal to load CRC value from cascaded modules.
- **i_cascade_sel**: One-hot encoded selection signal for cascade input.
- **i_data**: Input data bus with a width defined by `DATA_WIDTH`.
- **o_crc**: Output CRC value with a width defined by `CRC_WIDTH`.

## Parameters

- **DATA_WIDTH**: Configurable data width.
- **CHUNKS**: Number of 8-bit blocks in the input data, calculated as `DATA_WIDTH / 8`.
- **CRC_WIDTH**: Width of the CRC polynomial.
- **POLY**: The polynomial used for CRC calculation.
- **POLY_INIT**: Initial value for the CRC calculation.
- **REFIN**: Flag to enable reflection of input data.
- **REFOUT**: Flag to enable reflection of the output CRC.
- **XOROUT**: Final XOR value applied to the computed CRC before output.

## Inner Workings

1. **Initialization**: On reset or when `i_load_crc_start` is asserted, the CRC value is set to `POLY_INIT`.
2. **Input Reflection**: If `REFIN` is enabled, input data bits are reflected before processing.
3. **Cascade Selection**: The module supports cascading, where partial CRC calculations from previous blocks can be selected and continued.
4. **CRC Calculation**: The module computes the CRC in chunks, using the specified polynomial. The calculation includes optional reflection of input data (`REFIN`) and output data (`REFOUT`), and it concludes with an XOR operation with `XOROUT`.
5. **Dynamic Configuration**: Through the use of parameters and input signals, the module supports various CRC algorithms and configurations, allowing it to be tailored to specific requirements.
6. **Output Handling**: The final CRC value is registered and output on the next clock cycle after computation.

This module provides a flexible and efficient solution for implementing CRC in hardware, supporting a wide range of applications from simple data integrity checks to complex communication protocols.

## Tested Configurations

| Algorithm          | CRC_WIDTH | POLY                 | POLY_INIT            | REFIN | REFOUT | XOROUT               |
| ------------------ | --------- | -------------------- | -------------------- | ----- | ------ | -------------------- |
| CRC-8              | 8         | 8'h07                | 8'h00                | 0     | 0      | 8'h00                |
| CRC-8_CDMA2000     | 8         | 8'h9B                | 8'hFF                | 0     | 0      | 8'h00                |
| CRC-8_DARC         | 8         | 8'h39                | 8'h00                | 1     | 1      | 8'h00                |
| CRC-8_DVB-S2       | 8         | 8'hD5                | 8'h00                | 0     | 0      | 8'h00                |
| CRC-8_EBU          | 8         | 8'h1D                | 8'hFF                | 1     | 1      | 8'h00                |
| CRC-8_I-CODE       | 8         | 8'h1D                | 8'hFD                | 0     | 0      | 8'h00                |
| CRC-8_ITU          | 8         | 8'h07                | 8'h00                | 0     | 0      | 8'h55                |
| CRC-8_MAXIM        | 8         | 8'h31                | 8'h00                | 1     | 1      | 8'h00                |
| CRC-8_ROHC         | 8         | 8'h07                | 8'hFF                | 1     | 1      | 8'h00                |
| CRC-8_WCDMA        | 8         | 8'h9B                | 8'h00                | 1     | 1      | 8'h00                |
| CRC-16_ARC         | 16        | 16'h8005             | 16'h0000             | 1     | 1      | 16'h0000             |
| CRC-16_AUG-CCITT   | 16        | 16'h1021             | 16'h1D0F             | 0     | 0      | 16'h0000             |
| CRC-16_BUYPASS     | 16        | 16'h8005             | 16'h0000             | 0     | 0      | 16'h0000             |
| CRC-16_CCITT-FALSE | 16        | 16'h1021             | 16'hFFFF             | 0     | 0      | 16'h0000             |
| CRC-16_CDMA2000    | 16        | 16'hC867             | 16'hFFFF             | 0     | 0      | 16'h0000             |
| CRC-16_DDS-110     | 16        | 16'h8005             | 16'h800D             | 0     | 0      | 16'h0000             |
| CRC-16_DECT-R      | 16        | 16'h0589             | 16'h0000             | 0     | 0      | 16'h0001             |
| CRC-16_DECT-X      | 16        | 16'h0589             | 16'h0000             | 0     | 0      | 16'h0000             |
| CRC-16_DNP         | 16        | 16'h3D65             | 16'h0000             | 1     | 1      | 16'hFFFF             |
| CRC-16_EN-13757    | 16        | 16'h3D65             | 16'h0000             | 0     | 0      | 16'hFFFF             |
| CRC-16_GENIBUS     | 16        | 16'h1021             | 16'hFFFF             | 0     | 0      | 16'hFFFF             |
| CRC-16_KERMIT      | 16        | 16'h1021             | 16'h0000             | 1     | 1      | 16'h0000             |
| CRC-16_MAXIM       | 16        | 16'h8005             | 16'h0000             | 1     | 1      | 16'hFFFF             |
| CRC-16_MCRF4XX     | 16        | 16'h1021             | 16'hFFFF             | 1     | 1      | 16'h0000             |
| CRC-16_MODBUS      | 16        | 16'h8005             | 16'hFFFF             | 1     | 1      | 16'h0000             |
| CRC-16_RIELLO      | 16        | 16'h1021             | 16'hB2AA             | 1     | 1      | 16'h0000             |
| CRC-16_T10-DIF     | 16        | 16'h8BB7             | 16'h0000             | 0     | 0      | 16'h0000             |
| CRC-16_TELEDISK    | 16        | 16'hA097             | 16'h0000             | 0     | 0      | 16'h0000             |
| CRC-16_TMS37157    | 16        | 16'h1021             | 16'h89EC             | 1     | 1      | 16'h0000             |
| CRC-16_USB         | 16        | 16'h8005             | 16'hFFFF             | 1     | 1      | 16'hFFFF             |
| CRC-16_X-25        | 16        | 16'h1021             | 16'hFFFF             | 1     | 1      | 16'hFFFF             |
| CRC-16_XMODEM      | 16        | 16'h1021             | 16'h0000             | 0     | 0      | 16'h0000             |
| CRC-16             | 16        | 16'h1021             | 16'hC6C6             | 1     | 1      | 16'h0000             |
| CRC-32             | 32        | 32'h04C11DB7         | 32'hFFFFFFFF         | 1     | 1      | 32'hFFFFFFFF         |
| CRC-32_BZIP2       | 32        | 32'h04C11DB7         | 32'hFFFFFFFF         | 0     | 0      | 32'hFFFFFFFF         |
| CRC-32_JAMCRC      | 32        | 32'h04C11DB7         | 32'hFFFFFFFF         | 1     | 1      | 32'h00000000         |
| CRC-32_MPEG-2      | 32        | 32'h04C11DB7         | 32'hFFFFFFFF         | 0     | 0      | 32'h00000000         |
| CRC-32_POSIX       | 32        | 32'h04C11DB7         | 32'h00000000         | 0     | 0      | 32'hFFFFFFFF         |
| CRC-32_SATA        | 32        | 32'h04C11DB7         | 32'h52325032         | 0     | 0      | 32'h00000000         |
| CRC-32_XFER        | 32        | 32'h000000AF         | 32'h00000000         | 0     | 0      | 32'h00000000         |
| CRC-32C            | 32        | 32'h1EDC6F41         | 32'hFFFFFFFF         | 1     | 1      | 32'hFFFFFFFF         |
| CRC-32D            | 32        | 32'hA833982B         | 32'hFFFFFFFF         | 1     | 1      | 32'hFFFFFFFF         |
| CRC-32Q            | 32        | 32'h814141AB         | 32'h00000000         | 0     | 0      | 32'h00000000         |
| CRC-40_GSM         | 40        | 40'h4820009          | 40'h000000000        | 0     | 0      | 40'hFFFFFFFFFF       |
| CRC-64_ECMA-182    | 64        | 64'h42F0E1EBA9EA3693 | 64'h00000000000000   | 0     | 0      | 64'h00000000         |
| CRC-64_GO-ISO      | 64        | 64'h000000000000001B | 64'hFFFFFFFFFFFFFFFF | 1     | 1      | 64'hFFFFFFFFFFFFFFFF |
| CRC-64_MS          | 64        | 64'h259C84CBA6426349 | 64'hFFFFFFFFFFFFFFFF | 1     | 1      | 64'h00000000000000   |
| CRC-64_REDIS       | 64        | 64'hAD93D23594C935A9 | 64'h00000000000000   | 1     | 1      | 64'h00000000000000   |
| CRC-64_WE          | 64        | 64'h42F0E1EBA9EA3693 | 64'hFFFFFFFFFFFFFFFF | 0     | 0      | 64'hFFFFFFFFFFFFFFFF |
| CRC-64_XZ          | 64        | 64'h42F0E1EBA9EA3693 | 64'hFFFFFFFFFFFFFFFF | 1     | 1      | 64'hFFFFFFFFFFFFFFFF |

---

## Block Hierarchy and Links

- [CRC](fifo_async_div2)
- [XOR shift cascade](dataint_crc_xor_shift_cascade)
- [XOR Shift](dataint_crc_xor_shift)

---

[Return to Index](/docs/mark_down/rtl/)

---
