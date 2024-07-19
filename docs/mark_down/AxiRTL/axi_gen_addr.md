# axi_gen_addr

## Overview

The Verilog module `axi_gen_addr` is designed to generate the next address for AXI transactions based on inputs such as the current address, size, burst type, and length. It works with AXI bus interfaces and accommodates address generation for fixed, incrementing, and wrapping burst types. It also handles cases where there might be a data width mismatch between input and output data paths.

## Inputs and Outputs

- **i_curr_addr[AW-1:0]**: (Input) Current AXI bus address.
- **i_size[2:0]**: (Input) Size of the transfer; it determines how much the address will be incremented.
- **i_burst[1:0]**: (Input) Burst type; it can be fixed (00), incrementing (01), or wrapping (10).
- **i_len[LEN-1:0]**: (Input) The number of data beats in an AXI burst.
- **ow_next_addr[AW-1:0]**: (Output) The next address after the current address, derived based on burst type and size.
- **ow_next_addr_align[AW-1:0]**: (Output) Next address aligned to the output data width (ODW).

## Parameters

- **AW** (int): Address width.
- **DW** (int): Data width for the input data path.
- **ODW** (int): Data width for the output data path.
- **LEN** (int): Supporting maximum burst length of 2^LEN beats.

## Internal Functionality

- Handles different burst types: Fixed, Incrementing, and Wrapping.
- Supports alignment requirements as per AXI protocol.
- Generates address increment value based on input size.
- Adjusts the increment if there’s a mismatch between input and output data width.
- Calculates wrap mask and aligned address for wrapping burst.
- Aligns the next address to the boundary defined by the output data width.

## Code Explanation

- **ODWBYTES**: Defined as `ODW / 8`, representing the number of bytes for the output data path width.
- **increment** and **increment_pre**: Used for calculating the amount by which the current address should be incremented.
- **wrap_mask**: Used in wrapping burst type calculations to ensure address wraps around a specified boundary.
(QQQ)
- **aligned_addr**: Used to generate an aligned address based on the increment value.
- **wrap_addr**: Represents the next address for wrapping burst type, calculated using the wrap mask.

The module employs two `always_comb` blocks to calculate the increment value and the next address, respectively. It also includes an `assign` statement for the aligned next address output (`ow_next_addr_align`).

## Usage

To use this module:

1. Instantiate `axi_gen_addr` within your design.
2. Configure the address width (`AW`), data width (`DW`), output data width (`ODW`), and burst length (`LEN`) parameters, if the defaults are not suitable.
3. Connect the inputs (`i_curr_addr`, `i_size`, `i_burst`, `i_len`) with the appropriate signals in your design.
4. Utilize the outputs (`ow_next_addr`, `ow_next_addr_align`) for subsequent AXI transactions.

**Note**: This code assumes a knowledge of AXI4 bus protocol. Users of this module should understand the implications of AXI addressing and burst transactions.

---

[Return to Index](index.md)

---
