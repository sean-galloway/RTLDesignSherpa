# fifo_control

## Overview

This document provides a summary of the `fifo_control` module implemented in SystemVerilog. The module is designed to manage the control signals for a parameterized asynchronous FIFO (First-In-First-Out) buffer. This module handles depth adjustments, full and almost full conditions for writing and empty and almost empty conditions for reading.

## Functionality

The `fifo_control` module performs several key operations to manage the status of the FIFO buffer:

1. **Full Signal Generation**: Determines when the FIFO buffer is full based on write pointers.
2. **Almost Full Signal Generation**: Indicates when the FIFO buffer is nearing full capacity.
3. **Empty Signal Generation**: Detects when the FIFO buffer is empty based on read pointers.
4. **Almost Empty Signal Generation**: Indicates when the FIFO buffer is close to empty.
5. **Count Signal Generation**: Provides a count of the items currently stored in the FIFO.

## Parameters

The module is parameterized to allow customization of various aspects:

- `DEL`: Delay for signal assignments.
- `ADDR_WIDTH`: Width of the address pointers.
- `DEPTH`: Depth of the FIFO, which must be a power of two.
- `ALMOST_WR_MARGIN`: Margin for the almost full condition.
- `ALMOST_RD_MARGIN`: Margin for the almost empty condition.
- `INSTANCE_NAME`: A custom name for the instance.

## Ports

### Input Ports

- **Clocks and Resets**
  - `i_wr_clk`: Write clock.
  - `i_wr_rst_n`: Write reset (active low).
  - `i_rd_clk`: Read clock.
  - `i_rd_rst_n`: Read reset (active low).

- **Pointers**
  - `iw_wr_ptr_bin`: Binary write pointer.
  - `iw_wdom_rd_ptr_bin`: Write domain read pointer (binary).
  - `iw_rd_ptr_bin`: Binary read pointer.
  - `iw_rdom_wr_ptr_bin`: Read domain write pointer (binary).

### Output Ports

- **Status**
  - `ow_count`: Current count of items in the FIFO.
  - `o_wr_full`: Full status for the write operations.
  - `o_wr_almost_full`: Almost full status for the write operations.
  - `o_rd_empty`: Empty status for the read operations.
  - `o_rd_almost_empty`: Almost empty status for the read operations.

## Internal Logic

### Full and Almost Full Signal Generation

- **XOR Pointers**: The upper bits of the read and write pointers are XORed to assist in the full/empty conditions.
- **Full Detection**: A full condition is detected when the most significant XORed bits and the lower address bits of the write and read pointers match.
- **Almost Full Calculation**: The difference in the pointers determines if the FIFO is almost full.

### Empty and Almost Empty Signal Generation

- **Empty Detection**: An empty condition is detected when the XORed most significant bits are zero and the lower address bits match.
- **Almost Empty Calculation**: The difference in the pointers determines if the FIFO is almost empty.
- **Count Calculation**: Determines the current number of items in the FIFO.

### Sequential Logic

- **Write Clock Domain**: Updates `o_wr_full` and `o_wr_almost_full` at the positive edge of the write clock or a negative edge of the write reset.
- **Read Clock Domain**: Updates `o_rd_empty` and `o_rd_almost_empty` at the positive edge of the read clock or a negative edge of the read reset.

---

## Block Hierarchy and Links

- [Fifo sync](fifo_sync.md)
- [Fifo async](fifo_async.md)
- [Fifo async div by 2](fifo_async_div2.md)

---

[Return to Index](index.md)

---
