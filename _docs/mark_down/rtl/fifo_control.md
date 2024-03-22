---
title: FIFO Control Block Description
layout: docs
date: 2024-01-02
categories: ["Adders and Subtractors", "simple"]
---

The `fifo_control` module implements the control logic for a parameterized synchronous or asynchronous FIFO (First-In, First-Out) queue. It is designed to operate with any FIFO depth. The control block manages full and empty flags, as well as almost full and almost empty conditions, facilitating robust data handling and flow control between independent read and write domains.

## Parameters

- `DEL` (Default: 1): Delay for internal signals, useful for timing adjustments.
- `ADDR_WIDTH` (Default: 3): The width of the address bus, determining the FIFO's depth as `2^ADDR_WIDTH`.
- `DEPTH` (Default: 16): The total number of entries in the FIFO.
- `ALMOST_WR_MARGIN` (Default: 1): Margin entries before the FIFO signals "almost full".
- `ALMOST_RD_MARGIN` (Default: 1): Margin entries before the FIFO signals "almost empty".
- `INSTANCE_NAME` (Default: "DEADF1F0"): Optional parameter for instance identification, not directly used in the logic.

## Ports

- Clocks and Resets:
  - `i_wr_clk`: Write domain clock.
  - `i_wr_rst_n`: Active low reset for the write domain.
  - `i_rd_clk`: Read domain clock.
  - `i_rd_rst_n`: Active low reset for the read domain.
- Pointers:
  - `iw_wr_ptr_bin`: Binary write pointer from the write domain.
  - `iw_wdom_rd_ptr_bin`: Binary read pointer as seen from the write domain.
  - `iw_rd_ptr_bin`: Binary read pointer from the read domain.
  - `iw_rdom_wr_ptr_bin`: Binary write pointer as seen from the read domain.
- Status Flags:
  - `o_wr_full`: Indicates the FIFO is full.
  - `o_wr_almost_full`: Indicates the FIFO is almost full.
  - `o_rd_empty`: Indicates the FIFO is empty.
  - `o_rd_almost_empty`: Indicates the FIFO is almost empty.

### Internal Functionality

1. **Pointer XOR Logic**: Utilizes the MSB of the binary pointers to generate XOR results for full and empty detection logic.
2. **Full and Almost Full Detection**:
   - Full condition is detected when the write domain's pointer MSB XOR with the read domain's pointer MSB (as seen from the write domain) is true, and their lower bits match.
   - Almost full condition is calculated based on the difference between the write and read pointers, taking into account the FIFO depth and the specified almost full margin.
3. **Empty and Almost Empty Detection**:
   - an empty condition is detected when the read domain's pointer MSB XOR with the write domain's pointer MSB (as seen from the read domain) is false, and their lower bits match.
   - almost empty condition is calculated similarly to almost full, using the almost empty margin.

### Usage

This module is intended for use in systems where asynchronous read and write operations need to be managed for data integrity and flow control. It is especially useful in applications requiring buffer management between different clock domains or data processing stages.

---

## Block Hierarchy and Links

- [Fifo sync](fifo_sync)
- [Fifo async](fifo_async)
- [Fifo async div by 2](fifo_async_div2)

---

[Return to Index](/docs/mark_down/rtl/)

---
