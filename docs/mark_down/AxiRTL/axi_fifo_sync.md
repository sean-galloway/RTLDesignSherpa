# axi_fifo_sync

## Operation

This is a parameterized synchronous FIFO module designed for AXI interfaces. It is suitable only for inteernal operations as the outputs come off of a mux; AXI protocol requires interface signals to all come off of a flop; the skid buffer should be used for these cases.

## Overview

The `axi_fifo_sync` module is a synchronous FIFO suited for AXI interface protocols. It is capable of buffering data entries and managing the flow control between writer and reader interfaces.

## Parameters

- `DEL` (int): Additional logic delay (unused in provided code)
- `DATA_WIDTH` (int): Number of bits in a single data entry
- `DEPTH` (int): Maximum number of data entries the FIFO can hold
- `ALMOST_WR_MARGIN` (int): Margin level for the almost-full status signal
- `ALMOST_RD_MARGIN` (int): Margin level for the almost-empty status signal
- `INSTANCE_NAME` (string): Identifier for this FIFO instance; used in debug messages
- `DW` (int): Same as `DATA_WIDTH` (potentially redundant)
- `D` (int): Same as `DEPTH` (potentially redundant)
- `AW` (int): Address width, which is the number of bits needed to address FIFO entries

## Ports

- `i_axi_aclk`: Input clock signal
- `i_axi_aresetn`: Active-low reset signal
- `i_wr_valid`: Write enable signal (indicates if write data is valid)
- `o_wr_ready`: Output signal indicating FIFO is not full and can accept data
- `i_wr_data` [DW-1:0]: Input data to be written to the FIFO
- `i_rd_ready`: Input signal indicating the downstream component is ready to accept data
- `ow_count` [AW-1:0]: Output FIFO fill level count
- `o_rd_valid`: Output signal indicating FIFO is not empty and has data to be read
- `ow_rd_data` [DW-1:0]: Data to be read from the FIFO (output stage)
- `o_rd_data` [DW-1:0]: Data output from the FIFO (output stage)

---

[Return to Index](index.md)

---
