# axi_skid_buffer

The `axi_skid_buffer` module is designed for use with AXI (Advanced eXtensible Interface) protocols. It implements a "skid buffer," which is a form of FIFO (First-In-First-Out) that handles data buffering between interfaces with possible differences in processing and data transfer speeds.

## Parameters

- `DATA_WIDTH` (integer, default: 32): The bit width of the data.
- `SKID_DEPTH` (integer, default: 2): The depth of the skid buffer, which represents the number of data entries the buffer can hold. The depth must be set at {2, 4, 6, 8}.
- `DW` (integer, default: equal to DATA_WIDTH): A convenience parameter set equal to DATA_WIDTH.
- `BUF_WIDTH` (integer, default: DATA_WIDTH * SKID_DEPTH): The bit width of the buffer which accumulates all the data.
- `BW` (integer, default: equal to BUF_WIDTH): Another convenience parameter set equal to BUF_WIDTH.

## Inputs/Outputs

- `i_axi_aclk` (input logic): The global clock signal input.
- `i_axi_aresetn` (input logic): Active low asynchronous reset signal.
- `i_wr_valid` (input logic): Input write valid signal indicating the data is valid and ready for writing.
- `o_wr_ready` (output logic): Output signal that informs the writer that the buffer is ready to accept data.
- `i_wr_data` (input logic [DW-1:0]): Parallel data input to be written into the buffer.
- `ow_count` (output logic [3:0]): Output signal indicating the count of the data in the buffer (from read perspective, since it's the same as the write count here).
- `o_rd_valid` (output logic): Output read valid signal indicating that there is data available to be read.
- `i_rd_ready` (input logic): Input ready signal indicating the downstream consumer is ready to accept data.
- `o_rd_count` (output logic [3:0]): Output read count signal representing the number of entries currently held in the buffer.
- `o_jrd_data` (output logic [DW-1:0]): Output data from the buffer for reading.

## Internal Functionality

- `r_data` (logic [BW-1:0]): Internal register for storing the buffer data.
- `r_data_count` (logic [3:0]): Internal counter for the number of data entries in the buffer.
- `w_wr_xfer`, `w_rd_xfer` (logic): Internal wires for determining if a write or read transfer should occur.
- `zeros` (logic [DW-1:0]): A constant vector of zeros used for buffer shifting.

## Synchronization Logic

Data transfers are synchronized with the global clock. Conditions to handle the reset state, data write, data read, and simultaneous read and write scenarios are specified in the `always_ff` blocks.

## Write and Read Handling

The module handles write and read requests according to the current status of the buffer. It allows for regular data transfer and maintains the skid buffer's state correctly, even when both read and write happen simultaneously.

## Output Logic Signals

Signals `o_wr_ready` and `o_rd_valid` are derived from the current data count and transfer status, indicating whether the module can accept new data or has data ready to read.

---

The `axi_skid_buffer` is typically used in AXI-based systems to ensure smooth data transfer between master and slave components that may operate at different speeds or have different processing power. Ensure that the parameters 'SKID_DEPTH' and buffer sizes are set according to the requirement of the system where this module is to be deployed. This module relies on standard SystemVerilog constructs and should be synthesized and integrated with proper AXI-compliant interfaces.

---

[Return to Index](index.md)

---
