# axi_fifo_async

## Operation

This is a standard FIFO that uses the axi ready/valid protocol. Since it is a FIFO it should only be used internally as there are muxes on the outputs. AXI protocol requires interface signals to all come off of a flop; the skid buffer should be used for these cases. Note: the port list of the skid buffer is nearly identicle to the FIFO.

### Parameters

- `DEL` (Default: 1): An optional delay parameter for FIFO control.
- `DATA_WIDTH` (Default: 8): The specified width, in bits, of the data to be stored in the FIFO.
- `DEPTH` (Default: 10): The number of entries in the FIFO storage; it must be set to an even number.
- `N_FLOP_CROSS` (Default: 2): Determines the number of flip-flop stages to safely cross clock domains.
- `ALMOST_WR_MARGIN` (Default: 1): Number of free spaces left in the FIFO when `almost_full` is asserted.
- `ALMOST_RD_MARGIN` (Default: 1): Number of items in the FIFO when `almost_empty` is asserted.
- `INSTANCE_NAME`: A string parameter typically used for debug purposes to identify the FIFO instance.
- `DW`, `D`, `AW`, `JCW`, `N`: Derived parameters for internal calculations, mainly redundant for end-user customization.

### Ports

- `i_axi_wr_aclk`: The clock signal for the write (ingress) side of the FIFO.
- `i_axi_wr_aresetn`: The active low asynchronous reset for the write domain.
- `i_axi_rd_aclk`: The clock signal for the read (egress) side of the FIFO.
- `i_axi_rd_aresetn`: The active low asynchronous reset for the read domain.
- `i_wr_valid`: Input indicating that valid write data is available.
- `o_wr_ready`: Output indicating that the FIFO can accept new data (i.e., it is not full).
- `i_wr_data`: The actual data to be written into the FIFO.
- `i_rd_ready`: Input indicating that the read side is ready to accept data.
- `o_rd_parametric`: Output indicating that valid data is available for reading.
- `ow_rd_data`, `o_rd_data`: Data outputs for read operations.

### Internal Functionality

The FIFO uses binary counters for the write and read pointers, which are then translated into Gray counters to mitigate issues while crossing clock domains. These counters are essential to managing the FIFO's read and write operations, preventing data corruption and timing issues.

### Error Checking and Debugging

At the end of the module, there is code wrapped in `synopsys translate_off` and `synopsys translate_on` pragmas, which is intended for simulation purposes only and helps to notify the user upon erroneous write (when FIFO is full) and read (when FIFO is empty) attempts.

This code is a typical implementation for an asynchronous FIFO that is used within a larger digital system, potentially as a buffer between two components operating at different frequencies or to manage data flow between different clock domains, ensuring data integrity in the presence of such asynchronous operations.

---

[Return to Index](index.md)

---
