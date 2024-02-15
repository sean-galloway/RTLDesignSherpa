# fifo_async

The `fifo_async` module implements a parameterized asynchronous FIFO (First-In, First-Out) buffer with the power of two depths. This means that the depth (`DEPTH`) should be chosen as a power of two for proper operation. The FIFO can handle different clock domains for read and write operations. It is suitable for cases where data is produced and consumed at different rates or on different clock domains.

## Module Parameters

- `DATA_WIDTH`: (int) Width of the data bus.

- `DEPTH`: (int) Depth of the FIFO must be a power of two.

- `N_FLOP_CROSS`: (int) Number of flops for domain crossing, typically two for better metastability handling, although one may see three or four being used.

- `ALMOST_WR_MARGIN`: (int) Margin for the almost full threshold.

- `ALMOST_RD_MARGIN`: (int) Margin for the almost empty threshold.

- `INSTANCE_NAME`: (string) An identifier for the FIFO instance, useful for debugging purposes.

## Ports

### Clocks and Resets

- `i_wr_clk`: (input, logic) Write clock signal.

- `i_wr_rst_n`: (input, logic) Active-low reset signal for write domain.

- `i_rd_clk`: (input, logic) Read clock signal.

- `i_rd_rst_n`: (input, logic) Active-low reset signal for read domain.

### Write Domain

- `i_write`: (input, logic) Write enable signal.

- `i_wr_data`: (input, logic) Data input for the write operation.

- `ow_wr_full`: (output, logic) Indicates when the FIFO is full.

- `ow_wr_almost_full`: (output, logic) Indicates when the FIFO is almost full.

### Read Domain

- `i_read`: (input, logic) Read enable signal.

- `ow_rd_data`: (output, logic) Data output for the read operation.

- `ow_rd_empty`: (output, logic) Indicates when the FIFO is empty.

- `ow_rd_almost_empty`: (output, logic) Indicates when the FIFO is almost empty.

## Internal Functionality

- Counts for read and write pointers are maintained in binary and gray codes to avoid glitches during conversions in different clock domains.

- The FIFO memory is implemented using an unpacked array of logic vectors.

- Uses clock domain crossing modules to transfer pointer values between write and read domains safely.

- Generates full and empty signals based on the converted read and write pointers.

- Implements almost full and empty logic that uses a margin to indicate these states before the FIFO is full or empty.

- Error checking in simulation to alert when write operations are attempted on a full FIFO or read operations on an empty FIFO.

- The initial block for dumping waveforms during simulation for debugging purposes.

## Simulation Notes

- The module includes test code disabled during synthesis (`synopsys translate_off` / `synopsys translate_on`). This includes error displays and VCD dumping, which can only be used to debug the FIFO's behavior in a simulated environment.

### Usage Considerations

- The `fifo_async` module must operate in a system with proper reset synchronization to ensure safe and reliable reset of both write and read domains.

- Write and read operations should respect the full and empty status of the FIFO to avoid data corruption or undefined behavior.

## Example Instantiation

```verilog

fifo_async #(

.DATA_WIDTH(32),

.DEPTH(64),

.N_FLOP_CROSS(2),

.ALMOST_WR_MARGIN(2),

.ALMOST_RD_MARGIN(2),

.INSTANCE_NAME("FIFO_INSTANCE")

) fifo_instance (

.i_wr_clk(wr_clk),

.i_wr_rst_n(wr_rst_n),

.i_rd_clk(rd_clk),

.i_rd_rst_n(rd_rst_n),

.i_write(write_en),

.i_wr_data(data_in),

.ow_wr_full(fifo_full),

.ow_wr_almost_full(fifo_almost_full),

.i_read(read_en),

.ow_rd_data(data_out),

.ow_rd_empty(fifo_empty),

.ow_rd_almost_empty(fifo_almost_empty)

);

```

This instantiation example shows how to create an instance of the `fifo_async` with a 32-bit wide data bus and a depth of 64 elements. The parameters and signals should be adjusted according to the specific design requirements.

---

[Return to Index](index.md)

----------
