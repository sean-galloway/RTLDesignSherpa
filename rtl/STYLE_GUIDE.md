# Style Guide

These rules are short and straightforward to keep them easy to be adhered to Note: some naming convention documents are 30+ pages long. For this forum, I want to keep it simple. You can follow (or not) if you like. Be aware of some of the tools I have developed from the naming convention.

- Module names are snake case
- Signal names a snake case
- Parameter names are all caps
- Input ports all begin with i_ or iw_. It is assumed all inputs come directly from flops. In the rare cases where that does not occur, the iw_ signifier is used (w meaning wire.)
- Output ports all begin with o_ or ow_. It is assumed all outputs come directly from flops. In the rare cases where that does not occur, the ow_ signifier is used (w meaning wire.)
- All register signals (flops) start with r_.
- All wire signals start with w_.
Note: I was not going to have a strict naming convention. I started exploring automation to create wavedrom diagrams from the existing vcd and gktw files. I want to put a phase of 0.2 on flopped signals (representing tCO), and 0.8 on wire signals to show artificially significant propagation delays. Without the naming convention, none of this can be automated by someone working on a side project like this.

Here is an example port list:

```verilog

module fifo_async #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 16,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0"  // verilog_lint: waive explicit-parameter-storage-type
) (
    // clocks and resets
    input  logic                  i_wr_clk,
    i_wr_rst_n,
    i_rd_clk,
    i_rd_rst_n,
    // i_wr_clk domain
    input  logic                  i_write,
    input  logic [DATA_WIDTH-1:0] i_wr_data,
    output logic                  ow_wr_full,
    output logic                  ow_wr_almost_full,
    // i_rd_clk domain
    input  logic                  i_read,
    output logic [DATA_WIDTH-1:0] ow_rd_data,
    output logic                  ow_rd_empty,
    output logic                  ow_rd_almost_empty
);
```

This example illustrates the bulk of the port-level naming conventions described above.
Below is an example that illustrates a mix of wired and registers being declared. Note: they all use the logic type, then the "r_" and "w_" are helpful in knowing how the signal is used:

```verilog
    /////////////////////////////////////////////////////////////////////////
    // local logics
    logic [AW-1:0] r_wr_addr, r_rd_addr;

    logic [AW:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin,  w_wdom_rd_ptr_bin,  r_rd_ptr_bin,  w_rdom_wr_ptr_bin;
```
