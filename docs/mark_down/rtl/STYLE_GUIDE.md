# Style Guide

The first thing I want to mention is the naming convention. These files are all named very artificially. I did this so that I could find groups of similar functions easier. These rules are short and straightforward to keep them easy to be adhered to Note: some naming convention documents are 30+ pages long. For this forum, I want to keep it simple. You can follow (or not) if you like. Be aware of some of the tools I have developed from the naming convention.

## The Naming Conventions

- Module names are snake case
- Signal names a snake case
- Parameter names are all caps
- Input ports all begin with i_or iw_. It is assumed all inputs come directly from flops. In the rare cases where that does not occur, the iw_ signifier is used (w meaning wire.)
- Output ports all begin with o or ow_. It is assumed all outputs come directly from flops. In the rare cases where that does not occur, the ow_ signifier is used (w meaning wire.)
- All register signals (flops) start with r_.
- All wire signals start with w_.
Note: I was not going to have a strict naming convention. I started exploring automation to create wavedrom diagrams from the existing vcd and gktw files. I want to put a phase of 0.2 on flopped signals (representing tCO), and 0.8 on wire signals to show artificially significant propagation delays. Without the naming convention, none of this can be automated by someone working on a side project like this.

---Here is an example fifo using always_ff and always_comb

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

**This example illustrates the bulk of the port-level naming conventions described above.
Below is an example that illustrates a mix of wired and registers being declared. Note: they all use the logic type, then the "r_" and "w_" are helpful in knowing how the signal is used**

```verilog
    /////////////////////////////////////////////////////////////////////////
    // local logics
    logic [AW-1:0] r_wr_addr, r_rd_addr;

    logic [AW:0] r_wr_ptr_gray, r_wdom_rd_ptr_gray, r_rd_ptr_gray, r_rdom_wr_ptr_gray;
    logic [AW:0] r_wr_ptr_bin,  w_wdom_rd_ptr_bin,  r_rd_ptr_bin,  w_rdom_wr_ptr_bin;
```

### Coding Convention, recommended

In this code base, I have eschewed the usage of macros. They only seem to be used in certain groups in certain companies. Macros have been shown, through internal studies that I can't directly cite, to simulate ~10% faster that using always_ff structures. So, there is a strong argument for why they should be used. I'll show two examples of an 8-bit fifo, one with only always_ff and always_comb and one using macros.

// Fifo without Macros:
`timescale 1ns / 1ps

module simple_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 8
) (
    input wire clk,
    input wire rst_n,
    input wire wr_en,            // Write enable
    input wire rd_en,            // Read enable
    input wire [DATA_WIDTH-1:0] wr_data, // Data to write
    output reg [DATA_WIDTH-1:0] rd_data, // Data to read
    output wire fifo_full,
    output wire fifo_empty
);

// Internal variables
reg [DATA_WIDTH-1:0] fifo_mem [DEPTH-1:0]; // FIFO memory array
reg [$clog2(DEPTH):0] wr_ptr = 0;          // Write pointer
reg [$clog2(DEPTH):0] rd_ptr = 0;          // Read pointer
reg [$clog2(DEPTH)+1:0] count = 0;         // Count of items in FIFO

// Write operation
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wr_ptr <= 0;
    end else if (wr_en && !fifo_full) begin
        fifo_mem[wr_ptr[DEPTH-1:0]] <= wr_data;
        wr_ptr <= wr_ptr + 1;
    end
end

// Read operation
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        rd_ptr <= 0;
        rd_data <= 0;
    end else if (rd_en && !fifo_empty) begin
        rd_data <= fifo_mem[rd_ptr[DEPTH-1:0]];
        rd_ptr <= rd_ptr + 1;
    end
end

// Count management
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        count <= 0;
    end else begin
        case({wr_en, rd_en})
            2'b01: if (!fifo_empty) count <= count - 1; // Read only
            2'b10: if (!fifo_full) count <= count + 1;  // Write only
            2'b11: ;                                    // Read and write
            default: ;                                  // No operation
        endcase
    end
end

// Full and empty flags
always_comb begin
    fifo_full = (count == DEPTH);
    fifo_empty = (count == 0);
end

endmodule

---

### Coding Convention, structural, using macros

// Macro Definitions (this would come from an include file)
// D Flip-Flop Macro
`define DFF(D, Q, CLK, RST_N) \
    always_ff @(posedge CLK or negedge RST_N) \
        if (!RST_N) Q <= 0; \
        else Q <= D;

// 2-to-1 Multiplexer Macro
`define MUX2(A, B, SEL, Y) \
    assign Y = (SEL) ? B : A;

// 4-to-1 Multiplexer Macro
`define MUX4(A, B, C, D, SEL, Y) \
    assign Y = (SEL == 2'b00) ? A : \
               (SEL == 2'b01) ? B : \
               (SEL == 2'b10) ? C : D;

---
// Same Fifo as above using macro's
module simple_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 8
) (
    input wire clk,
    input wire rst_n,
    input wire wr_en,
    input wire rd_en,
    input wire [DATA_WIDTH-1:0] wr_data,
    output reg [DATA_WIDTH-1:0] rd_data,
    output wire fifo_full,
    output wire fifo_empty
);

    reg [DATA_WIDTH-1:0] fifo_mem [DEPTH-1:0];
    reg [$clog2(DEPTH):0] wr_ptr, rd_ptr;
    reg [$clog2(DEPTH)+1:0] count;

    wire [$clog2(DEPTH):0] wr_ptr_next, rd_ptr_next;
    wire [$clog2(DEPTH)+1:0] count_next;
    wire wr_enable, rd_enable;

    assign wr_enable = wr_en && !fifo_full;
    assign rd_enable = rd_en && !fifo_empty;
    assign fifo_full = (count == DEPTH);
    assign fifo_empty = (count == 0);

    // Write pointer logic
    `MUX2(wr_ptr, wr_ptr + 1, wr_enable, wr_ptr_next)
    `DFF(wr_ptr_next, wr_ptr, clk, rst_n)

    // Read pointer logic
    `MUX2(rd_ptr, rd_ptr + 1, rd_enable, rd_ptr_next)
    `DFF(rd_ptr_next, rd_ptr, clk, rst_n)

    // Count logic
    wire [$clog2(DEPTH)+1:0] count_plus_one = count + 1;
    wire [$clog2(DEPTH)+1:0] count_minus_one = count - 1;
    wire [1:0] count_select = {wr_enable, rd_enable};
    `MUX4(count, count_plus_one, count_minus_one, count, count_select, count_next)
    `DFF(count_next, count, clk, rst_n)

    // FIFO read and write operations
    always_ff @(posedge clk) begin
        if (wr_enable) fifo_mem[wr_ptr] <= wr_data;
    end

    assign rd_data_next = fifo_mem[rd_ptr];
    `DFF(rd_data_next, rd_data, clk, rst_n)

endmodule

---

I greatly prefer the second coding style. It is very structural and it is close to the gates one is synthesizing. Also, it is very easy to write a script for parse the code and find the number of flops and muxes in the code. For most cases, if we only count the flops and muxes, we will get very close to what the finial synthesis gate count will tell us. However, I recognize that not everyone is a fan. In some organizations, this coding style is strictly forbidden. So, in the spirit of appealing to the greater masses, I have stuck to the former coding style.

---
[Return to Index](index.md)
