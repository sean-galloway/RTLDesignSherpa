`include "macro_inc.svh"
`timescale 1ns / 1ps

// Paramerized Synchronous FIFO
// TODO: Does this work for non-worwers of two????
module async_fifo #(
    parameter WIDTH = 64,
    parameter DEPTH = 16
)(
    input wire             wrclk,
    input wire             rdclk,
    input wire             rst_n,
    input [WIDTH-1:0]      data_in,       // wrclk
    input wire             write,         // wrclk
    input wire             read,          // rdclk
    output reg [WIDTH-1:0] data_out,      // rdclk
    output wire            fifo_free,     // wrclk
    output wire            fifo_avail     // rdclk
);

    // memory will contain the FIFO data.
    reg [WIDTH-1:0] memory [0:DEPTH-1];
    
    // $clog2(DEPTH+1)-2 to count from 0 to DEPTH
    reg [$clog2(DEPTH)-1:0] write_ptr_bin;
    reg [$clog2(DEPTH)-1:0] read_ptr_bin;
    reg [$clog2(DEPTH)-1:0] write_ptr_gray;
    reg [$clog2(DEPTH)-1:0] read_ptr_gray;

    // FIFO Conditions
    assign fifo_empty     = ( write_ptr == read_ptr ) ? 1'b1 : 1'b0;
    assign fifo_full      = ( write_ptr == (DEPTH-1) ) ? 1'b1 : 1'b0;
    assign fifo_not_empty = !fifo_empty;
    assign fifo_free      = !fifo_full;
    assign fifo_avail     = fifo_not_empty;

    // error checking events
    assign fifo_underflow = fifo_empty && read;
    assign fifo_overflow = fifo_full && write;

    // Read and write FIFO contents
    always @ (posedge clk) begin
        if ( write ) memory[write_ptr] <= data_in;
        if ( read )  data_out <= memory[read_ptr];
    end

    // Read and Write Pointer Flops
    assign write_ptr_next = (write & !fifo_full) ? write_ptr + 1 : write_ptr;
    `DFF_ARN(write_ptr, write_ptr_next, clk, rst_n)

    assign read_ptr_next = (read && fifo_not_empty) ? read_ptr + 1 : read_ptr;
    `DFF_ARN(read_ptr, read_ptr_next, clk, rst_n)

    // Error Conditions
    initial begin

        // FIFO underflow
        if ( fifo_underflow ) begin
            $error("** Illegal condition **, read when fifo_empty");
        end
        // FIFO Overflow
        if ( fifo_overflow ) begin
            $error("** Illegal condition **, write when fifo_full");
        end

    end // end initial
endmodule