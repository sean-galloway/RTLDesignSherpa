`timescale 1ns / 1ps

module ksalu(
    input         clk, rst_n,
    input [7:0]   a, b,
    input [3:0]   op,
    input         start,
    output        done,
    output [15:0] result
);

load_clear_counter 
#(
    .MAX  (MAX)
)
u_load_clear_counter(
    .clk       (clk),
    .rst_n     (rst_n),
    .clear     (clear),
    .increment (increment ),
    .load      (load),
    .loadval   (loadval),
    .count     (count),
    .done      (done)
);


endmodule