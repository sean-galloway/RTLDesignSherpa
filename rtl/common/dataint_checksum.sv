`timescale 1ns / 1ps

// Generic Checksum Module
module dataint_checksum #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    rst_n,
    input  logic             reset,
    input  logic             valid,
    input  logic [WIDTH-1:0] data,
    output logic [WIDTH-1:0] chksum
);

    logic [WIDTH-1:0] r_count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) r_count <= 'b0;
        else if (reset) r_count <= 'b0;
        else if (valid) r_count <= r_count + data;
    end

    assign chksum = r_count;

endmodule : dataint_checksum
