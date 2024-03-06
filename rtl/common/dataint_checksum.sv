`timescale 1ns / 1ps

// Generic Checksum Module
module dataint_checksum #(
    parameter int WIDTH = 8
) (
    input  logic             i_clk,
    i_rst_n,
    input  logic             i_reset,
    input  logic             i_valid,
    input  logic [WIDTH-1:0] i_data,
    output logic [WIDTH-1:0] o_chksum
);

    logic [WIDTH-1:0] r_count;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) r_count <= 'b0;
        else if (i_reset) r_count <= 'b0;
        else if (i_valid) r_count <= r_count + i_data;
    end

    assign o_chksum = r_count;

endmodule : dataint_checksum
