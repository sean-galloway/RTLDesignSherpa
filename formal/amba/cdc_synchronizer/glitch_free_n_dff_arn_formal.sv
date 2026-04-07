// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible version of glitch_free_n_dff_arn.sv
// Changes: replaced packed 2D array with unpacked array (yosys limitation)

`include "reset_defs.svh"
module glitch_free_n_dff_arn #(
    parameter int FLOP_COUNT = 3,
    parameter int WIDTH = 4
) (
    input wire clk,
    rst_n,
    input wire [WIDTH-1:0] d,
    output reg [WIDTH-1:0] q
);

    localparam int FC = FLOP_COUNT;
    localparam int DW = WIDTH;

    ////////////////////////////////////////////////////////////////////////////
    // Unpacked array to hold the synchronizer stages (yosys-compatible)
    reg [WIDTH-1:0] r_q_array [0:FC-1];

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin : reset_block
            integer j;
            for (j = 0; j < FC; j = j + 1) begin
                r_q_array[j] <= {DW{1'b0}};
            end
        end else begin : shift_block
            integer j;
            // Load new data into stage 0
            r_q_array[0] <= d;
            // Shift the existing data
            for (j = 1; j < FC; j = j + 1) begin
                r_q_array[j] <= r_q_array[j-1];
            end
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Output assignment
    assign q = r_q_array[FC-1];

endmodule : glitch_free_n_dff_arn
