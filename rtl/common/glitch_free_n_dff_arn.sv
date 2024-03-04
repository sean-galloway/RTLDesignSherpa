`timescale 1ns / 1ps

// A parameterized synchronizer
module glitch_free_n_dff_arn #(
    parameter int FLOP_COUNT = 3,
    parameter int WIDTH = 4,
    parameter int DEL = 1
) (
    input wire i_clk,
    i_rst_n,
    input wire [WIDTH-1:0] i_d,
    output reg [WIDTH-1:0] o_q
);

    localparam int FC = FLOP_COUNT;
    localparam int DW = WIDTH;

    ////////////////////////////////////////////////////////////////////////////
    // Packed array to hold the states
    logic [FC-1:0][WIDTH-1:0] r_q_array;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            // Reset all the flip-flops
            r_q_array <= {FC{{DW{1'b0}}}};
        end else begin
            // Load new data
            r_q_array[0] <= i_d;
            // Shift the existing data
            for (int i = 1; i < FC; i++) begin
                r_q_array[i] <= r_q_array[i-1];
            end
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Output assignment with DEL time unit delay
    assign #DEL o_q = r_q_array[FC-1];

    wire [(DW*FC)-1:0] flat_r_q;
    genvar i;
    generate
        for (i = 0; i < FC; i++) begin : gen_flatten_memory
            assign flat_r_q[i*DW+:DW] = r_q_array[i];
        end
    endgenerate

endmodule : glitch_free_n_dff_arn
