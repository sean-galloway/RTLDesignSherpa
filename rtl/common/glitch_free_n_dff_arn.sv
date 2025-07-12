`timescale 1ns / 1ps

// A parameterized synchronizer
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
    // Packed array to hold the states
    logic [FC-1:0][WIDTH-1:0] r_q_array;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all the flip-flops
            r_q_array <= {FC{{DW{1'b0}}}};
        end else begin
            // Load new data
            r_q_array[0] <= d;
            // Shift the existing data
            for (int i = 1; i < FC; i++) begin
                r_q_array[i] <= r_q_array[i-1];
            end
        end
    end

    ////////////////////////////////////////////////////////////////////////////
    // Output assignment
    assign q = r_q_array[FC-1];

    wire [(DW*FC)-1:0] flat_r_q;
    genvar i;
    generate
        for (i = 0; i < FC; i++) begin : gen_flatten_memory
            assign flat_r_q[i*DW+:DW] = r_q_array[i];
        end
    endgenerate

endmodule : glitch_free_n_dff_arn
