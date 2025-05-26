`timescale 1ns / 1ps
/**
 * Counter with Load and Clear functionality
 *
 * Updated with proper naming conventions: w_ for combo, r_ for flopped
 */
module counter_load_clear #(
    parameter int MAX = 32'd32  // Fixed: Explicitly specify as 32-bit value
) (
    input logic i_clk,
    input logic i_rst_n,
    input logic i_clear,
    input logic i_increment,
    input logic i_load,
    input logic [$clog2(MAX)-1:0] i_loadval,
    // this loads the match value for ending the counter
    output logic [$clog2(MAX)-1:0] o_count,
    output logic ow_done
);
    // Match value register (flopped)
    logic [$clog2(MAX)-1:0] r_match_val;
    
    // Next count calculation (combinational)
    logic [$clog2(MAX)-1:0] w_next_count;

    assign w_next_count = (i_clear == 1'b1) ? 'b0 :
                            ((o_count == r_match_val) ? 'b0 : o_count + 'b1);

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            o_count <= 'b0;
            r_match_val <= 'b0;
        end else begin
            if (i_load) r_match_val <= i_loadval;
            // Only increment if i_increment is asserted
            if (i_increment) o_count <= w_next_count;
        end
    end

    assign ow_done = (o_count == r_match_val);

endmodule : counter_load_clear