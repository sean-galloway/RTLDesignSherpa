`timescale 1ns / 1ps
/**
 * Counter with Load and Clear functionality
 */
module counter_load_clear #(
    parameter int MAX = 32'd32  // Fixed: Explicitly specify as 32-bit value
) (
    input logic                     clk,
    input logic                     rst_n,
    input logic                     clear,
    input logic                     increment,
    input logic                     load,
    input logic [$clog2(MAX)-1:0]   loadval,
    // this loads the match value for ending the counter
    output logic [$clog2(MAX)-1:0]  count,
    output logic                    done
);
    // Match value register (flopped)
    logic [$clog2(MAX)-1:0] r_match_val;

    // Next count calculation (combinational)
    logic [$clog2(MAX)-1:0] w_next_count;

    assign w_next_count = (clear == 1'b1) ? 'b0 :
                            ((count == r_match_val) ? 'b0 : count + 'b1);

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        count <= 'b0;
        r_match_val <= 'b0;
    end else begin
        if (load) r_match_val <= loadval;

        // Clear has highest priority
        if (clear) begin
            count <= 'b0;
        end else if (increment) begin
            count <= (count == r_match_val) ? 'b0 : count + 'b1;
        end
    end
end

    assign done = (count == r_match_val);

endmodule : counter_load_clear
