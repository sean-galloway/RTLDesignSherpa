`timescale 1ns / 1ps

module counter_load_clear #(
    parameter int MAX = 32
) (
    input                          i_clk,
    i_rst_n,
    input                          i_clear,
    i_increment,
    i_load,
    input        [$clog2(MAX)-1:0] i_loadval,
    // this loads the match value for ending the counter
    output logic [$clog2(MAX)-1:0] o_count,
    output logic                   ow_done
);

    logic [$clog2(MAX)-1:0] r_match_val;
    logic [$clog2(MAX)-1:0] r_next_count;

    assign r_next_count = (i_clear == 1'b1) ? 'b0 : (o_count == r_match_val) ? 'b0 : o_count + 'b1;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            o_count <= 'b0;
            r_match_val <= 'b0;
        end else begin
            if (i_load) r_match_val <= i_loadval;
            o_count <= r_next_count;
        end
    end

    assign ow_done = (o_count == r_match_val);

endmodule : counter_load_clear
