`timescale 1ns / 1ps

module counter_load_clear #(parameter MAX=32) (
    input                          i_clk, i_rst_n,
    input                          i_clear, i_increment, i_load,
    input        [$clog2(MAX)-1:0] i_loadval,                  // this loads the match value for ending the counter
    output logic [$clog2(MAX)-1:0] o_count,
    output logic                   ow_done
);

    logic [$clog2(MAX)-1:0] r_match_val;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!rst_n) begin
            o_count <= 'b0;
            r_match_val <= 'b0;
        end else begin
            if (i_clear)
                o_count <= 'b0;
            else if (i_load)
                r_match_val <= i_loadval;
            else if (i_increment)
                o_count <= (o_count == r_match_val) ? 'b0 : o_count + 'b1;
        end
    end

    assign ow_done = (o_count == r_match_val);

endmodule : counter_load_clear