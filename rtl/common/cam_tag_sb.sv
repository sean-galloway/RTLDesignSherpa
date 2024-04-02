`timescale 1ns / 1ps

module cam_tag_sb #(
    parameter int ENABLE = 1,
    parameter int N = 8,       // Width of the TAG
    parameter int DEPTH = 16   // Not used if we're checking the entire range
)(
    input  logic               i_clk,
    input  logic               i_rst_n,
    input  logic [N-1:0]       i_tag_in_status,
    input  logic               i_mark_valid,
    input  logic [N-1:0]       i_tag_in_valid,
    input  logic               i_mark_invalid,
    input  logic [N-1:0]       i_tag_in_invalid,
    output logic               ow_tags_empty,
    output logic               ow_tags_full,
    output logic               ow_tag_status
);

localparam int TotalDepth = 2**N; // Total entries in the scoreboard

logic [TotalDepth-1:0] r_tag_scoreboard;

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_tag_scoreboard <= 'b0;
    end else begin
        if (i_mark_valid) begin
            r_tag_scoreboard[i_tag_in_valid] <= 1'b1;
        end

        if (i_mark_invalid) begin
            r_tag_scoreboard[i_tag_in_invalid] <= 1'b0;
        end
    end
end

assign ow_tags_empty = ~|r_tag_scoreboard;
assign ow_tags_full  =  &r_tag_scoreboard;
assign ow_tag_status = r_tag_scoreboard[i_tag_in_status];

endmodule : cam_tag_sb
