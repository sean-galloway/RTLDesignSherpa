`timescale 1ns / 1ps

module cam_tag_scoreboard #(
    parameter int ENABLE = 1,
    parameter int N = 8,       // Width of the TAG
    parameter int DEPTH = 16   // Not used if we're checking the entire range
)(
    input  logic               i_clk,
    input  logic               i_rst_n,
    input  logic               i_mark_valid,
    input  logic [N-1:0]       i_tag_in_valid,
    input  logic               i_mark_invalid,
    input  logic [N-1:0]       i_tag_in_invalid,
    output logic [N-1:0]       o_tag_remap
);

localparam int TotalDepth = 2**N; // Total entries in the scoreboard

function automatic [N-1:0] find_clr_index;
    input [TotalDepth-1:0] input_data;
    input [N-1:0] curr_ptr;
    logic found;
    begin
        find_clr_index = {N{1'b0}};  // Default value if no bit is set
        found = 1'b0;
        for (int i = 0; i < DEPTH && !found; i++) begin
            int index = (curr_ptr + i) % TotalDepth;
            if (~input_data[index]) begin
                find_clr_index = index;
                found = 1'b1;
            end
        end
end
endfunction

logic [TotalDepth-1:0] r_cam_tag_scoreboard;
logic [N-1:0] r_ptr;
logic w_hit;

assign w_hit = r_cam_tag_scoreboard[i_tag_in_valid];

always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_cam_tag_scoreboard <= 'b0;
        r_ptr <= 'b0;
    end else begin
        if (i_mark_valid) begin
            r_ptr <= find_clr_index(r_cam_tag_scoreboard, r_ptr);
        end

        if (i_mark_valid) begin
            if (w_hit)  // Collision handling
                r_cam_tag_scoreboard[r_ptr] <= 1'b1;
            else
                r_cam_tag_scoreboard[i_tag_in_valid] <= 1'b1;
        end

        if (i_mark_invalid) begin
            r_cam_tag_scoreboard[i_tag_in_invalid] <= 1'b0;
        end
    end
end

assign o_tag_remap = (w_hit) ? r_ptr : i_tag_in_valid;

endmodule : cam_tag_scoreboard
