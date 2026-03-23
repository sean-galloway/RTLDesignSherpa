// SPDX-License-Identifier: MIT
`include "reset_defs.svh"
module formal_cam_tag #(parameter int N = 4, parameter int DEPTH = 4) (
    input logic clk, input logic rst_n,
    input logic [N-1:0] tag_in_status, input logic mark_valid, input logic [N-1:0] tag_in_valid,
    input logic mark_invalid, input logic [N-1:0] tag_in_invalid
);
    logic tags_empty, tags_full, tag_status;
    cam_tag #(.ENABLE(1), .N(N), .DEPTH(DEPTH)) dut (
        .clk(clk), .rst_n(rst_n),
        .tag_in_status(tag_in_status), .mark_valid(mark_valid), .tag_in_valid(tag_in_valid),
        .mark_invalid(mark_invalid), .tag_in_invalid(tag_in_invalid),
        .tags_empty(tags_empty), .tags_full(tags_full), .tag_status(tag_status)
    );
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);
    
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_empty: assert (tags_empty);
    end
    always @(posedge clk) begin
        if (rst_n) ap_mutex: assert (!(tags_empty && tags_full));
    end
    always @(posedge clk) begin
        if (rst_n) begin
            cp_notempty: cover (!tags_empty);
            cp_full: cover (tags_full);
        end
    end
endmodule
