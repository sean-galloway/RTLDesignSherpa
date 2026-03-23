// SPDX-License-Identifier: MIT
`include "reset_defs.svh"
module formal_gaxi_regslice #(parameter int DATA_WIDTH = 8) (
    input logic clk, input logic rst_n,
    input logic wr_valid, input logic [DATA_WIDTH-1:0] wr_data, input logic rd_ready
);
    logic wr_ready, rd_valid;
    logic [DATA_WIDTH-1:0] rd_data;
    logic [3:0] count;
    gaxi_regslice #(.DATA_WIDTH(DATA_WIDTH)) dut (
        .axi_aclk(clk), .axi_aresetn(rst_n),
        .wr_valid(wr_valid), .wr_ready(wr_ready), .wr_data(wr_data),
        .rd_valid(rd_valid), .rd_ready(rd_ready), .rd_data(rd_data), .count(count)
    );
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);
    always @(posedge clk) if (rst_n) begin
        assume (!(wr_valid && !wr_ready));
        assume (!(rd_ready && !rd_valid));
    end
    
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_count: assert (count == 0);
            ap_reset_valid: assert (!rd_valid);
        end
    end
    always @(posedge clk) begin
        if (rst_n) ap_count_01: assert (count <= 1);
    end
    always @(posedge clk) begin
        if (rst_n) begin
            cp_full: cover (count == 1);
            cp_empty: cover (count == 0 && f_past_valid > 3);
        end
    end
endmodule
