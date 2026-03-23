// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for gaxi_skid_buffer_dbldrn (yosys-compatible)
// NOTE: This module has complex registered flag timing. Properties are
// conservative — checking reset and structural invariants only.
// Full ghost-counter verification requires deeper analysis of the
// DUT's internal pipelining of wr_ready/rd_valid.

module formal_gaxi_skid_dbldrn #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 4
) (
    input  logic                    clk,
    input  logic                    rst_n,
    input  logic                    wr_valid,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    input  logic                    rd_ready,
    input  logic                    rd_ready2
);

    logic                    wr_ready;
    logic [3:0]              count;
    logic                    rd_valid;
    logic [3:0]              rd_count;
    logic [DATA_WIDTH-1:0]   rd_data;
    logic [DATA_WIDTH-1:0]   rd_data2;

    gaxi_skid_buffer_dbldrn #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (wr_valid),
        .wr_ready    (wr_ready),
        .wr_data     (wr_data),
        .count       (count),
        .rd_valid    (rd_valid),
        .rd_ready    (rd_ready),
        .rd_ready2   (rd_ready2),
        .rd_count    (rd_count),
        .rd_data     (rd_data),
        .rd_data2    (rd_data2)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // Reset clears state
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_ready: assert (!wr_ready);
            ap_reset_valid: assert (!rd_valid);
            ap_reset_count: assert (count == 4'd0);
        end
    end

    // count == rd_count always
    always @(posedge clk) begin
        if (rst_n)
            ap_count_eq: assert (count == rd_count);
    end

    // Cover
    always @(posedge clk) begin
        if (rst_n) begin
            cp_nonempty: cover (count > 0);
            cp_valid: cover (rd_valid);
            cp_ready: cover (wr_ready);
        end
    end

endmodule
