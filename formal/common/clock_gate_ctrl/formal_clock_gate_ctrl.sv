// SPDX-License-Identifier: MIT
`include "reset_defs.svh"
module formal_clock_gate_ctrl #(parameter int IDLE_CNTR_WIDTH = 4) (
    input logic clk, input logic rst_n,
    input logic cfg_cg_enable, input logic [IDLE_CNTR_WIDTH-1:0] cfg_cg_idle_count,
    input logic wakeup
);
    logic clk_out, gating;
    clock_gate_ctrl #(.IDLE_CNTR_WIDTH(IDLE_CNTR_WIDTH)) dut (
        .clk_in(clk), .aresetn(rst_n), .cfg_cg_enable(cfg_cg_enable),
        .cfg_cg_idle_count(cfg_cg_idle_count), .wakeup(wakeup),
        .clk_out(clk_out), .gating(gating)
    );
    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating: cover (gating);
            cp_not_gating: cover (!gating && cfg_cg_enable);
        end
    end
endmodule
