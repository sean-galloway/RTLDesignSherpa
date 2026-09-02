// SPDX-License-Identifier: MIT
// Formal stub for amba_clock_gate_ctrl (pass-through clock + free gating)
`timescale 1ns / 1ps

module amba_clock_gate_ctrl #(
    parameter int CG_IDLE_COUNT_WIDTH = 4,
    parameter int ICW = CG_IDLE_COUNT_WIDTH
) (
    input  logic           clk_in,
    input  logic           aresetn,
    input  logic           cfg_cg_enable,
    input  logic [ICW-1:0] cfg_cg_idle_count,
    input  logic           user_valid,
    input  logic           axi_valid,
    output logic           clk_out,
    output logic           gating,
    output logic           idle
);
    assign clk_out = clk_in;
    logic r_wakeup;
    always_ff @(posedge clk_in or negedge aresetn) begin
        if (!aresetn) r_wakeup <= 1'b1;
        else          r_wakeup <= user_valid || axi_valid;
    end
    assign idle = ~r_wakeup;
    (* anyseq *) logic free_gating;
    assign gating = free_gating;
endmodule : amba_clock_gate_ctrl
