// SPDX-License-Identifier: MIT
// Formal stub for amba_clock_gate_ctrl
//
// Replaces the production amba_clock_gate_ctrl (which instantiates an ICG
// latch that formal solvers cannot model correctly) with a pass-through
// stub. The gated clock is identical to the input clock, while the
// "gating" status output is a free input so formal can exercise both
// gated and ungated behaviour via external drivers in the formal wrapper.
//
// This lets us verify the surrounding CG wrapper logic (valid aggregation,
// ready force-to-zero, reset, handshake stability of passthrough) without
// trying to formally model a latch-based ICG cell.

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

    // Pass-through clock for formal
    assign clk_out = clk_in;

    // Gating is driven by a free input at the top of the formal wrapper via a
    // hierarchical force from a sibling signal. Here we simply default to 0;
    // the enclosing formal_* wrapper drives it through an internal wire.
    //
    // We register wakeup for symmetry with the real module (so busy->clock
    // restoration analysis works on the combinational enable wires).
    logic r_wakeup;

    always_ff @(posedge clk_in or negedge aresetn) begin
        if (!aresetn) r_wakeup <= 1'b1;
        else          r_wakeup <= user_valid || axi_valid;
    end

    assign idle   = ~r_wakeup;

    // Let formal freely choose the gating output so both gated and ungated
    // behaviour of the surrounding wrapper is covered.
    (* anyseq *) logic free_gating;
    assign gating = free_gating;

endmodule : amba_clock_gate_ctrl
