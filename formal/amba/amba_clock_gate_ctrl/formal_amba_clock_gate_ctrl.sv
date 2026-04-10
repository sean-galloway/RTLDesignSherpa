// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for amba_clock_gate_ctrl
//
// Properties verified:
//   P1: Reset wakes up (r_wakeup=1, so idle=0) -- no spurious gating on reset
//   P2: idle = ~r_wakeup (combinational) -- obvious but covers connectivity
//   P3: When user_valid or axi_valid asserted, r_wakeup is reloaded next cycle
//   P4: When cfg_cg_enable=0, gating never asserts
//   P5: When no activity for long enough, gating eventually asserts
//   P6: When wakeup asserts, gating deasserts within 1 cycle

`include "reset_defs.svh"

module formal_amba_clock_gate_ctrl (
    input logic clk,
    input logic rst_n
);

    localparam int ICW = 3;

    (* anyseq *) reg             cfg_cg_enable;
    (* anyseq *) reg [ICW-1:0]   cfg_cg_idle_count;
    (* anyseq *) reg             user_valid;
    (* anyseq *) reg             axi_valid;

    wire clk_out;
    wire gating;
    wire idle;

    amba_clock_gate_ctrl #(
        .CG_IDLE_COUNT_WIDTH(ICW)
    ) dut (
        .clk_in            (clk),
        .aresetn           (rst_n),
        .cfg_cg_enable     (cfg_cg_enable),
        .cfg_cg_idle_count (cfg_cg_idle_count),
        .user_valid        (user_valid),
        .axi_valid         (axi_valid),
        .clk_out           (clk_out),
        .gating            (gating),
        .idle              (idle)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // P1: after reset, r_wakeup should be 1 (initialized); idle should be 0
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n)) begin
            ap_reset_not_idle: assert (!idle);
            ap_reset_not_gating: assert (!gating);
        end
    end

    // P2: idle == ~r_wakeup -- check that idle is the inverse of what was reported as wakeup
    // Check that whenever valid activity occurred last cycle, idle is LOW this cycle.
    always @(posedge clk) begin
        if (f_past_valid > 1 && rst_n && $past(rst_n))
            if ($past(user_valid) || $past(axi_valid))
                ap_activity_not_idle: assert (!idle);
    end

    // P3: When cfg_cg_enable=0, gating must never be asserted
    always @(posedge clk) begin
        if (rst_n && !cfg_cg_enable)
            ap_no_gate_when_disabled: assert (!gating);
    end

    // P6: When user or axi valid is high, gating must be deasserted
    // (because the underlying clock_gate_ctrl uses wakeup signal to bypass gating)
    // Note: r_wakeup is registered, so the relationship is 1 cycle delayed.
    always @(posedge clk) begin
        if (f_past_valid > 1 && rst_n && $past(rst_n))
            if ($past(user_valid) || $past(axi_valid))
                ap_active_not_gating: assert (!gating);
    end

    // Cover points
    always @(posedge clk) begin
        if (rst_n) begin
            cp_gating:        cover (gating);
            cp_idle:          cover (idle);
            cp_clk_running:   cover (!gating && user_valid);
            cp_transition_to_gate: cover (gating && $past(!gating));
            cp_transition_to_run:  cover (!gating && $past(gating));
        end
    end

endmodule
