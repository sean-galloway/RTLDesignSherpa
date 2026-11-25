// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: formal_peregrine_mdu
// Purpose: peregrine_mdu against a reference function (PRD §5 targeted
//          formal, riscv-ip/peregrine-rv32im TASK-001 stage 5): when the
//          unit is done, its result is the M-extension result of the
//          operands it started with -- the RISC-V spec's values, including
//          divide by zero and the -2^31 / -1 overflow.  Every input is free
//          (start, cancel, consume, funct3, the operands); one task per
//          operation fixes funct3 so each runs as its own proof.
//          FMUL_DSP selects the build (0 iterative, 1 DSP multiply).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-25

`timescale 1ns / 1ps

module formal_peregrine_mdu (
    input  logic        clk,
    input  logic        start,
    input  logic        cancel,
    input  logic        consume,
    input  logic [2:0]  funct3,
    input  logic [31:0] a,
    input  logic [31:0] b
);

`ifdef FMUL_DSP
    localparam bit MUL_DSP = 1'b1;
`else
    localparam bit MUL_DSP = 1'b0;
`endif
`ifndef FOP
`define FOP 3'b000
`endif

    localparam logic [2:0] F_OP = `FOP;

    logic [1:0] r_rst_cnt = 2'd0;
    logic       rst_n;
    always_ff @(posedge clk) begin
        if (r_rst_cnt != 2'd2) r_rst_cnt <= r_rst_cnt + 2'd1;
    end
    assign rst_n = (r_rst_cnt == 2'd2);

    logic        idle, done;
    logic [31:0] result;

    peregrine_mdu #(
        .MUL_DSP (MUL_DSP)
    ) u_mdu (
        .clk     (clk),
        .rst_n   (rst_n),
        .start   (start),
        .cancel  (cancel),
        .consume (consume),
        .funct3  (funct3),
        .a       (a),
        .b       (b),
        .idle    (idle),
        .done    (done),
        .result  (result)
    );

    // The core's contract: funct3 and the operands are stable for the
    // instruction in EX, but the unit latches them at start, so the
    // harness lets them change freely afterwards.
    logic [31:0] r_a, r_b;
    logic        r_started;
    logic [5:0]  r_cyc;          // cycles since start (saturating)
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_started <= 1'b0;
        end else if (cancel) begin
            r_started <= 1'b0;
        end else if (start && idle) begin
            r_a       <= a;
            r_b       <= b;
            r_started <= 1'b1;
            r_cyc     <= 6'd0;
        end else if (done && consume) begin
            r_started <= 1'b0;
        end
        if (r_started && (r_cyc != 6'h3F)) r_cyc <= r_cyc + 6'd1;
    end

    // Reference: the M-extension results (RISC-V unprivileged spec, M).
    logic signed [63:0] p_ss, p_su;
    logic        [63:0] p_uu;
    logic        [31:0] w_ref;
    assign p_ss = $signed({{32{r_a[31]}}, r_a}) * $signed({{32{r_b[31]}}, r_b});
    assign p_su = $signed({{32{r_a[31]}}, r_a}) * $signed({32'd0, r_b});
    assign p_uu = {32'd0, r_a} * {32'd0, r_b};

    always_comb begin
        unique case (`FOP)
            3'b000:  w_ref = p_uu[31:0];
            3'b001:  w_ref = p_ss[63:32];
            3'b010:  w_ref = p_su[63:32];
            3'b011:  w_ref = p_uu[63:32];
            3'b100:  w_ref = (r_b == 32'd0) ? 32'hFFFF_FFFF :
                             ((r_a == 32'h8000_0000) && (r_b == 32'hFFFF_FFFF)) ? 32'h8000_0000 :
                             32'($signed(r_a) / $signed(r_b));
            3'b101:  w_ref = (r_b == 32'd0) ? 32'hFFFF_FFFF : (r_a / r_b);
            3'b110:  w_ref = (r_b == 32'd0) ? r_a :
                             ((r_a == 32'h8000_0000) && (r_b == 32'hFFFF_FFFF)) ? 32'd0 :
                             32'($signed(r_a) % $signed(r_b));
            default: w_ref = (r_b == 32'd0) ? r_a : (r_a % r_b);
        endcase
    end

    // Operand domain.  Full width (no FSMALL) is the real claim, but the
    // solver cannot prove a 32-step shift-add or shift-subtract against a
    // 32-bit `*`, `/` or `%` (TASK-001 stage 5: no result after the first
    // step a result is possible).  With FSMALL each operand's upper 24 bits
    // are one of 0x000000, 0xFFFFFF, 0x800000, 0x7FFFFF and its low byte is
    // free: small positive and negative values, values near +/-2^31 and
    // 2^32, and the divide corners (0, -1, -2^31, 2^31 - 1) -- 2^10 values
    // per operand.  Every step of the iteration, every sign case, the
    // high-word select, the negate-with-carry and both early-outs are
    // reached; the full-width arithmetic is simulation's (rv32um,
    // arch-test M, test_peregrine_mdu).  Owner, 2026-11-25: "Bounded
    // proof + sim" (PRD §5).  A full-width mul run sat on step 35 for
    // 59 min with no result.
`ifdef FSMALL
    function automatic logic f_small(input logic [31:0] x);
        f_small = (x[31:8] == 24'h000000) || (x[31:8] == 24'hFFFFFF) ||
                  (x[31:8] == 24'h800000) || (x[31:8] == 24'h7FFFFF);
    endfunction
    always_comb begin
        assume (f_small(a));
        assume (f_small(b));
    end
`endif

    always_comb begin
        assume (funct3 == `FOP);
        if (rst_n && done) begin
            ap_started:    assert (r_started);
            ap_result_ref: assert (result == w_ref);
        end
        if (rst_n) begin
            cp_done:      cover (done && r_started);
            // A result after the full iteration (not an early-out); the
            // MUL_DSP build's multiply is done after two cycles.
            cp_done_full: cover (done && r_started && (r_cyc >= ((MUL_DSP && !F_OP[2]) ? 6'd1 : 6'd32)));
        end
    end

endmodule : formal_peregrine_mdu
