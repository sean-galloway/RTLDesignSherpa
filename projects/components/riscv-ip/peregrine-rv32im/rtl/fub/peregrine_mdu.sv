// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_mdu
// Purpose: The peregrine M unit: one iterative multiply/divide resource,
//          started from EX (PRD §4.4, P3, P8).  The instruction that started
//          it holds in EX until done; the core stalls the front end behind
//          it (hold-in-EX, owner 2026-11-23), so the result writes back in
//          program order and RVFI stays exact.
//
//          Sequencing is three control registers (busy, done, a 5-bit
//          count), not a state-encoded FSM:
//          - start (unit idle, M instruction in EX): capture the operand
//            magnitudes, the result sign and the half/word select.  A
//            divide by zero, or the signed overflow -2^31 / -1, writes its
//            spec result here and goes straight to done (the early-out).
//          - busy: one radix-2 step per cycle, 32 steps.  Multiply is
//            shift-add over {hi, multiplier}; divide is restoring
//            shift-subtract over {remainder, quotient}.
//          - done: the result is valid (sign fixup on the registered
//            value) and held until the core consumes it as EX advances.
//          Iterative latency is therefore 33 stall cycles (start + 32), a
//          divide early-out 1, and a MUL_DSP multiply 2 (start, then one
//          registered product).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-23
//
// Parameters:
//   - MUL_DSP: 0 (default) multiplies iteratively, 32 steps; 1 computes the
//     product in one registered 32x32 multiply (a DSP on the FPGA), the
//     measured contrast of PRD P8.  Divide is iterative either way.
//
// Notes:
//   - The operation is the M-extension funct3: 000 mul, 001 mulh,
//     010 mulhsu, 011 mulhu, 100 div, 101 divu, 110 rem, 111 remu.
//   - The datapath works on magnitudes.  mul (the low word) is the same for
//     signed and unsigned operands, so it takes the unsigned path and never
//     negates.
//   - Negating a 64-bit product and keeping the high word is
//     ~hi + (lo == 0): the low word's +1 carries into the high word only
//     when the low word is zero.
//   - cancel (the M instruction in EX was killed by a MEM-stage trap or
//     mret) wins over everything and returns the unit to idle.
//   - Only busy, done and the count reset; the datapath is payload, read
//     only under done.
//
// Related Modules:
//   - peregrine_core (instantiates this in EX and owns the hold-in-EX stall)
//
// Test:
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_mdu.py
//   - rv32um battery and riscv-arch-test rv32i_m/M on peregrine_core

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_mdu #(
    parameter bit MUL_DSP = 1'b0
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        start,      // capture: unit idle and an M instruction in EX
    input  logic        cancel,     // the M instruction in EX was killed
    input  logic        consume,    // EX advanced: the done result was taken
    input  logic [2:0]  funct3,
    input  logic [31:0] a,          // rs1 (forwarded)
    input  logic [31:0] b,          // rs2 (forwarded)
    output logic        idle,
    output logic        done,
    output logic [31:0] result
);

    localparam logic [4:0]  LAST_STEP   = 5'd31;
    localparam logic [31:0] INT_MIN     = 32'h8000_0000;
    localparam logic [31:0] ALL_ONES    = 32'hFFFF_FFFF;

    // -----------------------------------------------------------------
    // Operation decode at start
    // -----------------------------------------------------------------
    logic        w_is_div;
    logic        w_signed_a;
    logic        w_signed_b;
    logic        w_sa;
    logic        w_sb;
    logic [31:0] w_abs_a;
    logic [31:0] w_abs_b;
    logic        w_sel_hi;
    logic        w_neg;
    logic        w_div0;
    logic        w_ovf;

    assign w_is_div   = funct3[2];
    // mulh and mulhsu take rs1 signed; div and rem take both signed.
    assign w_signed_a = w_is_div ? ~funct3[0] : (funct3[1:0] == 2'b01) | (funct3[1:0] == 2'b10);
    assign w_signed_b = w_is_div ? ~funct3[0] : (funct3[1:0] == 2'b01);
    assign w_sa       = w_signed_a & a[31];
    assign w_sb       = w_signed_b & b[31];
    assign w_abs_a    = w_sa ? (~a + 32'd1) : a;
    assign w_abs_b    = w_sb ? (~b + 32'd1) : b;
    // High word: mulh/mulhsu/mulhu, and the remainder for rem/remu.
    assign w_sel_hi   = w_is_div ? funct3[1] : (funct3[1:0] != 2'b00);
    // Result sign: the product's and quotient's is sa ^ sb; the
    // remainder's is the dividend's.
    assign w_neg      = (w_is_div & funct3[1]) ? w_sa : (w_sa ^ w_sb);
    assign w_div0     = w_is_div & (b == 32'd0);
    assign w_ovf      = w_is_div & ~funct3[0] & (a == INT_MIN) & (b == ALL_ONES);

    // -----------------------------------------------------------------
    // Control: busy, done, step count
    // -----------------------------------------------------------------
    logic        r_busy;
    logic        r_done;
    logic [4:0]  r_count;
    logic        w_start;
    logic        w_early;
    logic        w_dsp_mul;
    logic        w_last;

    assign w_start   = start & ~r_busy & ~r_done & ~cancel;
    assign w_early   = w_div0 | w_ovf;

    // Payload registers (no reset), declared ahead of the control logic
    // that reads them.
    logic        r_is_div;
    logic        r_sel_hi;
    logic        r_neg;
    logic [31:0] r_opnd;        // multiplicand or divisor magnitude
    logic [63:0] r_acc;         // mul {hi, multiplier}; div {remainder, quotient}

    assign w_dsp_mul = MUL_DSP & ~r_is_div;
    assign w_last    = w_dsp_mul | (r_count == LAST_STEP);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_busy  <= 1'b0;
            r_done  <= 1'b0;
            r_count <= 5'd0;
        end else if (cancel) begin
            r_busy  <= 1'b0;
            r_done  <= 1'b0;
            r_count <= 5'd0;
        end else if (w_start) begin
            r_busy  <= ~w_early;
            r_done  <= w_early;
            r_count <= 5'd0;
        end else if (r_busy) begin
            r_busy  <= ~w_last;
            r_done  <= w_last;
            r_count <= r_count + 5'd1;
        end else if (r_done & consume) begin
            r_done  <= 1'b0;
        end
    )

    // -----------------------------------------------------------------
    // Datapath: one radix-2 step per busy cycle
    // -----------------------------------------------------------------
    // Multiply step: add the multiplicand into the high word when the
    // multiplier's low bit is set, then shift the whole register right.
    logic [32:0] w_mul_sum;
    logic [63:0] w_mul_next;

    assign w_mul_sum  = {1'b0, r_acc[63:32]} + (r_acc[0] ? {1'b0, r_opnd} : 33'd0);
    assign w_mul_next = {w_mul_sum, r_acc[31:1]};

    // Divide step: shift the next dividend bit into the remainder and
    // subtract the divisor when it fits (restoring).
    logic [32:0] w_div_shift;
    // Bit 33 is the borrow; bit 32 is zero whenever the divisor fits (the
    // remainder stays below it), so only [31:0] and the borrow are read.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [33:0] w_div_diff;
    /* verilator lint_on UNUSEDSIGNAL */
    logic        w_div_fits;
    logic [63:0] w_div_next;

    assign w_div_shift = {r_acc[63:32], r_acc[31]};
    assign w_div_diff  = {1'b0, w_div_shift} - {2'b00, r_opnd};
    assign w_div_fits  = ~w_div_diff[33];
    assign w_div_next  = {(w_div_fits ? w_div_diff[31:0] : w_div_shift[31:0]),
                          r_acc[30:0], w_div_fits};

    // MUL_DSP: the whole product in one registered multiply.
    `ifdef XILINX
        (* use_dsp = "yes" *)
    `endif
    logic [63:0] w_dsp_product;

    assign w_dsp_product = 64'(r_opnd) * 64'(r_acc[31:0]);

    // The payload loads on every idle cycle, not only on start (TASK-001
    // stage 7): the start condition is late (it waits for mem_wait), and an
    // idle unit's payload is never read -- the result is taken only under
    // done.  The start cycle loads exactly what it did.
    always_ff @(posedge clk) begin
        if (~r_busy & ~r_done) begin
            r_is_div <= w_is_div;
            r_sel_hi <= w_sel_hi;
            r_neg    <= w_early ? 1'b0 : w_neg;
            r_opnd   <= w_is_div ? w_abs_b : w_abs_a;
            // Early-outs write the spec result directly: divide by zero
            // gives quotient all ones and remainder = the dividend;
            // overflow gives quotient -2^31 and remainder 0.
            r_acc    <= w_div0   ? {a, ALL_ONES}       :
                        w_ovf    ? {32'd0, INT_MIN}    :
                        w_is_div ? {32'd0, w_abs_a}    :
                                   {32'd0, w_abs_b};
        end else if (r_busy) begin
            r_acc    <= w_dsp_mul ? w_dsp_product :
                        r_is_div  ? w_div_next    : w_mul_next;
        end
    end

    // -----------------------------------------------------------------
    // Result: select the word, apply the sign
    // -----------------------------------------------------------------
    logic [31:0] w_word;
    logic        w_carry;

    assign w_word  = r_sel_hi ? r_acc[63:32] : r_acc[31:0];
    // Negating the 64-bit product: the high word gets the low word's carry.
    assign w_carry = (~r_is_div & r_sel_hi) ? (r_acc[31:0] == 32'd0) : 1'b1;
`ifdef RISCV_FORMAL_ALTOPS
    // riscv-formal's alternative M operations (formal/peregrine/riscv-formal,
    // TASK-001 stage 5): the solver cannot prove a 32-step shift-add or
    // shift-subtract against a 32-bit `*` or `/`, so under this define the
    // unit returns riscv-formal's stand-in function of the same operands
    // instead -- (rs1 +/- rs2) ^ a per-operation constant, the values in
    // vendor/riscv-formal/insns/insn_<op>.v.  The control (start, the step
    // count, the early-out, cancel, done, consume) is unchanged, so the
    // proofs still see the real hold-in-EX timing.  The real arithmetic is
    // verified in simulation (test_peregrine_mdu, rv32um, arch-test M).
    // Never defined in a simulation or synthesis build.
    logic [31:0] r_alt_a;
    logic [31:0] r_alt_b;
    logic [2:0]  r_alt_f3;
    logic [31:0] w_alt;

    always_ff @(posedge clk) begin
        if (~r_busy & ~r_done) begin
            r_alt_a  <= a;
            r_alt_b  <= b;
            r_alt_f3 <= funct3;
        end
    end

    always_comb begin
        unique case (r_alt_f3)
            3'b000:  w_alt = (r_alt_a + r_alt_b) ^ 32'h5876_063e;   // mul
            3'b001:  w_alt = (r_alt_a + r_alt_b) ^ 32'hf658_3fb7;   // mulh
            3'b010:  w_alt = (r_alt_a - r_alt_b) ^ 32'hecfb_e137;   // mulhsu
            3'b011:  w_alt = (r_alt_a + r_alt_b) ^ 32'h949c_e5e8;   // mulhu
            3'b100:  w_alt = (r_alt_a - r_alt_b) ^ 32'h7f85_29ec;   // div
            3'b101:  w_alt = (r_alt_a - r_alt_b) ^ 32'h10e8_fd70;   // divu
            3'b110:  w_alt = (r_alt_a - r_alt_b) ^ 32'h8da6_8fa5;   // rem
            default: w_alt = (r_alt_a - r_alt_b) ^ 32'h3138_d0e1;   // remu
        endcase
    end

    assign result  = w_alt;
`else
    assign result  = r_neg ? (~w_word + {31'd0, w_carry}) : w_word;
`endif

    assign idle = ~r_busy & ~r_done;
    assign done = r_done;

endmodule : peregrine_mdu
