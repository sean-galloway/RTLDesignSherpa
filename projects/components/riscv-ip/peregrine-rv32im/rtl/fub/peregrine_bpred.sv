// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_bpred
// Purpose: The peregrine branch predictor (PRD §4.2, P2, P5): a direct-mapped
//          BTB and a BHT of 2-bit saturating counters (COD Fig 4.65).
//          Looked up by the fetch PC in IF; written at EX resolution.
//
//          Prediction for the instruction at lookup_pc:
//          - BTB hit (entry valid, tag equal): the target is the entry's;
//            the direction is "taken" for an unconditional entry (JAL,
//            JALR) and the BHT counter's high bit for a conditional one.
//          - BTB miss: not taken (PC + 4).
//
//          Update, for one resolved instruction in EX:
//          - a conditional branch moves its BHT counter toward the outcome,
//            except when it installs: a taken conditional branch that did
//            not hit a conditional BTB entry writes the counter to weakly
//            not taken (2'b01) instead of stepping it from its old value.
//            2'b01 is what a zeroed counter reaches after one taken step,
//            i.e. the board's behaviour from power-up (LUTRAM INIT 0); it
//            keeps an alternating branch from mispredicting every outcome,
//            which weakly taken does (measured: loop_trip2 and interlock
//            fell below predict-not-taken with 2'b10);
//          - a taken branch, JAL or JALR writes its BTB entry (tag, target,
//            unconditional bit);
//          - an instruction that is not a branch but was predicted taken
//            (a stale BTB entry, e.g. after code was rewritten) clears its
//            BTB entry, so it mispredicts once, not on every pass.
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-24
//
// Parameters:
//   - BP_EN: 1 (default) predicts; 0 always predicts not taken (merlin's
//     behaviour, the PRD P5 A/B build) and instantiates no storage.
//   - BTB_ENTRIES: BTB size, a power of two >= 2 (PRD P5: 32).
//   - BHT_ENTRIES: BHT size, a power of two >= BTB_ENTRIES (PRD P5: 256).
//
// Notes:
//   - BHT index PC[log2(BHT)+1:2]; BTB index PC[log2(BTB)+1:2] and tag the
//     PC bits above it, so a BTB hit is an exact PC match.
//   - The BTB valid bits reset; the BTB payload and the BHT are memories
//     with no reset (LUTRAM).  A lookup reads the BHT only on a hit of a
//     conditional entry, and the update that installs a conditional entry
//     writes its counter to a fixed value, so every counter a lookup reads
//     descends from a defined write.  (The first build stepped the counter
//     from its old value on install: in a 4-state simulator that is X, on
//     the board whatever an earlier program left.  The unit test now
//     randomizes the initial memory contents and failed it on every func
//     seed tried.)
//   - The target is stored as PC[31:2]: IALIGN is 32, and a misaligned
//     target mispredicts against the resolved one and then traps in MEM.
//   - Lookup and update read the BHT through separate ports; an update in
//     the same cycle as a lookup of the same entry is seen by the next
//     lookup (the read is before the edge).
//
// Related Modules:
//   - peregrine_core (looks up in IF, updates and detects mispredicts in EX)
//
// Test:
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_bpred.py
//   - projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_predictor.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_bpred #(
    parameter bit BP_EN       = 1'b1,
    parameter int BTB_ENTRIES = 32,
    parameter int BHT_ENTRIES = 256
) (
    input  logic        clk,
    input  logic        rst_n,
    // Lookup (IF)
    input  logic [31:0] lookup_pc,
    output logic        pred_taken,
    output logic [31:0] pred_target,
    // Update (EX resolution)
    input  logic        upd_valid,      // one resolved instruction, this cycle
    input  logic [31:0] upd_pc,
    input  logic        upd_cond,       // conditional branch
    input  logic        upd_uncond,     // JAL or JALR
    input  logic        upd_taken,
    input  logic [31:0] upd_target,
    input  logic        upd_pred_taken  // what the lookup predicted for it
);

    generate
    if (BP_EN) begin : g_bp

        localparam int BTB_IW  = $clog2(BTB_ENTRIES);
        localparam int BHT_IW  = $clog2(BHT_ENTRIES);
        localparam int TAG_W   = 30 - BTB_IW;      // PC[31:BTB_IW+2]

        typedef struct packed {
            logic [TAG_W-1:0] tag;
            logic [29:0]      target;              // target PC[31:2]
            logic             uncond;
        } btb_entry_t;

        // -------------------------------------------------------------
        // Storage
        // -------------------------------------------------------------
        (* ram_style = "distributed" *)
        /* synthesis ramstyle = "MLAB" */
        btb_entry_t r_btb [BTB_ENTRIES];
        (* ram_style = "distributed" *)
        /* synthesis ramstyle = "MLAB" */
        logic [1:0] r_bht [BHT_ENTRIES];
        logic [BTB_ENTRIES-1:0] r_btb_valid;

        // -------------------------------------------------------------
        // Lookup
        // -------------------------------------------------------------
        logic [BTB_IW-1:0] w_lk_btb_idx;
        logic [BHT_IW-1:0] w_lk_bht_idx;
        btb_entry_t        w_lk_entry;
        logic              w_lk_hit;

        assign w_lk_btb_idx = lookup_pc[BTB_IW+1:2];
        assign w_lk_bht_idx = lookup_pc[BHT_IW+1:2];
        assign w_lk_entry   = r_btb[w_lk_btb_idx];
        assign w_lk_hit     = r_btb_valid[w_lk_btb_idx] &
                              (w_lk_entry.tag == lookup_pc[31:BTB_IW+2]);
        assign pred_taken   = w_lk_hit & (w_lk_entry.uncond | r_bht[w_lk_bht_idx][1]);
        assign pred_target  = {w_lk_entry.target, 2'b00};

        // -------------------------------------------------------------
        // Update
        // -------------------------------------------------------------
        logic [BTB_IW-1:0] w_up_btb_idx;
        logic [BHT_IW-1:0] w_up_bht_idx;
        logic [TAG_W-1:0]  w_up_old_tag;
        logic              w_up_old_uncond;
        logic              w_up_cond_hit;
        logic [1:0]        w_up_ctr;
        logic [1:0]        w_up_ctr_next;
        logic              w_up_bht_we;
        logic              w_up_btb_we;
        logic              w_up_btb_kill;
        btb_entry_t        w_up_entry;

        assign w_up_btb_idx  = upd_pc[BTB_IW+1:2];
        assign w_up_bht_idx  = upd_pc[BHT_IW+1:2];
        assign w_up_old_tag    = r_btb[w_up_btb_idx].tag;
        assign w_up_old_uncond = r_btb[w_up_btb_idx].uncond;
        assign w_up_cond_hit   = r_btb_valid[w_up_btb_idx] & ~w_up_old_uncond &
                                 (w_up_old_tag == upd_pc[31:BTB_IW+2]);
        assign w_up_ctr      = r_bht[w_up_bht_idx];
        // Saturating toward the outcome; an install writes weakly not taken.
        assign w_up_ctr_next = (upd_taken & ~w_up_cond_hit) ? 2'b01 :
                               upd_taken ? ((w_up_ctr == 2'b11) ? 2'b11 : w_up_ctr + 2'd1)
                                         : ((w_up_ctr == 2'b00) ? 2'b00 : w_up_ctr - 2'd1);
        assign w_up_bht_we   = upd_valid & upd_cond;
        assign w_up_btb_we   = upd_valid & upd_taken & (upd_cond | upd_uncond);
        assign w_up_btb_kill = upd_valid & ~upd_cond & ~upd_uncond & upd_pred_taken;

        assign w_up_entry.tag    = upd_pc[31:BTB_IW+2];
        assign w_up_entry.target = upd_target[31:2];
        assign w_up_entry.uncond = upd_uncond;

        // PCs are word addresses here: bits [1:0] carry no information.
        logic w_unused_lsbs;
        assign w_unused_lsbs = &{1'b0, lookup_pc[1:0], upd_pc[1:0], upd_target[1:0]};

        always_ff @(posedge clk) begin
            if (w_up_bht_we) r_bht[w_up_bht_idx] <= w_up_ctr_next;
            if (w_up_btb_we) r_btb[w_up_btb_idx] <= w_up_entry;
        end

        `ALWAYS_FF_RST(clk, rst_n,
            if (`RST_ASSERTED(rst_n)) begin
                r_btb_valid <= '0;
            end else if (w_up_btb_we) begin
                r_btb_valid[w_up_btb_idx] <= 1'b1;
            end else if (w_up_btb_kill) begin
                r_btb_valid[w_up_btb_idx] <= 1'b0;
            end
        )

    end else begin : g_no_bp

        assign pred_taken  = 1'b0;
        assign pred_target = 32'd0;

        // The update port is unused when there is no predictor.
        logic w_unused;
        assign w_unused = &{1'b0, clk, rst_n, lookup_pc, upd_valid, upd_pc, upd_cond,
                            upd_uncond, upd_taken, upd_target, upd_pred_taken};

    end
    endgenerate

endmodule : peregrine_bpred
