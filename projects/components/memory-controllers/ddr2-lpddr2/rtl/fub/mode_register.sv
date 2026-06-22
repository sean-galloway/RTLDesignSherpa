// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: mode_register
// Purpose: Per-rank Mode Register shadow + live decode of MR-derived
//          timing values for use by the rest of the controller.
//
//          On `mr_we_i`, write `mr_data_i` into shadow MR[`mr_index_i`]
//          for `mr_rank_i`. The init_sequencer drives this during
//          DRAM bring-up; a CSR/APB hot-update path drives it later.
//
//          Live decoded outputs:
//            cl_o   : CAS read latency  (DDR2 MR0[6:4], LPDDR2 MR2[3:0])
//            cwl_o  : CAS write latency (DDR2 = CL-1, LPDDR2 MR2[7:4])
//            bl_o   : burst length      (4, 8, or 16 for LPDDR2)
//            al_o   : additive latency  (DDR2 MR1[5:3], LPDDR2: 0)
//            drv_o  : output drive strength (informational; not used)
//            odt_o  : ODT rule          (DDR2 MR1[6,2]; LPDDR2: 0)
//
// v2 status:
//   * MAX_MR_IDX=17 covers both DDR2 (MR0..MR3) and LPDDR2 (MR0..MR16).
//   * LPDDR2 BL decode clips BL16 → BL8 because bl_o is 4-bit. v3 widens
//     bl_o to [4:0] + updates the 3 downstream macros that consume it.
//
// v2 / v3 TODO:
//   * mr_req_o always tied 0 — no hot MR updates issued via the
//     scheduler. Lands when the APB CSR slave provides a write-during-
//     traffic path and the quiet-point handshake is implemented.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mode_register
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS  = 1,
    parameter int MAX_MR_IDX = 17,   // 0..16; LPDDR2 supports up to MR16
    parameter int RKW        = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  memtype_e             memtype_i,

    // ----- CSR / init-sequencer write port -----
    input  logic                 mr_we_i,
    input  logic [4:0]           mr_index_i,
    input  logic [15:0]          mr_data_i,
    input  logic [RKW-1:0]       mr_rank_i,

    // ----- request channel to scheduler (v1: unused) -----
    output logic                 mr_req_o,
    input  logic                 mr_grant_i,
    output logic [4:0]           mr_req_index_o,
    output logic [15:0]          mr_req_data_o,
    output logic [RKW-1:0]       mr_req_rank_o,

    // ----- live decoded values (driven from rank 0) -----
    output logic [3:0]           cl_o,
    output logic [3:0]           cwl_o,
    output logic [3:0]           bl_o,
    output logic [3:0]           al_o,
    output logic [1:0]           drv_strength_o,
    output logic [1:0]           odt_o
);

    //=========================================================================
    // Shadow MRs — one bank of MRs per rank.
    //=========================================================================
    logic [15:0] r_mr_shadow [NUM_RANKS][MAX_MR_IDX];

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            for (int unsigned k = 0; k < NUM_RANKS; k++) begin
                for (int unsigned i = 0; i < MAX_MR_IDX; i++) begin
                    r_mr_shadow[k][i] <= 16'h0000;
                end
            end
        end else begin
            if (mr_we_i && mr_index_i < 5'(MAX_MR_IDX)) begin
                r_mr_shadow[mr_rank_i][mr_index_i] <= mr_data_i;
            end
        end
    end)

    //=========================================================================
    // Live decode from rank 0 (multi-rank designs must use matching MR
    // values across ranks; mixed MR per rank is unusual and is a TODO).
    //=========================================================================
    logic [15:0] w_mr0;
    logic [15:0] w_mr1;
    logic [15:0] w_mr2;
    assign w_mr0 = r_mr_shadow[0][0];
    assign w_mr1 = r_mr_shadow[0][1];
    assign w_mr2 = r_mr_shadow[0][2];

    // Combinational next-cycle values for every decoded output.
    logic [3:0] w_cl;
    logic [3:0] w_cwl;
    logic [3:0] w_bl;
    logic [3:0] w_al;
    logic [1:0] w_drv;
    logic [1:0] w_odt;

    // BL — DDR2: MR0[2:0], LPDDR2: MR1[2:0].
    always_comb begin
        w_bl = 4'd4;
        if (memtype_i == MEMTYPE_DDR2) begin
            unique case (w_mr0[2:0])
                3'b010:  w_bl = 4'd4;
                3'b011:  w_bl = 4'd8;
                default: w_bl = 4'd4;
            endcase
        end else begin
            // LPDDR2: BL16 clips to BL8 (TODO widens port).
            unique case (w_mr1[2:0])
                3'b010:  w_bl = 4'd4;
                3'b011:  w_bl = 4'd8;
                3'b100:  w_bl = 4'd8;
                default: w_bl = 4'd4;
            endcase
        end
    end

    // CL — DDR2: MR0[6:4]; LPDDR2: MR2[3:0].
    assign w_cl = (memtype_i == MEMTYPE_DDR2)
                ? {1'b0, w_mr0[6:4]}
                : w_mr2[3:0];

    // CWL — DDR2: CL-1; LPDDR2: MR2[7:4] (fallback CL-1).
    always_comb begin
        if (memtype_i == MEMTYPE_DDR2) begin
            w_cwl = (w_cl == 4'd0) ? 4'd0 : (w_cl - 4'd1);
        end else begin
            w_cwl = (w_mr2[7:4] == 4'd0)
                  ? ((w_cl == 4'd0) ? 4'd0 : (w_cl - 4'd1))
                  : w_mr2[7:4];
        end
    end

    // AL — DDR2: MR1[5:3]; LPDDR2: 0.
    assign w_al = (memtype_i == MEMTYPE_DDR2) ? {1'b0, w_mr1[5:3]} : 4'd0;

    // Drive strength + ODT — informational.
    assign w_drv = (memtype_i == MEMTYPE_DDR2) ? {1'b0, w_mr1[1]} : 2'b00;
    assign w_odt = (memtype_i == MEMTYPE_DDR2) ? {w_mr1[6], w_mr1[2]} : 2'b00;

    //=========================================================================
    // Output registers — strict "every port is Q of a flop".
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            cl_o           <= 4'd0;
            cwl_o          <= 4'd0;
            bl_o           <= 4'd4;
            al_o           <= 4'd0;
            drv_strength_o <= 2'd0;
            odt_o          <= 2'd0;
        end else begin
            cl_o           <= w_cl;
            cwl_o          <= w_cwl;
            bl_o           <= w_bl;
            al_o           <= w_al;
            drv_strength_o <= w_drv;
            odt_o          <= w_odt;
        end
    end)

    //=========================================================================
    // mr_req channel — unused in v1, but still flopped for consistency.
    //=========================================================================
    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            mr_req_o       <= 1'b0;
            mr_req_index_o <= '0;
            mr_req_data_o  <= '0;
            mr_req_rank_o  <= '0;
        end else begin
            mr_req_o       <= 1'b0;
            mr_req_index_o <= '0;
            mr_req_data_o  <= '0;
            mr_req_rank_o  <= '0;
        end
    end)

    wire unused_v1 = |{ mr_grant_i, w_mr0[15:7], w_mr1[15:7],
                        w_mr2[15:8] };

endmodule : mode_register
